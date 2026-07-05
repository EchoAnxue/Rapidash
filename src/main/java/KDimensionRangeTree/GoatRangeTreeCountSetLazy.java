package KDimensionRangeTree;

import rangetree.Point;
import rangetree.setUtil.IntArray;
import rangetree.setUtil.Utils;
import tidset.*;
import java.util.*;

/**
 * RangeTreeCountSetLazy
 *
 * 改动目标：
 * 1. 只保证第一维（outer-most dimension）是平衡的；
 * 2. 不改变“min-max 区间 fully cover 时，可直接从 inner node 的最后一维 tidset 得到结果”的查询逻辑；
 * 3. 保证 insert / query 正确；
 * 4. 其余维度仍沿用原先的递归 RangeTree + lazy tidset 方案。
 *
 * 方案说明：
 * - 第一维采用 scapegoat-style 的“失衡后局部重构”。
 * - 为了保证重构后 inner 仍然准确表示“该节点整个子树的低维索引”，
 *   第一维节点在重构时会基于其子树全部 PointTid 重新建立：
 *      1) 第一维的平衡 BST 结构
 *      2) 每个节点对应的 inner（维度-1）子树
 * - 这样不会破坏 full-cover -> inner.query(...) 的语义。
 */
public class GoatRangeTreeCountSetLazy {

    public static class Stats {
        public long splitCount = 0;
        public long cloneNodeCount = 0;
        public long flushCount = 0;
        public long materializeCount = 0;
        public long rebuildCount = 0;

        public void reset() {
            splitCount = 0;
            cloneNodeCount = 0;
            flushCount = 0;
            materializeCount = 0;
            rebuildCount = 0;
        }

        @Override
        public String toString() {
            return String.format(
                    "splits=%d, clones=%d, flushes=%d, materializes=%d, rebuilds=%d",
                    splitCount, cloneNodeCount, flushCount, materializeCount, rebuildCount
            );
        }
    }

    public static final Stats STATS = new Stats();

    private FirstDimNode root;
    private int topDimension = -1;

    // scapegoat alpha，通常取 (0.5, 1) 之间
    private static final double ALPHA = 0.75;

    public GoatRangeTreeCountSetLazy() {
        this.root = null;
    }

    public boolean isEmpty() {
        return root == null;
    }

    public void insert(Point p, int tid) {
        if (p == null) {
            throw new IllegalArgumentException("point must not be null");
        }
        if (root == null) {
            topDimension = p.dimension() - 1;
            root = new FirstDimNode(topDimension, new PointTid(p, tid));
            return;
        }
        if (p.dimension() - 1 != topDimension) {
            throw new IllegalArgumentException("all points must have the same dimension");
        }
        root = insertAndRebalance(root, new PointTid(p, tid));
    }

    public TIdSet query(Point from, Point to) {
        TIdSet out = Utils.createNewTIdSet();
        queryInto(from, to, out);
        return out;
    }

    public void queryInto(Point from, Point to, TIdSet acc) {
        if (root == null) {
            return;
        }
        root.queryInto(from, to, acc);
    }

    // ============================================================
    // =============== 第一维：平衡层（Scapegoat） ==================
    // ============================================================

    private FirstDimNode insertAndRebalance(FirstDimNode node, PointTid pt) {
        Deque<FirstDimNode> path = new ArrayDeque<>();
        root = bstInsert(root, pt, path);

        // 自底向上更新 size / min / max / inner
        List<FirstDimNode> nodes = new ArrayList<>(path);
        for (int i = nodes.size() - 1; i >= 0; i--) {
            nodes.get(i).pullUp();
        }

        // 找 scapegoat：第一个失衡祖先
        FirstDimNode scapegoat = null;
        FirstDimNode parentOfScapegoat = null;

        FirstDimNode prev = null;
        for (int i = nodes.size() - 1; i >= 0; i--) {
            FirstDimNode cur = nodes.get(i);
            if (!cur.isBalanced()) {
                scapegoat = cur;
                parentOfScapegoat = prev;
                break;
            }
            prev = cur;
        }

        if (scapegoat != null) {
            FirstDimNode rebuilt = rebuildSubtree(scapegoat);
            STATS.rebuildCount++;
            if (parentOfScapegoat == null) {
                root = rebuilt;
            } else if (parentOfScapegoat.left == scapegoat) {
                parentOfScapegoat.left = rebuilt;
            } else {
                parentOfScapegoat.right = rebuilt;
            }

            // rebuild 挂回去之后，再向上修正一遍祖先聚合值
            // nodes 中顺序是 root -> inserted leaf
            for (int i = nodes.size() - 1; i >= 0; i--) {
                FirstDimNode cur = nodes.get(i);
                if (cur == scapegoat) {
                    break;
                }
                cur.pullUp();
            }
            if (parentOfScapegoat != null) {
                parentOfScapegoat.pullUp();
            }
        }

        return root;
    }

    private FirstDimNode bstInsert(FirstDimNode node, PointTid pt, Deque<FirstDimNode> path) {
        if (node == null) {
            FirstDimNode created = new FirstDimNode(topDimension, pt);
            path.addLast(created);
            return created;
        }

        path.addLast(node);
        int key = pt.point.get(topDimension);
        if (key < node.key) {
            node.left = bstInsert(node.left, pt, path);
        } else if (key > node.key) {
            node.right = bstInsert(node.right, pt, path);
        } else {
            node.bucket.add(pt);
            node.pullUp();
        }
        return node;
    }

    private FirstDimNode rebuildSubtree(FirstDimNode node) {
        List<PointTid> points = new ArrayList<>(node.size);
        collectPoints(node, points);
        points.sort(Comparator.comparingInt(a -> a.point.get(topDimension)));

        List<Bucket> buckets = groupByFirstDim(points);
        return buildBalancedFirstDim(buckets, 0, buckets.size() - 1);
    }

    private void collectPoints(FirstDimNode node, List<PointTid> out) {
        if (node == null) {
            return;
        }
        collectPoints(node.left, out);
        out.addAll(node.bucket);
        collectPoints(node.right, out);
    }

    private List<Bucket> groupByFirstDim(List<PointTid> sorted) {
        List<Bucket> buckets = new ArrayList<>();
        int i = 0;
        while (i < sorted.size()) {
            PointTid first = sorted.get(i);
            int key = first.point.get(topDimension);
            Bucket b = new Bucket(key);
            while (i < sorted.size() && sorted.get(i).point.get(topDimension) == key) {
                b.points.add(sorted.get(i));
                i++;
            }
            buckets.add(b);
        }
        return buckets;
    }

    private FirstDimNode buildBalancedFirstDim(List<Bucket> buckets, int l, int r) {
        if (l > r) {
            return null;
        }
        int m = (l + r) >>> 1;
        Bucket b = buckets.get(m);
        FirstDimNode node = new FirstDimNode(topDimension, b.points.get(0));
        node.bucket.clear();
        node.bucket.addAll(b.points);
        node.left = buildBalancedFirstDim(buckets, l, m - 1);
        node.right = buildBalancedFirstDim(buckets, m + 1, r);
        node.pullUp();
        return node;
    }

    private static final class Bucket {
        final int key;
        final List<PointTid> points = new ArrayList<>();

        Bucket(int key) {
            this.key = key;
        }
    }

    private final class FirstDimNode {
        final int dimension;
        int key;
        int min;
        int max;
        int size;

        FirstDimNode left;
        FirstDimNode right;

        // 所有第一维等于 key 的点
        final List<PointTid> bucket = new ArrayList<>();

        // 该节点整个子树在低一维上的索引
        DimNode inner;

        FirstDimNode(int dimension, PointTid pt) {
            this.dimension = dimension;
            this.key = pt.point.get(dimension);
            this.min = key;
            this.max = key;
            this.size = 1;
            this.bucket.add(pt);
            rebuildInner();
        }

        boolean isBalanced() {
            int leftSize = (left == null) ? 0 : left.size;
            int rightSize = (right == null) ? 0 : right.size;
            return leftSize <= ALPHA * size && rightSize <= ALPHA * size;
        }

        void pullUp() {
            this.size = bucket.size() + ((left == null) ? 0 : left.size) + ((right == null) ? 0 : right.size);
            this.min = (left != null) ? left.min : key;
            this.max = (right != null) ? right.max : key;
            rebuildInner();
        }

        void rebuildInner() {
            List<PointTid> all = new ArrayList<>(size);
            collectSubtreePoints(this, all);
            this.inner = buildLowerDimFromPoints(all, dimension - 1);
        }

        void queryInto(Point from, Point to, TIdSet acc) {
            if (to.get(dimension) < min || from.get(dimension) > max) {
                return;
            }
            if (to.get(dimension) == min && !to.getInclusive(dimension)) {
                return;
            }
            if (from.get(dimension) == max && !from.getInclusive(dimension)) {
                return;
            }

            boolean fullyCovered =
                    (from.get(dimension) < min ||
                            (from.get(dimension) == min && from.getInclusive(dimension)))
                            &&
                            (to.get(dimension) > max ||
                                    (to.get(dimension) == max && to.getInclusive(dimension)));

            if (fullyCovered) {
                if (inner != null) {
                    inner.queryInto(from, to, acc);
                }
                return;
            }

            if (left != null) {
                left.queryInto(from, to, acc);
            }

            if (containsKey(from, to, key, dimension)) {
                for (PointTid pt : bucket) {
                    if (pointInside(pt.point, from, to)) {
                        acc.add(pt.tid);
                    }
                }
            }

            if (right != null) {
                right.queryInto(from, to, acc);
            }
        }
    }

    private void collectSubtreePoints(FirstDimNode node, List<PointTid> out) {
        if (node == null) {
            return;
        }
        collectSubtreePoints(node.left, out);
        out.addAll(node.bucket);
        collectSubtreePoints(node.right, out);
    }

    // ============================================================
    // =============== 低维：沿用原来的递归结构 ======================
    // ============================================================

    private DimNode buildLowerDimFromPoints(List<PointTid> points, int dimension) {
        if (points == null || points.isEmpty()) {
            return null;
        }
        DimNode root = null;
        for (PointTid pt : points) {
            if (root == null) {
                root = new DimNode(pt.point, dimension, pt.tid);
            } else {
                root.insert(pt.point, pt.tid);
            }
        }
        return root;
    }

    private static class DimNode {
        private int dimension;
        private int value;

        private int min;
        private int max;

        private DimNode left;
        private DimNode right;
        private DimNode inner;

        // ---- Lazy TidSet ----
        private TIdSet base;
        private IntArray delta;

        private static final int DELTA_THRESHOLD = 1024;

        public DimNode(Point p, int dimension, int tid) {
            this.dimension = dimension;
            this.value = p.get(dimension);
            this.min = value;
            this.max = value;
            this.left = null;
            this.right = null;

            if (dimension == 0) {
                this.inner = null;
                this.base = Utils.createNewTIdSet();
                this.delta = new IntArray();
                this.delta.add(tid);
            } else {
                this.inner = new DimNode(p, dimension - 1, tid);
                this.base = null;
                this.delta = null;
            }
        }

        public DimNode(DimNode node) {
            this.dimension = node.dimension;
            this.value = node.value;
            this.min = node.min;
            this.max = node.max;

            this.left = (node.left == null) ? null : new DimNode(node.left);
            this.right = (node.right == null) ? null : new DimNode(node.right);

            if (node.inner == null) {
                this.inner = null;
                this.base = node.base;
                this.delta = node.delta.clone();
            } else {
                this.inner = new DimNode(node.inner);
                this.base = null;
                this.delta = null;
            }
        }

        public void insert(Point p, int tid) {
            if (left != null) {
                if (p.get(dimension) < value) {
                    left.insert(p, tid);
                    min = left.min;
                } else {
                    right.insert(p, tid);
                    max = right.max;
                }
            } else {
                if (p.get(dimension) > value) {
                    left = new DimNode(this);
                    STATS.cloneNodeCount++;
                    right = new DimNode(p, dimension, tid);
                    value = p.get(dimension);
                    max = value;
                    STATS.splitCount++;
                } else if (p.get(dimension) < value) {
                    right = new DimNode(this);
                    STATS.cloneNodeCount++;
                    left = new DimNode(p, dimension, tid);
                    min = p.get(dimension);
                    STATS.splitCount++;
                }
            }

            if (inner != null) {
                inner.insert(p, tid);
            } else {
                delta.add(tid);
                maybeFlush();
            }
        }

        private void queryInto(Point from, Point to, TIdSet acc) {
            if (to.get(dimension) < min || from.get(dimension) > max) {
                return;
            }
            if (to.get(dimension) == min && !to.getInclusive(dimension)) {
                return;
            }
            if (from.get(dimension) == max && !from.getInclusive(dimension)) {
                return;
            }

            boolean fullyCovered =
                    (from.get(dimension) < min ||
                            (from.get(dimension) == min && from.getInclusive(dimension)))
                            &&
                            (to.get(dimension) > max ||
                                    (to.get(dimension) == max && to.getInclusive(dimension)));

            if (fullyCovered) {
                if (inner == null) {
                    base = materialize();
                    delta.clear();
                    acc.union(base);
                } else {
                    inner.queryInto(from, to, acc);
                }
                return;
            }

            if (left != null) {
                left.queryInto(from, to, acc);
            }
            if (right != null) {
                right.queryInto(from, to, acc);
            }
        }

        private TIdSet materialize() {
            if (delta.isEmpty()) {
                return base;
            }
            STATS.materializeCount++;
            TIdSet newBase = base.clone();
            newBase.add(delta.getData(), delta.getSize());
            this.base = newBase;
            return newBase;
        }

        private void maybeFlush() {
            if (delta.size() >= DELTA_THRESHOLD) {
                STATS.flushCount++;
                base = materialize();
                delta.clear();
            }
        }
    }

    // ============================================================
    // ======================= helpers ============================
    // ============================================================

    private boolean pointInside(Point p, Point from, Point to) {
        for (int d = 0; d < p.dimension(); d++) {
            int v = p.get(d);
            int lo = from.get(d);
            int hi = to.get(d);

            if (v < lo || v > hi) {
                return false;
            }
            if (v == lo && !from.getInclusive(d)) {
                return false;
            }
            if (v == hi && !to.getInclusive(d)) {
                return false;
            }
        }
        return true;
    }

    private boolean containsKey(Point from, Point to, int key, int dimension) {
        if (key < from.get(dimension) || key > to.get(dimension)) {
            return false;
        }
        if (key == from.get(dimension) && !from.getInclusive(dimension)) {
            return false;
        }
        if (key == to.get(dimension) && !to.getInclusive(dimension)) {
            return false;
        }
        return true;
    }

    // 避免依赖外部 rangetree.lsm.PointTid
    private static final class PointTid {
        final Point point;
        final int tid;

        PointTid(Point point, int tid) {
            this.point = point;
            this.tid = tid;
        }
    }
}
