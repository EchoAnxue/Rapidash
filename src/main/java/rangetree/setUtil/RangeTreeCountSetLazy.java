package rangetree.setUtil;


import rangetree.Point;
import rangetree.lsm.PointTid;
import tidset.*;
import java.util.*;

public class RangeTreeCountSetLazy {

    private Node root;

    public RangeTreeCountSetLazy() {
        root = null;
    }

    public void insert(Point p, int tid) {
        if (root == null) {
            root = new Node(p, p.dimension() - 1, tid);
        } else {
            root.insert(p, tid);
        }
    }

    public TIdSet query(Point from, Point to) {
        if (root == null) {
            return Utils.createNewTIdSet();
        }
        return root.query(from, to);
    }
    public boolean isEmpty() {
        return root == null;
    }
    public static RangeTreeCountSetLazy bulkBuild(List<PointTid> tuples) {
        RangeTreeCountSetLazy tree = new RangeTreeCountSetLazy();
        if (tuples.isEmpty()) return tree;

        int dim = tuples.get(0).point.dimension() - 1;
        tree.root = buildNode(tuples, dim);
        return tree;
    }
    private static Node addNodes(List<PointTid> pts, int dim) {

        if (pts.isEmpty()) return null;

        pts.sort(Comparator.comparingInt(p -> p.point.get(dim)));

        int n = pts.size();
        int mid = n / 2;
        PointTid pivot = pts.get(mid);

        Node node = new Node();
        node.dimension = dim;
        node.value = pivot.point.get(dim);
        node.min = pts.get(0).point.get(dim);
        node.max = pts.get(n - 1).point.get(dim);

        List<PointTid> leftPts  = pts.subList(0, mid);
        List<PointTid> rightPts = pts.subList(mid + 1, n);

        if (dim == 0) {
            node.inner = null;
            node.base = Utils.createNewTIdSet();
            node.delta = new IntArray();
            for (PointTid pt : pts) {
                node.base.add(pt.tid);
            }
        } else {
            node.inner = buildNode(new ArrayList<>(pts), dim - 1);
            node.base = null;
            node.delta = null;
        }

        node.left = buildNode(new ArrayList<>(leftPts), dim);
        node.right = buildNode(new ArrayList<>(rightPts), dim);

        return node;
    }

    private static Node buildNode(List<PointTid> pts, int dim) {

        if (pts.isEmpty()) return null;

        pts.sort(Comparator.comparingInt(p -> p.point.get(dim)));

        int n = pts.size();
        int mid = n / 2;
        PointTid pivot = pts.get(mid);

        Node node = new Node();
        node.dimension = dim;
        node.value = pivot.point.get(dim);
        node.min = pts.get(0).point.get(dim);
        node.max = pts.get(n - 1).point.get(dim);

        List<PointTid> leftPts  = pts.subList(0, mid);
        List<PointTid> rightPts = pts.subList(mid + 1, n);

        if (dim == 0) {
            node.inner = null;
            node.base = Utils.createNewTIdSet();
            node.delta = new IntArray();
            for (PointTid pt : pts) {
                node.base.add(pt.tid);
            }
        } else {
            node.inner = buildNode(new ArrayList<>(pts), dim - 1);
            node.base = null;
            node.delta = null;
        }

        node.left = buildNode(new ArrayList<>(leftPts), dim);
        node.right = buildNode(new ArrayList<>(rightPts), dim);

        return node;
    }

    // ===================== Node =====================

    private static class Node {

        private int dimension;
        private int value;

        private int min;
        private int max;

        private Node left;
        private Node right;
        private Node inner;

        // ---- Lazy TidSet ----
        private TIdSet base;          // materialized bitmap
        private IntArray delta;       // newly inserted tids

        private static final int DELTA_THRESHOLD = 128;

        public Node(){

        }
        // ---------- constructor ----------
        public Node(Point p, int dimension, int tid) {
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
                this.inner = new Node(p, dimension - 1, tid);
                this.base = null;   // 非最后一维不维护 TidSet
                this.delta = null;
            }
        }

        // ---------- deep copy constructor ----------
        public Node(Node node) {
            this.dimension = node.dimension;
            this.value = node.value;
            this.min = node.min;
            this.max = node.max;

            this.left = (node.left == null) ? null : new Node(node.left);
            this.right = (node.right == null) ? null : new Node(node.right);

            if (node.inner == null) {
                this.inner = null;
                this.base = node.base.clone();
                this.delta = node.delta.clone();
            } else {
                this.inner = new Node(node.inner);
                this.base = null;
                this.delta = null;
            }
        }

        // ================= insert =================

        public void insert(Point p, int tid) {

            // ---- 1. 结构插入（与原实现一致） ----
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
                    left = new Node(this);
                    right = new Node(p, dimension, tid);
                    value = p.get(dimension);
                    max = value;
                } else if (p.get(dimension) < value) {
                    right = new Node(this);
                    left = new Node(p, dimension, tid);
                    min = p.get(dimension);
                }
            }

            // ---- 2. Lazy TidSet 更新 ----
            if (inner != null) {
                inner.insert(p, tid);
            } else {
                // dimension == 0
                delta.add(tid);
                maybeFlush();
            }
        }

        // ================= query =================

        public TIdSet query(Point from, Point to) {

            if (to.get(dimension) < min || from.get(dimension) > max) {
                return Utils.createNewTIdSet();
            }

            if (to.get(dimension) == min && !to.getInclusive(dimension)) {
                return Utils.createNewTIdSet();
            }

            if (from.get(dimension) == max && !from.getInclusive(dimension)) {
                return Utils.createNewTIdSet();
            }

            boolean fullyCovered =
                    (from.get(dimension) < min ||
                            (from.get(dimension) == min && from.getInclusive(dimension)))
                            && (to.get(dimension) > max ||
                            (to.get(dimension) == max && to.getInclusive(dimension)));

            if (fullyCovered) {
                if (inner == null) {
                    return materialize();
                }
                return inner.query(from, to);
            }
            TIdSet leftSet = Utils.createNewTIdSet();
            if (left != null) {
                 leftSet = left.query(from, to);
            }
            TIdSet rightSet = Utils.createNewTIdSet();
            if (right != null) {
                rightSet = right.query(from, to);
            }

            return leftSet.union(rightSet);
        }

        // ================= Lazy helpers =================

        private TIdSet materialize() {
            if (delta.isEmpty()) {
                return base;
            }
            TIdSet result = base.clone();
            for (int tid : delta) {
                result.add(tid);
            }
            return result;
        }

        private void maybeFlush() {
            if (delta.size() >= DELTA_THRESHOLD) {
                base = materialize();
                delta.clear();
            }
        }
    }
}
