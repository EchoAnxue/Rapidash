package rangetree.lsm;

import rangetree.Point;

import java.util.*;

public class L0KDTree {

    // ================= Node =================

    private static class KDNode {
        PointTid pt;
        int axis;
        KDNode left;
        KDNode right;

        KDNode(PointTid pt, int axis) {
            this.pt = pt;
            this.axis = axis;
        }
    }

    // ================= Tree =================

    private KDNode root;
    private final int dim;
    private final int MAX_SIZE;
    private int size = 0;

    public L0KDTree(int dim, int maxSize) {
        this.dim = dim;
        this.MAX_SIZE = maxSize;
    }

    public int size() {
        return size;
    }

    public boolean isFull() {
        return size >= MAX_SIZE;
    }

    public void clear() {
        root = null;
        size = 0;
    }

    // ================= insert =================

    public void insert(PointTid pt) {
        root = insert(root, pt, 0);
        size++;
    }

    private KDNode insert(KDNode node, PointTid pt, int depth) {
        if (node == null) {
            return new KDNode(pt, depth % dim);
        }

        int axis = node.axis;
        int vNew = pt.point.get(axis);
        int vCur = node.pt.point.get(axis);

        /*
         * 关键设计：
         * - 如果在当前 axis 上相等，也必须继续往下走
         * - 否则完全相等的点会无限卡在同一位置
         */
        if (vNew < vCur) {
            node.left = insert(node.left, pt, depth + 1);
        } else {
            // vNew >= vCur，包括完全相等的情况
            node.right = insert(node.right, pt, depth + 1);
        }

        return node;
    }

    // ================= range query =================

    public List<Integer> rangeQuery(Point low, Point up) {
        List<Integer> res = new ArrayList<>();
        rangeQuery(root, low, up, res);
        return res;
    }

    private void rangeQuery(KDNode node, Point low, Point up, List<Integer> out) {
        if (node == null) return;

        // 1️⃣ 检查当前点（全维）
        if (inRange(node.pt.point, low, up)) {
            out.add(node.pt.tid);
        }

        // 2️⃣ 不做任何剪枝，左右都访问
        rangeQuery(node.left, low, up, out);
        rangeQuery(node.right, low, up, out);
    }

    // ================= utils =================

    private boolean inRange(Point p, Point low, Point up) {
        int d = p.dimension();
        for (int i = 0; i < d; i++) {
            int v = p.get(i);

            if (v < low.get(i)) return false;
            if (v > up.get(i)) return false;
        }
        return true;
    }
}
