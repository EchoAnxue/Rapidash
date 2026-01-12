package rangetree.lsm;

import rangetree.Point;

import java.util.*;

public class SelectiveDimensionL0Index {

    private Node root;
    private final int[] dims;   // 被索引的维度
    private int size = 0;

    private static final int LEAF_SIZE = 32;

    public SelectiveDimensionL0Index(int[] dims) {
        this.dims = dims;
    }

    public int size() {
        return size;
    }

    // ================= insert =================

    public void insert(PointTid pt) {
        root = insert(root, pt, 0);
        size++;
    }

    private Node insert(Node node, PointTid pt, int depth) {
        if (node == null) {
            return new Node(pt);
        }

        if (node.isLeaf()) {
            node.points.add(pt);
            if (node.points.size() > LEAF_SIZE) {
                return node.split(depth, dims);
            }
            return node;
        }

        int axis = dims[depth % dims.length];
        int v = pt.point.get(axis);

        if (v < node.splitValue) {
            node.left = insert(node.left, pt, depth + 1);
        } else {
            node.right = insert(node.right, pt, depth + 1);
        }
        return node;
    }

    // ================= query =================

    public List<Integer> rangeQuery(Point from, Point to) {
        List<Integer> result = new ArrayList<>();
        rangeQuery(root, from, to, 0, result);
        return result;
    }

    private void rangeQuery(
            Node node,
            Point from,
            Point to,
            int depth,
            List<Integer> out) {

        if (node == null) return;

        if (node.isLeaf()) {
            for (PointTid pt : node.points) {
                if (inRange(pt.point, from, to)) {
                    out.add(pt.tid);
                }
            }
            return;
        }

        int axis = dims[depth % dims.length];

        if (from.get(axis) <= node.splitValue) {
            rangeQuery(node.left, from, to, depth + 1, out);
        }
        if (to.get(axis) >= node.splitValue) {
            rangeQuery(node.right, from, to, depth + 1, out);
        }
    }

    // ================= dump =================

    public List<PointTid> dumpAll() {
        List<PointTid> all = new ArrayList<>();
        dump(root, all);
        return all;
    }

    private void dump(Node node, List<PointTid> out) {
        if (node == null) return;
        if (node.isLeaf()) {
            out.addAll(node.points);
        } else {
            dump(node.left, out);
            dump(node.right, out);
        }
    }

    // ================= utils =================

    private boolean inRange(Point p, Point from, Point to) {
        int d = p.dimension();
        for (int i = 0; i < d; i++) {
            int v = p.get(i);
            if (v < from.get(i) || v > to.get(i)) {
                return false;
            }
        }
        return true;
    }


    class Node {

        // internal node
        int splitValue;
        Node left;
        Node right;

        // leaf node
        List<PointTid> points;

        // leaf constructor
        Node(PointTid pt) {
            this.points = new ArrayList<>();
            this.points.add(pt);
        }

        boolean isLeaf() {
            return points != null;
        }

        // split leaf into internal node
        Node split(int depth, int[] dims) {
            int axis = dims[depth % dims.length];

            points.sort(Comparator.comparingInt(
                    p -> p.point.get(axis)));

            int mid = points.size() / 2;
            splitValue = points.get(mid).point.get(axis);

            Node l = new Node();
            Node r = new Node();

            l.points = new ArrayList<>(points.subList(0, mid));
            r.points = new ArrayList<>(points.subList(mid, points.size()));

            this.points = null;
            this.left = l;
            this.right = r;

            return this;
        }

        // internal constructor
        private Node() {}
    }

}
