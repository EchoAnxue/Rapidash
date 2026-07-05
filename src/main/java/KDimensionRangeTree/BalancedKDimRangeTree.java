package KDimensionRangeTree;

import java.util.*;

/**
 * Balanced k-dimensional range tree with partial rebuilding.
 *
 * Design goals:
 * 1) Every primary tree in every dimension is height-balanced by subtree rebuild.
 * 2) Insert is amortized O(log^k n).
 * 3) Query supports orthogonal range search.
 * 4) The last dimension stores tuple ids lazily as base + delta arrays.
 *
 * This implementation is self-contained and uses standard Java collections.
 */
public class BalancedKDimRangeTree {

    public static final class Entry {
        public final int[] coords;
        public final int tid;

        public Entry(int[] coords, int tid) {
            this.coords = coords;
            this.tid = tid;
        }
    }

    public static final class Range {
        public final long[] low;
        public final long[] high;
        public final boolean[] lowInclusive;
        public final boolean[] highInclusive;

        public Range(long[] low, long[] high, boolean[] lowInclusive, boolean[] highInclusive) {
            this.low = low;
            this.high = high;
            this.lowInclusive = lowInclusive;
            this.highInclusive = highInclusive;
        }
    }

    private static final class IntBag {
        private int[] data;
        private int size;

        IntBag() {
            this(8);
        }

        IntBag(int capacity) {
            this.data = new int[Math.max(1, capacity)];
            this.size = 0;
        }

        void add(int x) {
            ensure(size + 1);
            data[size++] = x;
        }

        void addAll(IntBag other) {
            ensure(size + other.size);
            System.arraycopy(other.data, 0, data, size, other.size);
            size += other.size;
        }

        void addTo(BitSet acc) {
            for (int i = 0; i < size; i++) {
                acc.set(data[i]);
            }
        }

        void clear() {
            size = 0;
        }

        boolean isEmpty() {
            return size == 0;
        }

        int size() {
            return size;
        }

        IntBag copy() {
            IntBag out = new IntBag(size);
            out.size = size;
            System.arraycopy(data, 0, out.data, 0, size);
            return out;
        }

        private void ensure(int need) {
            if (need <= data.length) return;
            int cap = data.length;
            while (cap < need) cap <<= 1;
            data = Arrays.copyOf(data, cap);
        }
    }

    public static final class Stats {
        public long rebuildCount = 0;
        public long materializeCount = 0;
        public long nodeCount = 0;
    }

    private static final class Node {
        final int dim;
        int value;   // split value = min of right subtree in current dimension
        int min;
        int max;
        int size;    // number of leaves in subtree

        Node left;
        Node right;
        Node inner;

        // Leaf payload
        Entry leaf;

        // Last-dimension lazy payload
        IntBag base;
        IntBag delta;

        Node(int dim) {
            this.dim = dim;
        }

        boolean isLeaf() {
            return left == null && right == null;
        }
    }

    private static final double ALPHA = 0.70; // subtree rebuild threshold
    private static final int DELTA_THRESHOLD = 1024;

    private final int dimensions;
    private final Stats stats = new Stats();
    private Node root;

    public BalancedKDimRangeTree(int dimensions) {
        if (dimensions <= 0) throw new IllegalArgumentException("dimensions must be positive");
        this.dimensions = dimensions;
        this.root = null;
    }

    public Stats stats() {
        return stats;
    }

    public boolean isEmpty() {
        return root == null;
    }

    public void insert(int[] coords, int tid) {
        if (coords.length != dimensions) {
            throw new IllegalArgumentException("dimension mismatch");
        }
        Entry e = new Entry(Arrays.copyOf(coords, coords.length), tid);
        root = insertRecursive(root, e, dimensions - 1);
    }

    public BitSet query(Range range) {
        BitSet out = new BitSet();
        queryInto(root, range, out);
        return out;
    }

    private Node insertRecursive(Node node, Entry e, int dim) {
        if (node == null) {
            return makeLeaf(e, dim);
        }

        if (node.isLeaf()) {
            ArrayList<Entry> two = new ArrayList<>(2);
            two.add(node.leaf);
            two.add(e);
            return buildBalanced(two, dim);
        }

        if (e.coords[dim] < node.value) {
            node.left = insertRecursive(node.left, e, dim);
        } else {
            node.right = insertRecursive(node.right, e, dim);
        }

        if (dim > 0) {
            node.inner = insertRecursive(node.inner, e, dim - 1);
        } else {
            node.delta.add(e.tid);
            maybeFlush(node);
        }

        pullUp(node);
        if (isUnbalanced(node)) {
            node = rebuild(node, dim);
        }
        return node;
    }

    private void queryInto(Node node, Range range, BitSet acc) {
        if (node == null) return;
        int d = node.dim;

        if (disjoint(node, range, d)) return;

        if (fullyCovered(node, range, d)) {
            if (node.inner == null) {
                materialize(node);
                node.base.addTo(acc);
            } else {
                queryInto(node.inner, range, acc);
            }
            return;
        }

        queryInto(node.left, range, acc);
        queryInto(node.right, range, acc);
    }

    private boolean disjoint(Node node, Range range, int d) {
        if (range.high[d] < node.min || range.low[d] > node.max) return true;
        if (range.high[d] == node.min && !range.highInclusive[d]) return true;
        if (range.low[d] == node.max && !range.lowInclusive[d]) return true;
        return false;
    }

    private boolean fullyCovered(Node node, Range range, int d) {
        boolean lowOk = (range.low[d] < node.min) || (range.low[d] == node.min && range.lowInclusive[d]);
        boolean highOk = (range.high[d] > node.max) || (range.high[d] == node.max && range.highInclusive[d]);
        return lowOk && highOk;
    }

    private Node rebuild(Node node, int dim) {
        ArrayList<Entry> entries = new ArrayList<>(node.size);
        collectEntries(node, entries);
        stats.rebuildCount++;
        return buildBalanced(entries, dim);
    }

    private void collectEntries(Node node, List<Entry> out) {
        if (node == null) return;
        if (node.isLeaf()) {
            out.add(node.leaf);
            return;
        }
        collectEntries(node.left, out);
        collectEntries(node.right, out);
    }

    private Node buildBalanced(List<Entry> entries, int dim) {
        if (entries.isEmpty()) return null;
        if (entries.size() == 1) {
            return makeLeaf(entries.get(0), dim);
        }

        entries.sort(entryComparator(dim));
        int mid = entries.size() >>> 1;

        List<Entry> leftEntries = new ArrayList<>(entries.subList(0, mid));
        List<Entry> rightEntries = new ArrayList<>(entries.subList(mid, entries.size()));

        Node u = new Node(dim);
        stats.nodeCount++;
        u.left = buildBalanced(leftEntries, dim);
        u.right = buildBalanced(rightEntries, dim);
        u.value = u.right.min; // split by min of right subtree, consistent with your current code style
        pullUp(u);

        if (dim > 0) {
            ArrayList<Entry> innerEntries = new ArrayList<>(entries);
            u.inner = buildBalanced(innerEntries, dim - 1);
            u.base = null;
            u.delta = null;
        } else {
            u.inner = null;
            u.base = new IntBag(entries.size());
            for (Entry e : entries) {
                u.base.add(e.tid);
            }
            u.delta = new IntBag();
        }
        return u;
    }

    private Node makeLeaf(Entry e, int dim) {
        Node leaf = new Node(dim);
        stats.nodeCount++;
        leaf.leaf = e;
        leaf.value = e.coords[dim];
        leaf.min = e.coords[dim];
        leaf.max = e.coords[dim];
        leaf.size = 1;
        if (dim > 0) {
            leaf.inner = makeLeaf(e, dim - 1);
            leaf.base = null;
            leaf.delta = null;
        } else {
            leaf.inner = null;
            leaf.base = new IntBag(1);
            leaf.delta = new IntBag(1);
            leaf.delta.add(e.tid);
            maybeFlush(leaf);
        }
        return leaf;
    }

    private void pullUp(Node node) {
        if (node.isLeaf()) {
            node.size = 1;
            node.min = node.value;
            node.max = node.value;
            return;
        }
        node.size = size(node.left) + size(node.right);
        node.min = (node.left != null) ? node.left.min : node.value;
        node.max = (node.right != null) ? node.right.max : node.value;
    }

    private int size(Node node) {
        return node == null ? 0 : node.size;
    }

    private boolean isUnbalanced(Node node) {
        if (node == null || node.isLeaf()) return false;
        int l = size(node.left);
        int r = size(node.right);
        return Math.max(l, r) > ALPHA * node.size;
    }

    private void materialize(Node node) {
        if (node.delta == null || node.delta.isEmpty()) return;
        IntBag newBase = node.base.copy();
        newBase.addAll(node.delta);
        node.base = newBase;
        node.delta.clear();
        stats.materializeCount++;
    }

    private void maybeFlush(Node node) {
        if (node.delta != null && node.delta.size() >= DELTA_THRESHOLD) {
            materialize(node);
        }
    }

    private Comparator<Entry> entryComparator(int dim) {
        return (a, b) -> {
            int cmp = Integer.compare(a.coords[dim], b.coords[dim]);
            if (cmp != 0) return cmp;
            for (int i = dimensions - 1; i >= 0; i--) {
                if (i == dim) continue;
                cmp = Integer.compare(a.coords[i], b.coords[i]);
                if (cmp != 0) return cmp;
            }
            return Integer.compare(a.tid, b.tid);
        };
    }
}
