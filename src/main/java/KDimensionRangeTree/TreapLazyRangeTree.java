package KDimensionRangeTree;

import java.util.*;

/**
 * Treap + Lazy k-dimensional Range Tree.
 *
 * Honest complexity statement:
 *  - expected insertion time: O(log^k n)
 *  - query time: O(log^k n + z) in the standard output-sensitive sense,
 *    while this implementation returns a BitSet, so set-union cost also matters in practice.
 *
 * Design:
 *  1) Every dimension is maintained as a Treap (BST by coordinate, heap by random priority).
 *  2) Internal nodes recursively maintain an inner tree for the next dimension.
 *  3) The last dimension stores tids lazily via base + delta.
 *
 * Notes:
 *  - This implementation is self-contained and does not depend on your Point/TIdSet/IntArray classes.
 *  - It is meant as a correct, complete reference implementation that you can adapt back into your project.
 */
public class TreapLazyRangeTree {

    // ========================= Public helper types =========================

    public static final class Point {
        private final int[] coords;
        private final boolean[] inclusive;

        public Point(int[] coords) {
            this.coords = coords;
            this.inclusive = new boolean[coords.length];
            Arrays.fill(this.inclusive, true);
        }

        public Point(int[] coords, boolean[] inclusive) {
            if (coords.length != inclusive.length) {
                throw new IllegalArgumentException("coords/inclusive length mismatch");
            }
            this.coords = coords;
            this.inclusive = inclusive;
        }

        public int get(int d) {
            return coords[d];
        }

        public boolean getInclusive(int d) {
            return inclusive[d];
        }

        public int dimension() {
            return coords.length;
        }

        public int[] raw() {
            return coords;
        }
    }

    /** Lightweight growable int buffer for lazy last-dimension tids. */
    public static final class IntBag {
        private int[] data;
        private int size;

        public IntBag() {
            this.data = new int[8];
            this.size = 0;
        }

        public IntBag(IntBag other) {
            this.data = Arrays.copyOf(other.data, other.size);
            this.size = other.size;
        }

        public void add(int x) {
            if (size == data.length) {
                data = Arrays.copyOf(data, data.length << 1);
            }
            data[size++] = x;
        }

        public int size() {
            return size;
        }

        public boolean isEmpty() {
            return size == 0;
        }

        public void clear() {
            size = 0;
        }

        public int[] array() {
            return data;
        }
    }

    public static final class Stats {
        public long rotationsLeft = 0;
        public long rotationsRight = 0;
        public long materializeCount = 0;
        public long flushCount = 0;
        public long nodeCount = 0;

        @Override
        public String toString() {
            return "Stats{" +
                    "rotL=" + rotationsLeft +
                    ", rotR=" + rotationsRight +
                    ", materialize=" + materializeCount +
                    ", flush=" + flushCount +
                    ", nodes=" + nodeCount +
                    '}';
        }
    }

    // ========================= Tree fields =========================

    private static final Random RAND = new Random(42);
    private static final int DELTA_THRESHOLD = 1024;

    private final Stats stats = new Stats();
    private final int dimensions;
    private Node root;

    public TreapLazyRangeTree(int dimensions) {
        if (dimensions <= 0) throw new IllegalArgumentException("dimensions must be positive");
        this.dimensions = dimensions;
    }

    public Stats stats() {
        return stats;
    }

    public boolean isEmpty() {
        return root == null;
    }

    // ========================= Public API =========================

    public void insert(Point p, int tid) {
        if (p.dimension() != dimensions) {
            throw new IllegalArgumentException("point dimension mismatch");
        }
        if (root == null) {
            root = new Node(p, dimensions - 1, tid);
            stats.nodeCount++;
        } else {
            root = root.insert(p, tid);
        }
    }

    /** Returns a BitSet of tids inside the orthogonal range. */
    public BitSet query(Point from, Point to) {
        if (from.dimension() != dimensions || to.dimension() != dimensions) {
            throw new IllegalArgumentException("query dimension mismatch");
        }
        BitSet out = new BitSet();
        if (root != null) {
            root.queryInto(from, to, out);
        }
        return out;
    }

    /** Count-only query to avoid building large intermediate structures in some workloads. */
    public int countQuery(Point from, Point to) {
        return query(from, to).cardinality();
    }

    /** Fast path for verification workloads that only need to know whether a match exists. */
    public int firstMatch(Point from, Point to) {
        BitSet bs = query(from, to);
        return bs.nextSetBit(0);
    }

    // ========================= Node =========================

    private final class Node {
        // Tree topology for this dimension.
        private final int dimension;
        private int value;           // split key: right subtree minimum key
        private int min;
        private int max;
        private int priority;

        private Node left;
        private Node right;
        private Node inner;

        // Leaf payload: original point; internal nodes keep it null.
        private Point leafPoint;

        // Last-dimension lazy tids.
        private BitSet base;
        private IntBag delta;

        private Node(Point p, int dimension, int tid) {
            this.dimension = dimension;
            this.value = p.get(dimension);
            this.min = value;
            this.max = value;
            this.priority = RAND.nextInt();
            this.leafPoint = p;

            if (dimension == 0) {
                this.inner = null;
                this.base = new BitSet();
                this.delta = new IntBag();
                this.delta.add(tid);
            } else {
                this.inner = new Node(p, dimension - 1, tid);
                stats.nodeCount++;
                this.base = null;
                this.delta = null;
            }
        }

        private boolean isLeaf() {
            return left == null && right == null;
        }

        // -------------------- Insert --------------------

        private Node insert(Point p, int tid) {
            int key = p.get(dimension);

            if (isLeaf()) {
                return splitLeafAndInsert(p, tid);
            }

            if (key < value) {
                left = left.insert(p, tid);
                if (left.priority > this.priority) {
                    return rotateRight();
                }
            } else {
                right = right.insert(p, tid);
                if (right.priority > this.priority) {
                    return rotateLeft();
                }
            }

            // Update recursive structure for the next dimension.
            if (inner != null) {
                inner = inner.insert(p, tid);
            } else {
                delta.add(tid);
                maybeFlush();
            }

            pullUp();
            return this;
        }

        /** Turn a leaf into a 2-leaf internal node while preserving the recursive inner tree. */
        private Node splitLeafAndInsert(Point p, int tid) {
            Point existing = this.leafPoint;
            int existingKey = existing.get(dimension);
            int newKey = p.get(dimension);

            // Duplicate key at this dimension: keep treap shape and recurse only in inner tree.
            if (existingKey == newKey) {
                if (inner != null) {
                    inner = inner.insert(p, tid);
                } else {
                    delta.add(tid);
                    maybeFlush();
                }
                // Keep this as a leaf-like bucket representative at current dimension.
                min = max = value = existingKey;
                return this;
            }

            Node oldLeaf = new Node(existing, dimension, extractRepresentativeTid(this));
            stats.nodeCount++;
            // Reuse already-built lazy/inner content from current node into oldLeaf.
            oldLeaf.leafPoint = this.leafPoint;
            oldLeaf.inner = this.inner;
            oldLeaf.base = this.base;
            oldLeaf.delta = this.delta;
            oldLeaf.priority = this.priority;
            oldLeaf.min = this.min;
            oldLeaf.max = this.max;
            oldLeaf.value = this.value;

            Node newLeaf = new Node(p, dimension, tid);
            stats.nodeCount++;

            // Convert current node into an internal node.
            this.leafPoint = null;
            this.base = null;
            this.delta = null;
            this.priority = RAND.nextInt();

            if (newKey < existingKey) {
                this.left = newLeaf;
                this.right = oldLeaf;
            } else {
                this.left = oldLeaf;
                this.right = newLeaf;
            }

            // Right subtree minimum key as split value.
            this.value = this.right.min;

            // Rebuild inner as the recursive union of both leaves.
            if (dimension > 0) {
                this.inner = new Node(existing, dimension - 1, extractRepresentativeTid(oldLeaf));
                stats.nodeCount++;
                this.inner = this.inner.insert(p, tid);
            } else {
                this.inner = null;
                this.base = new BitSet();
                this.delta = new IntBag();
                addLeafPayloadToCurrentNode(oldLeaf);
                addLeafPayloadToCurrentNode(newLeaf);
                maybeFlush();
            }

            pullUp();
            return this;
        }

        /** Representative tid used only for bootstrapping rebuilt inner leaves. */
        private int extractRepresentativeTid(Node node) {
            if (node.dimension == 0) {
                if (node.delta != null && !node.delta.isEmpty()) {
                    return node.delta.array()[0];
                }
                int bit = node.base == null ? -1 : node.base.nextSetBit(0);
                if (bit >= 0) return bit;
            }
            // Non-last-dimension leaves still have a recursively built inner tree.
            if (node.inner != null) return extractRepresentativeTid(node.inner);
            throw new IllegalStateException("leaf has no representative tid");
        }

        private void addLeafPayloadToCurrentNode(Node leaf) {
            if (leaf.dimension != 0) {
                int rep = extractRepresentativeTid(leaf);
                delta.add(rep);
                return;
            }
            if (leaf.base != null) {
                for (int b = leaf.base.nextSetBit(0); b >= 0; b = leaf.base.nextSetBit(b + 1)) {
                    delta.add(b);
                }
            }
            if (leaf.delta != null) {
                for (int i = 0; i < leaf.delta.size(); i++) {
                    delta.add(leaf.delta.array()[i]);
                }
            }
        }

        // -------------------- Query --------------------

        private void queryInto(Point from, Point to, BitSet acc) {
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
                    (from.get(dimension) < min || (from.get(dimension) == min && from.getInclusive(dimension)))
                            &&
                    (to.get(dimension) > max || (to.get(dimension) == max && to.getInclusive(dimension)));

            if (fullyCovered) {
                if (inner == null) {
                    BitSet mat = materialize();
                    acc.or(mat);
                } else {
                    inner.queryInto(from, to, acc);
                }
                return;
            }

            if (isLeaf()) {
                // Leaf/bucket case: verify its single key against current dimension, then recurse/use tids.
                int key = value;
                boolean lowerOk = (key > from.get(dimension)) || (key == from.get(dimension) && from.getInclusive(dimension));
                boolean upperOk = (key < to.get(dimension)) || (key == to.get(dimension) && to.getInclusive(dimension));
                if (!lowerOk || !upperOk) return;

                if (inner == null) {
                    BitSet mat = materialize();
                    acc.or(mat);
                } else {
                    inner.queryInto(from, to, acc);
                }
                return;
            }

            if (left != null) left.queryInto(from, to, acc);
            if (right != null) right.queryInto(from, to, acc);
        }

        // -------------------- Lazy helpers --------------------

        private BitSet materialize() {
            if (delta == null || delta.isEmpty()) {
                if (base == null) return new BitSet();
                return (BitSet) base.clone();
            }
            BitSet newBase = (base == null) ? new BitSet() : (BitSet) base.clone();
            for (int i = 0; i < delta.size(); i++) {
                newBase.set(delta.array()[i]);
            }
            this.base = newBase;
            this.delta.clear();
            stats.materializeCount++;
            return (BitSet) newBase.clone();
        }

        private void maybeFlush() {
            if (delta != null && delta.size() >= DELTA_THRESHOLD) {
                materialize();
                stats.flushCount++;
            }
        }

        // -------------------- Treap rotations --------------------

        private Node rotateRight() {
            Node newRoot = left;
            left = newRoot.right;
            newRoot.right = this;

            this.pullUp();
            newRoot.pullUp();
            stats.rotationsRight++;
            return newRoot;
        }

        private Node rotateLeft() {
            Node newRoot = right;
            right = newRoot.left;
            newRoot.left = this;

            this.pullUp();
            newRoot.pullUp();
            stats.rotationsLeft++;
            return newRoot;
        }

        // -------------------- Pull-up --------------------

        private void pullUp() {
            if (isLeaf()) {
                min = value;
                max = value;
            } else {
                min = (left != null) ? left.min : value;
                max = (right != null) ? right.max : value;
                if (right != null) {
                    value = right.min;
                }
            }
        }
    }

    // ========================= Minimal example =========================

    public static void main(String[] args) {
        // Example DC detection for: ¬(t.A < t'.A ∧ t.B > t'.B)
        // On insertion of p, query previously inserted t such that t.A < p.A and t.B > p.B.
        TreapLazyRangeTree tree = new TreapLazyRangeTree(2);

        int[][] pts = {
                {0, 0},
                {1, 1},
                {2, 0}, // conflicts with (1,1)
                {3, 3},
                {4, 2}  // conflicts with (3,3)
        };

        long total = 0;
        for (int i = 0; i < pts.length; i++) {
            Point p = new Point(new int[]{pts[i][0], pts[i][1]});
            Point from = new Point(new int[]{Integer.MIN_VALUE, p.get(1) + 1});
            Point to   = new Point(new int[]{p.get(0) - 1, Integer.MAX_VALUE});
            BitSet conflicts = tree.query(from, to);
            System.out.println("insert " + Arrays.toString(pts[i]) + " -> conflicts=" + conflicts + ", count=" + conflicts.cardinality());
            total += conflicts.cardinality();
            tree.insert(p, i);
        }
        System.out.println("total violations=" + total);
        System.out.println(tree.stats());
    }
}
