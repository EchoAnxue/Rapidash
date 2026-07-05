package KDimensionRangeTree;

import rangetree.Point;
import rangetree.setUtil.IntArray;
import rangetree.setUtil.Utils;
import tidset.*;
import java.util.*;

/**
 * Minimal-intrusion modification of RangeTreeCountSetLazy:
 * - only the first dimension (root level) is balanced by a Treap
 * - inner nodes keep the original recursive insertion/query logic
 * - last dimension still uses lazy base+delta materialization
 *
 * Notes:
 * - This removes the O(N) depth degeneration on monotone inserts at the first dimension.
 * - Expected height guarantee applies to the first dimension only.
 */
public class RangeTreeCountSetLazyFirstDimTreap {

    public static class Stats {
        public long splitCount = 0;
        public long cloneNodeCount = 0;
        public long flushCount = 0;
        public long materializeCount = 0;
        public long rotateLeftCount = 0;
        public long rotateRightCount = 0;

        public void reset() {
            splitCount = 0;
            cloneNodeCount = 0;
            flushCount = 0;
            materializeCount = 0;
            rotateLeftCount = 0;
            rotateRightCount = 0;
        }

        @Override
        public String toString() {
            return String.format(
                    "splits=%d, clones=%d, flushes=%d, materializes=%d, rotL=%d, rotR=%d",
                    splitCount, cloneNodeCount, flushCount, materializeCount, rotateLeftCount, rotateRightCount
            );
        }
    }

    public static final Stats STATS = new Stats();
    private Node root;
    private int topDimension = -1;

    public RangeTreeCountSetLazyFirstDimTreap() {
        root = null;
    }

    public void insert(Point p, int tid) {
        if (root == null) {
            topDimension = p.dimension() - 1;
            root = new Node(p, topDimension, tid, topDimension);
        } else {
            root = root.insert(p, tid);
        }
    }

    public TIdSet query(Point from, Point to) {
        if (root == null) return Utils.createNewTIdSet();
        TIdSet out = Utils.createNewTIdSet();
        root.queryInto(from, to, out);
        return out;
    }

    public void queryInto(Point from, Point to, TIdSet acc) {
        if (root == null) return;
        root.queryInto(from, to, acc);
    }

    public boolean isEmpty() {
        return root == null;
    }

    // ===================== Node =====================
    private static class Node {
        private static final Random RAND = new Random(42);

        private final int topDimension;
        private final boolean treapLevel;

        private int dimension;
        private int value;

        private int min;
        private int max;

        private Node left;
        private Node right;
        private Node inner;

        // Treap metadata (used only at first dimension)
        private int priority;

        // ---- Lazy TidSet ----
        private TIdSet base;
        private IntArray delta;
        private static final int DELTA_THRESHOLD = 1024;

        public Node(Point p, int dimension, int tid, int topDimension) {
            this.topDimension = topDimension;
            this.treapLevel = (dimension == topDimension);
            this.dimension = dimension;
            this.value = p.get(dimension);
            this.min = value;
            this.max = value;
            this.left = null;
            this.right = null;
            this.priority = RAND.nextInt();

            if (dimension == 0) {
                this.inner = null;
                this.base = Utils.createNewTIdSet();
                this.delta = new IntArray();
                this.delta.add(tid);
            } else {
                this.inner = new Node(p, dimension - 1, tid, topDimension);
                this.base = null;
                this.delta = null;
            }
        }

        public Node(Node node) {
            this.topDimension = node.topDimension;
            this.treapLevel = node.treapLevel;
            this.dimension = node.dimension;
            this.value = node.value;
            this.min = node.min;
            this.max = node.max;
            this.priority = node.priority;

            this.left = (node.left == null) ? null : new Node(node.left);
            this.right = (node.right == null) ? null : new Node(node.right);

            if (node.inner == null) {
                this.inner = null;
                this.base = node.base;
                this.delta = node.delta.clone();
            } else {
                this.inner = new Node(node.inner);
                this.base = null;
                this.delta = null;
            }
            STATS.cloneNodeCount++;
        }

        public Node insert(Point p, int tid) {
            Node out = treapLevel ? insertTreap(p, tid) : insertOriginal(p, tid);
            // the current point must also be propagated to lower dimensions / last-dim lazy set
            if (out.inner != null) {
                out.inner = out.inner.insert(p, tid);
            } else {
                out.delta.add(tid);
                out.maybeFlush();
            }
            out.pullUp();
            return out;
        }

        /** Original insertion logic (kept for inner levels only). */
        private Node insertOriginal(Point p, int tid) {
            if (left != null) {
                if (p.get(dimension) < value) {
                    left = left.insertOriginal(p, tid);
                    min = left.min;
                } else {
                    right = right.insertOriginal(p, tid);
                    max = right.max;
                }
            } else {
                if (p.get(dimension) > value) {
                    left = new Node(this);
                    right = new Node(p, dimension, tid, topDimension);
                    value = p.get(dimension);
                    max = value;
                    STATS.splitCount++;
                } else if (p.get(dimension) < value) {
                    right = new Node(this);
                    left = new Node(p, dimension, tid, topDimension);
                    min = p.get(dimension);
                    STATS.splitCount++;
                }
                // equal key: keep leaf as is; only inner/lazy update will happen later
            }
            pullUp();
            return this;
        }

        /** Treap insertion only for the first dimension. */
        private Node insertTreap(Point p, int tid) {
            int key = p.get(dimension);

            if (left == null) { // leaf / single-key node in the original representation
                if (key > value) {
                    left = new Node(this);
                    right = new Node(p, dimension, tid, topDimension);
                    value = key;
                    max = value;
                    STATS.splitCount++;
                } else if (key < value) {
                    right = new Node(this);
                    left = new Node(p, dimension, tid, topDimension);
                    min = key;
                    STATS.splitCount++;
                }
                // equal key: no structural change
                pullUp();
                return this;
            }

            if (key < value) {
                if (left == null) {
                    left = new Node(p, dimension, tid, topDimension);
                } else {
                    left = left.insertTreap(p, tid);
                }
                if (left != null && left.priority > this.priority) {
                    return rotateRight();
                }
            } else {
                if (right == null) {
                    right = new Node(p, dimension, tid, topDimension);
                } else {
                    right = right.insertTreap(p, tid);
                }
                if (right != null && right.priority > this.priority) {
                    return rotateLeft();
                }
            }

            pullUp();
            return this;
        }

        private Node rotateRight() {
            Node newRoot = left;
            left = newRoot.right;
            newRoot.right = this;
            this.pullUp();
            newRoot.pullUp();
            STATS.rotateRightCount++;
            return newRoot;
        }

        private Node rotateLeft() {
            Node newRoot = right;
            right = newRoot.left;
            newRoot.left = this;
            this.pullUp();
            newRoot.pullUp();
            STATS.rotateLeftCount++;
            return newRoot;
        }

        private void pullUp() {
            if (left == null && right == null) {
                min = value;
                max = value;
                return;
            }
            min = (left != null) ? left.min : value;
            max = (right != null) ? right.max : value;
        }

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
                    (from.get(dimension) < min || (from.get(dimension) == min && from.getInclusive(dimension)))
                            &&
                    (to.get(dimension) > max || (to.get(dimension) == max && to.getInclusive(dimension)));

            if (fullyCovered) {
                if (inner == null) {
                    base = materialize();
                    delta.clear();
                    return base.clone();
                }
                return inner.query(from, to);
            }

            TIdSet leftSet = Utils.createNewTIdSet();
            if (left != null) leftSet = left.query(from, to);
            TIdSet rightSet = Utils.createNewTIdSet();
            if (right != null) rightSet = right.query(from, to);
            return leftSet.union(rightSet);
        }

        private void queryInto(Point from, Point to, TIdSet acc) {
            if (to.get(dimension) < min || from.get(dimension) > max) return;
            if (to.get(dimension) == min && !to.getInclusive(dimension)) return;
            if (from.get(dimension) == max && !from.getInclusive(dimension)) return;

            boolean fullyCovered =
                    (from.get(dimension) < min || (from.get(dimension) == min && from.getInclusive(dimension)))
                            &&
                    (to.get(dimension) > max || (to.get(dimension) == max && to.getInclusive(dimension)));

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
            if (left != null) left.queryInto(from, to, acc);
            if (right != null) right.queryInto(from, to, acc);
        }

        private TIdSet materialize() {
            if (delta.isEmpty()) return base;
            TIdSet newBase = base.clone();
            newBase.add(delta.getData(), delta.getSize());
            this.base = newBase;
            STATS.materializeCount++;
            return newBase;
        }

        private void maybeFlush() {
            if (delta.size() >= DELTA_THRESHOLD) {
                base = materialize();
                delta.clear();
                STATS.flushCount++;
            }
        }
    }
}
