package rangetree.setUtil;

import rangetree.Point;
import tidset.*;

public class RangeTreeCountSet {
	private Node root;

	public RangeTreeCountSet() {
		root = null;
	}
	
	public void insert(Point p,int tid) {
		if (root == null) {
			root = new Node(p, p.dimension() - 1, tid);
		}
		else {
			root.insert(p, tid);
		}
	}
	
	public TIdSet query(Point from, Point to) {
		if (root == null) {
			return Utils.createNewTIdSet();
		}
		else {
			return root.query(from, to);
		}
	}


	private class Node {
		private final int dimension;
		private int value; // for non-leaf nodes, this value is the minimum value of its right subtree
		
		private int min;
		private int max;
		private Node left;
		private Node right;
		private final Node inner;
		private TIdSet count;
		
		public Node(Point p, int dimension,int tid) {
			if (dimension == 0) {
				this.inner = null;
				this.count = Utils.createNewTIdSet().add(tid);
			} else {
				this.inner = new Node(p, dimension - 1,tid);
				this.count =  Utils.createNewTIdSet().add(tid);
			}
			
			this.dimension = dimension;
			this.value = p.get(dimension);
			this.left = null;
			this.right = null;
			this.min = this.value;
			this.max = this.value;
		}
		
		public Node(Node node) {
			if (node.getInner() == null) {
				this.inner = null;
//                important! use deep copy ,otherwise introduce conflict
				this.count = node.getCount().clone();
			} else {
				this.inner = new Node(node.getInner());
			}
			
			if (node.getLeft() == null) {
				this.left = null;
			} else {
				this.left = new Node(node.getLeft());
			}
			
			if (node.getRight() == null) {
				this.right = null;
			} else {
				this.right = new Node(node.getRight());
			}
			this.dimension = node.getDimension();
			this.value = node.getValue();
			this.min = node.getMin();
			this.max = node.getMax();
		}
		
		public TIdSet getCount() {
			return count;
		}
		
		public Node getInner() {
			return inner;
		}
		
		public Node getLeft() {
			return left;
		}
		
		public Node getRight() {
			return right;
		}
		
		public int getValue() {
			return value;
		}
		
		public int getMin() {
			return min;
		}
		
		public int getMax() {
			return max;
		}
		
		public int getDimension() {
			return dimension;
		}
		
		public void printNode() {
			printNode(this, "");
		}
		
		private void printNode(Node node, String prefix) {
	        if (node == null) {
	            return;
	        }
	        if (node.count.isEmpty()) {
	        	System.out.println(prefix + " + " + node.value);
	        } else {
	        	System.out.print(prefix + " + " + node.value + " : [");
	        	System.out.print(node.count);
	        	System.out.println("]");
	        }
	        printNode(node.left, prefix + " ");
	        printNode(node.right, prefix + " ");
		}
		
		public void insert(Point p,int tid) {
			if (left != null) {
//                内部节点是一定有左右子节点的
				// When the current node is not a leaf node
				if (p.get(dimension) < value) {
					left.insert(p,tid);
					min = left.min;

				} else {
					right.insert(p,tid);
					max = right.max;
				}
			} else {
				// When the current node is a leaf node
				if (p.get(dimension) > value) {
					left = new Node(this);
					right = new Node(p, dimension,tid);
					value = p.get(dimension);
					max = p.get(dimension);
				} else if (p.get(dimension) < value) {
					right = new Node(this);
					left = new Node(p, dimension,tid);
					min = p.get(dimension);
				}
			}
			if (inner != null) {
				inner.insert(p,tid);
			} else {
				count.add(tid);
			}
		}
		
		public TIdSet query(Point from, Point to) {
//            TODO maybe can join the computation
			
			if (to.get(dimension) < min || from.get(dimension) > max) {
				return Utils.createNewTIdSet();
			}
			if (to.get(dimension) == min && !to.getInclusive(dimension)) {
				return Utils.createNewTIdSet();
			}
			if (from.get(dimension) == max && !from.getInclusive(dimension)) {
				return Utils.createNewTIdSet();
			}
			if ((from.get(dimension) < min || from.get(dimension) == min && from.getInclusive(dimension)) && 
					(to.get(dimension) > max || to.get(dimension) == max && to.getInclusive(dimension))) {
				if (inner == null) {
					return count;
				}
				return inner.query(from, to);
			} else {
				return left.query(from, to).union(right.query(from, to));
			}
		}
	}
}
