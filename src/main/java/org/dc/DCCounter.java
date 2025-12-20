package org.dc;

import it.unimi.dsi.fastutil.ints.Int2ObjectMap;
import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap;
import kdrange.KeyDuplicateException;
import kdrange.KeySizeException;
import rangetree.setUtil.RangeTreeSetHelper;
import rangetree.setUtil.Utils;
import tidset.TIdSet;
import trees.AVLTree;

import java.sql.Connection;
import java.sql.DriverManager;
import java.util.*;

public class DCCounter {
	ArrayList<Constraint> atomDCs = new ArrayList<Constraint>();
	InputTable input;
	boolean violationCountTwice;
    final ArrayList<int[]> idTKey = new ArrayList<int[]>();
    int maxTid=0;
    final Int2ObjectOpenHashMap<TIdSet> finalTMatches =  new Int2ObjectOpenHashMap<>();
    String dbName ="D:/ZAX_file/CODE/INFFICIAL/Weever/data/results/tax_DC1_random.db";


    //
    /*
     @value Int2ObjectOpenHashMap<Key=tId, Value=TIdSet>
    (existingTuple, newTuple) 方向
     */
    final Int2ObjectOpenHashMap<TIdSet> finalTPrimeMatches =  new Int2ObjectOpenHashMap<>();
    TIdSet allTuples = Utils.createNewTIdSet();
	public DCCounter(Constraint DC, InputTable input) {
		this.input = input;
		boolean allEq = true;
		for (Predicate pred : DC.predicates) {
			if (!pred.operator.equals("==")) {
				allEq = false;
				break;
			}
		}
		this.violationCountTwice = DC.isSymmetric && !allEq;
		if (this.violationCountTwice) {
			System.out.println("[Optimaization] Prune constraints by symmetricity during decomposition");
		}
		this.atomDCs = DC.decompose();
		System.out.println("[Decompose] Constraints after decomposition:");
		for (Constraint atomDC : atomDCs) {
			System.out.println("- " + atomDC);
		}
	}
	
	public long detectViolation(boolean earlyStop, String treeType) throws KeySizeException, KeyDuplicateException {
		long violationCount = 0;
		for (Constraint DC : atomDCs) {
			violationCount += detectViolationSingle(DC, earlyStop, treeType);
			if (earlyStop && violationCount > 0) {
				return violationCount;
			}
		}
		if (this.violationCountTwice) {
			violationCount *= 2;
		}
		return violationCount;
	}
	
	private long detectViolationSingle(Constraint DC, boolean earlyStop, String treeType) throws KeySizeException, KeyDuplicateException {
		System.out.println("\nDetecting violations for: " + DC);
		ArrayList<Integer> homoEqLocs = new ArrayList<Integer>();
        ArrayList<Integer> heteroEqLocs1 = new ArrayList<>();
        ArrayList<Integer> heteroEqLocs2 = new ArrayList<>();
		// Column indices and operator of the inequalities
		ArrayList<Integer> uneqLocs1 = new ArrayList<Integer>();
		ArrayList<Integer> uneqLocs2 = new ArrayList<Integer>();
		ArrayList<String> ops = new ArrayList<String>();
		for (Predicate pred : DC.predicates) {
			if (pred.operator.equals("==")&&(pred.column1.equals(pred.column2))) {
//                如果是跨列已经被decompose成不等式了
//                同列 等式
				homoEqLocs.add(this.input.nameLoc.get(pred.column1));
			} else
            if (pred.operator.equals("==")&&(!pred.column1.equals(pred.column2)))
            {
                heteroEqLocs1.add(this.input.nameLoc.get(pred.column1));
                heteroEqLocs2.add(this.input.nameLoc.get(pred.column2));
            }
            else
            {
//                跨列等式也被加入这个
				uneqLocs1.add(this.input.nameLoc.get(pred.column1));
				uneqLocs2.add(this.input.nameLoc.get(pred.column2));
				ops.add(pred.operator);
			}
		}
//        System.err.println(ops);
//        System.err.println(uneqLocs1);

		if (ops.size() == 0) {
			System.out.println("[Type] Equation-only DC");

            if (heteroEqLocs2.size() == 0) {
                return countDups(homoEqLocs, earlyStop);
            }
            else return HeteroCountDups(homoEqLocs, earlyStop,heteroEqLocs1,heteroEqLocs2);
		}
		if (ops.size() >= 1) {
            System.out.println("[Inequality DC ] size = "+ops.size());
			if (earlyStop) {
//                verification
				System.out.println("[Type] Homogeneous DC");
				System.out.println("[Optimaization] Only keep tack of min/max");
				return boolViolationsMinMax(homoEqLocs, uneqLocs1.get(0), uneqLocs2.get(0), ops.get(0));
			}
			if (uneqLocs1.equals(uneqLocs2)) {

                if (heteroEqLocs2.size() == 0) {
                    System.out.println("[Type] Homogeneous DC");
                    return countViolationsRangeTreeHomo(homoEqLocs,  uneqLocs1, ops, earlyStop);
                }
                else{
                    System.out.println("[Type] Heterogeneous Equal and homogeneous inequality ");
                    return countViolationsRangeTreeHeteroEqualHomo(homoEqLocs,heteroEqLocs1,heteroEqLocs2, uneqLocs1, ops, earlyStop);
                }

//				return countViolationsAVLTreeHomo(homoEqLocs, uneqLocs1.get(0), ops.get(0), earlyStop);
			} else {
                if (heteroEqLocs2.size() == 0) {
                    System.out.println("[Type] Heterogeneous DC[only inequality] ");
                    return countViolationsRangeTreeHeter(homoEqLocs, uneqLocs1,uneqLocs2, ops, earlyStop);
                }
                else{
//               值得是列名相等不是 列的数量相等
                    System.out.println("[Type] Heterogeneous DC with hetero Equality");
                    return countViolationsRangeTreeHeteroEqualHeter(homoEqLocs,heteroEqLocs1,heteroEqLocs2, uneqLocs1, uneqLocs2, ops, earlyStop);
//				return countViolationsAVLTreeHeter(homoEqLocs, uneqLocs1.get(0), uneqLocs2.get(0), ops.get(0), earlyStop);
                }

			}
		}
		
		if (ops.size() == 2 && !earlyStop) {
			if (uneqLocs1.equals(uneqLocs2)) {
				System.out.println("[Type] Homogeneous DC (two inequalities)");
				System.out.println("[Optimaization] Insert one column in an sorted order to reduce the tree dimension by one.");
//              insist using range tree
                return countViolationsRangeTreeHomo(homoEqLocs, uneqLocs1, ops, earlyStop);
                //				return this.countViolationsAVLTreeHomoInsertInOrder(homoEqLocs, uneqLocs1.get(0), ops.get(0),
//						uneqLocs1.get(1), ops.get(1), earlyStop);
			}
		}
//		最general的形式
		if (uneqLocs1.equals(uneqLocs2)) {
			System.out.println("[Type] Homogeneous DC (multiple inequalities), using " + treeType);
			if (treeType.equals("kd-tree")) {
//				return countViolationsKDTreeHomo(homoEqLocs, uneqLocs1, ops, earlyStop);
			} else {
				return countViolationsRangeTreeHomo(homoEqLocs, uneqLocs1, ops, earlyStop);
			}
		} else {
			System.out.println("[Type] Heterogeneous DC (multiple inequalities), using " + treeType);
			if (treeType.equals("kd-tree")) {
//				return countViolationsKDTreeHeter(homoEqLocs, uneqLocs1, uneqLocs2, ops, earlyStop);
			} else {
				return countViolationsRangeTreeHeter(homoEqLocs, uneqLocs1, uneqLocs2, ops, earlyStop);
			}
		}
        return 0;
	}
//TODO
    private long countViolationsRangeTreeHeteroEqualHeter(ArrayList<Integer> homoEqLocs, ArrayList<Integer> heteroEqLocs1, ArrayList<Integer> heteroEqLocs2,
                                                          ArrayList<Integer> uneqLocsLeft, ArrayList<Integer> uneqLocsRight, ArrayList<String> ops, boolean earlyStop) {
        /*
         * Use range trees to find violations.
         * The columns on the left-hand-side and the right-hand-side are different.
         */


        Map<List<Integer>, RangeTreeSetHelper> treesMapAsLeftSide = new HashMap<>();
        Map<List<Integer>, RangeTreeSetHelper> treesMapAsRightSide = new HashMap<>();

        List<Integer> indices = new ArrayList<>();
        for (int i = 0; i < input.data.length; i++) {
            indices.add(i);
        }
//        Collections.shuffle(indices);
        int  measureGranularity =1000;

        long insertTimeSum = 0;
        long longestInsertTime = 0;
        int longestTId = 0;

        long[] timePerHundredth = new long[indices.size() / measureGranularity + 1];
        int[] errorsPerHundredth = new int[indices.size() / measureGranularity + 1];
//
        for (int i : indices) {
            long tStart = System.nanoTime();
            List<Integer> eqValuesLeft = new ArrayList<>();
            List<Integer> eqValuesRight = new ArrayList<>();
            for (int j : homoEqLocs) {
                eqValuesLeft.add(input.data[i][j]);
                eqValuesRight.add(input.data[i][j]);
            }
            for (int j : heteroEqLocs1){
                eqValuesLeft.add(input.data[i][j]);
            }
            for (int j : heteroEqLocs2){
                eqValuesRight.add(input.data[i][j]);
            }

            int[] ineqValuesLeft = new int[ops.size()];
            for (int k = 0; k < ops.size(); k++) {
                ineqValuesLeft[k] = input.data[i][uneqLocsLeft.get(k)];
            }
            int[] ineqValuesRight = new int[ops.size()];
            for (int k = 0; k < ops.size(); k++) {
                ineqValuesRight[k] = input.data[i][uneqLocsRight.get(k)];
            }

//            idTKey.add(ineqValuesRight);// not used
            int tid = maxTid++;
            TIdSet violationCount = Utils.createNewTIdSet();
            int[] upperBound = new int[ops.size()];
            int[] lowerBound = new int[ops.size()];
            boolean[] inclusive = new boolean[ops.size()];
            if (treesMapAsLeftSide.containsKey(eqValuesRight)) {

                computeBounds(ineqValuesRight, upperBound, lowerBound, ops, inclusive);
                violationCount.union(treesMapAsLeftSide.get(eqValuesRight).rangeCount(lowerBound, upperBound, inclusive));
            }
            if(!treesMapAsLeftSide.containsKey(eqValuesLeft)){
                treesMapAsLeftSide.put(eqValuesLeft,new RangeTreeSetHelper());
            }
            treesMapAsLeftSide.get(eqValuesLeft).insert(ineqValuesLeft, tid);

            if(!treesMapAsRightSide.containsKey(eqValuesLeft)) {

                computeBounds(ineqValuesLeft, upperBound, lowerBound, reverseOp(ops), inclusive);
                violationCount.union(treesMapAsRightSide.get(eqValuesLeft).rangeCount(lowerBound, upperBound, inclusive));
            }
            if(!treesMapAsRightSide.containsKey(eqValuesRight)){
                treesMapAsRightSide.put(eqValuesRight,new RangeTreeSetHelper());
            }
            treesMapAsRightSide.get(eqValuesRight).insert(ineqValuesRight,tid);


            if (earlyStop && violationCount.cardinality() > 0) {
                return violationCount.cardinality();
            }

            allTuples.add(tid);
            if (violationCount.cardinality() > 0) {

                finalTMatches.put(tid, violationCount);
            }
/***
 * time computation
 */
            long tmp = System.nanoTime() - tStart;
            insertTimeSum += tmp;
            if (tmp > longestInsertTime) {
                longestInsertTime = tmp;
                longestTId = tid;
            }
            if ((tid + 1) % measureGranularity == 0) {
//                每1k次插入汇报一下情况
//                System.out.println(tid+1);
                timePerHundredth[(tid + 1) / measureGranularity] = insertTimeSum / 1000000;
                int sum = getSumOfViolationsForOneSide( finalTMatches) ;

                errorsPerHundredth[(tid + 1) / measureGranularity] =sum;
                try {
                    Class.forName("org.sqlite.JDBC");
                    Connection c = DriverManager.getConnection("jdbc:sqlite:" + dbName);
                    c.setAutoCommit(false);
                    var stmt = c.createStatement();
                    stmt.executeUpdate(String.format("INSERT INTO %s (run_id, tuples, time, violations) VALUES ('%s', %s, %s, %s);", "RA", 8, tid + 1, insertTimeSum / 1000000, sum));
                    stmt.close();
                    c.commit();
                    c.close();
                } catch (Exception e) {
                    System.out.println(e.getMessage());
                }



            }
        }
        System.out.println("====result=========");
        System.out.println(Arrays.toString(timePerHundredth));
        System.out.println(Arrays.toString(errorsPerHundredth));
        return 0;
    }


    private long countViolationsRangeTreeHomo(ArrayList<Integer> homoEqLocs, ArrayList<Integer> uneqLocs, ArrayList<String> ops, boolean earlyStop) {

            /*
             * Use range trees to find violations.
             * The columns on the left-hand-side and the right-hand-side are the same.
             */

            Map<List<Integer>, RangeTreeSetHelper> treesMap = new HashMap<>();

            List<Integer> indices = new ArrayList<>();

            for (int i = 0; i < input.data.length; i++) {
                indices.add(i);
            }

//    	Collections.shuffle(indices);
        /*
        preparation
         */
            int  measureGranularity =1000;

            long insertTimeSum = 0;
            long longestInsertTime = 0;
            int longestTId = 0;

            long[] timePerHundredth = new long[indices.size() / measureGranularity + 1];
            int[] errorsPerHundredth = new int[indices.size() / measureGranularity + 1];
//




//    insert
            for (int i : indices) {
                long tStart = System.nanoTime();
                List<Integer> eqValues = new ArrayList<>();
                for (int j : homoEqLocs) {
                    eqValues.add(input.data[i][j]);
                }
                int[] ineqValues = new int[ops.size()];
                for (int k = 0; k < ops.size(); k++) {
                    ineqValues[k] = input.data[i][uneqLocs.get(k)];
                }

                idTKey.add(ineqValues);
                int tid = maxTid++;
            /*
            每个tid 对应的operand ：violationCount
             */
                TIdSet violationCount = Utils.createNewTIdSet();
                TIdSet inter = Utils.createNewTIdSet();
                if (treesMap.containsKey(eqValues)) {
                    int[] upperBound = new int[ops.size()];
                    int[] lowerBound = new int[ops.size()];
                    boolean[]  inclusive = new boolean[ops.size()];

                    computeBounds(ineqValues, upperBound, lowerBound, ops,inclusive);
                    violationCount.union( treesMap.get(eqValues).rangeCount(lowerBound, upperBound,inclusive));
                    computeBounds(ineqValues, upperBound, lowerBound, reverseOp(ops),inclusive);
                    inter = treesMap.get(eqValues).rangeCount(lowerBound, upperBound,inclusive);
                    violationCount.union(inter );
                    if(violationCount.cardinality() > 0){
                        if (earlyStop && violationCount.cardinality() > 0) {
                            return violationCount.cardinality();
                        }
                    }

                } else {
                    treesMap.put(eqValues, new RangeTreeSetHelper());
                }
                treesMap.get(eqValues).insert(ineqValues, i);
                allTuples.add(tid);
                if (violationCount.cardinality() > 0) {

                    finalTMatches.put(tid, violationCount);
                }


//            operand = matches.get(id-1).union(violationCount);
//            matches.put(id,operand);
// end  insert
                long tmp = System.nanoTime() - tStart;
                insertTimeSum += tmp;
                if (tmp > longestInsertTime) {
                    longestInsertTime = tmp;
                    longestTId = tid;
                }
                if ((tid + 1) % measureGranularity == 0) {
//                每1k次插入汇报一下情况
//                System.out.println(tid+1);
                    timePerHundredth[(tid + 1) / measureGranularity] = insertTimeSum / 1000000;
                    int sum = getSumOfViolationsForOneSide( finalTMatches) ;

                    errorsPerHundredth[(tid + 1) / measureGranularity] =sum;
                    try {
                        Class.forName("org.sqlite.JDBC");
                        Connection c = DriverManager.getConnection("jdbc:sqlite:" + dbName);
                        c.setAutoCommit(false);
                        var stmt = c.createStatement();
                        stmt.executeUpdate(String.format("INSERT INTO %s (run_id, tuples, time, violations) VALUES ('%s', %s, %s, %s);", "RA", 8, tid + 1, insertTimeSum / 1000000, sum));
                        stmt.close();
                        c.commit();
                        c.close();
                    } catch (Exception e) {
                        System.out.println(e.getMessage());
                    }



                }



            }
            System.out.println("====result=========");
            System.out.println(Arrays.toString(timePerHundredth));
            System.out.println(Arrays.toString(errorsPerHundredth));
            return 0;
    }

    private long HeteroCountDups(ArrayList<Integer> homoEqLocs, boolean earlyStop, ArrayList<Integer> heteroEqLocs1, ArrayList<Integer> heteroEqLocs2) {
        /*
         * Use a hash set to detect violations when the constraint only contains equalities.
         */

        Map<List<Integer>, TIdSet> counterLeft = new HashMap<>();
        Map<List<Integer>, TIdSet> counterRight = new HashMap<>();


        List<Integer> indices = new ArrayList<>();

        for (int i = 0; i < input.data.length; i++) {
            indices.add(i);
        }
//        TODO : comparison between shuffle and non-shuffle
//    	Collections.shuffle(indices);
        /*
        preparation
         */
        int  measureGranularity =1000;

        long insertTimeSum = 0;
        long longestInsertTime = 0;
        int longestTId = 0;

        long[] timePerHundredth = new long[indices.size() / measureGranularity + 1];
        int[] errorsPerHundredth = new int[indices.size() / measureGranularity + 1];
//




//    insert
        for (int i : indices) {
            long tStart = System.nanoTime();

            List<Integer> eqValuesLeft = new ArrayList<>();
            List<Integer> eqValuesRight = new ArrayList<>();
            for (int j : homoEqLocs) {
                eqValuesLeft.add(input.data[i][j]);
                eqValuesRight.add(input.data[i][j]);
            }
            for (int j : heteroEqLocs1){
                eqValuesLeft.add(input.data[i][j]);
            }
            for (int j : heteroEqLocs2){
                eqValuesRight.add(input.data[i][j]);
            }


//            idTKey.add(ineqValues);
            int tid = maxTid++;
            /*
            每个tid 对应的operand ：violationCount
             */
            TIdSet violationCount = Utils.createNewTIdSet();

            if (counterLeft.containsKey(eqValuesRight)) {

                violationCount = counterLeft.get(eqValuesRight).clone();


            }
            if( !counterLeft.containsKey(eqValuesLeft)) {

                counterLeft.put(eqValuesLeft, Utils.createNewTIdSet());
            }
            counterLeft.get(eqValuesLeft).add( i);
            if(counterRight.containsKey(eqValuesLeft)){
                violationCount.union(counterRight.get(eqValuesLeft).clone());

            }
            if(!counterRight.containsKey(eqValuesRight)) {
                counterRight.put(eqValuesRight, Utils.createNewTIdSet());
            }
            counterRight.get(eqValuesRight).add( i);


            if(violationCount.cardinality() > 0){
                if (earlyStop && violationCount.cardinality() > 0) {
                    return violationCount.cardinality();
                }
            }


            allTuples.add(tid);
            if (violationCount.cardinality() > 0) {

                finalTMatches.put(tid, violationCount);
            }


//            operand = matches.get(id-1).union(violationCount);
//            matches.put(id,operand);
// end  insert
            long tmp = System.nanoTime() - tStart;
            insertTimeSum += tmp;
            if (tmp > longestInsertTime) {
                longestInsertTime = tmp;
                longestTId = tid;
            }
            if ((tid + 1) % measureGranularity == 0) {
//                每1k次插入汇报一下情况
//                System.out.println(tid+1);
                timePerHundredth[(tid + 1) / measureGranularity] = insertTimeSum / 1000000;
                int sum = getSumOfViolationsForOneSide( finalTMatches) ;

                errorsPerHundredth[(tid + 1) / measureGranularity] =sum;
                try {
                    Class.forName("org.sqlite.JDBC");
                    Connection c = DriverManager.getConnection("jdbc:sqlite:" + dbName);
                    c.setAutoCommit(false);
                    var stmt = c.createStatement();
                    stmt.executeUpdate(String.format("INSERT INTO %s (run_id, tuples, time, violations) VALUES ('%s', %s, %s, %s);", "RA", 3, tid + 1, insertTimeSum / 1000000, sum));
                    stmt.close();
                    c.commit();
                    c.close();
                } catch (Exception e) {
                    System.out.println(e.getMessage());
                }



            }



        }
        System.out.println("====result=========");
        System.out.println(Arrays.toString(timePerHundredth));
        System.out.println(Arrays.toString(errorsPerHundredth));
        return 0;
    }


    private long countViolationsRangeTreeHeter(ArrayList<Integer> homoEqLocs, ArrayList<Integer> uneqLocsLeft,
                                               ArrayList<Integer> uneqLocsRight, ArrayList<String> ops, boolean earlyStop) {
        /*
         * Use range trees to find violations.
         * The columns on the left-hand-side and the right-hand-side are different.
         */


        Map<List<Integer>, RangeTreeSetHelper> treesMapAsLeftSide = new HashMap<>();
        Map<List<Integer>, RangeTreeSetHelper> treesMapAsRightSide = new HashMap<>();

        List<Integer> indices = new ArrayList<>();
        for (int i = 0; i < input.data.length; i++) {
            indices.add(i);
        }
//        Collections.shuffle(indices);
        int  measureGranularity =1000;

        long insertTimeSum = 0;
        long longestInsertTime = 0;
        int longestTId = 0;

        long[] timePerHundredth = new long[indices.size() / measureGranularity + 1];
        int[] errorsPerHundredth = new int[indices.size() / measureGranularity + 1];
//
        for (int i : indices) {
            long tStart = System.nanoTime();
            List<Integer> eqValues = new ArrayList<>();
            for (int j : homoEqLocs) {
                eqValues.add(input.data[i][j]);
            }
            int[] ineqValuesLeft = new int[ops.size()];
            for (int k = 0; k < ops.size(); k++) {
                ineqValuesLeft[k] = input.data[i][uneqLocsLeft.get(k)];
            }
            int[] ineqValuesRight = new int[ops.size()];
            for (int k = 0; k < ops.size(); k++) {
                ineqValuesRight[k] = input.data[i][uneqLocsRight.get(k)];
            }

//            idTKey.add(ineqValuesRight);// not used
            int tid = maxTid++;
            TIdSet violationCount = Utils.createNewTIdSet();
            if (treesMapAsLeftSide.containsKey(eqValues)) {
                int[] upperBound = new int[ops.size()];
                int[] lowerBound = new int[ops.size()];
                boolean[]  inclusive = new boolean[ops.size()];
                computeBounds(ineqValuesRight, upperBound, lowerBound, ops,inclusive);
                violationCount.union(treesMapAsLeftSide.get(eqValues).rangeCount(lowerBound, upperBound,inclusive));

                computeBounds(ineqValuesLeft, upperBound, lowerBound, reverseOp(ops), inclusive);
                violationCount.union(treesMapAsRightSide.get(eqValues).rangeCount(lowerBound, upperBound,inclusive));

                if (earlyStop && violationCount.cardinality() > 0) {
                    return violationCount.cardinality();
                }
            } else {
                treesMapAsLeftSide.put(eqValues, new RangeTreeSetHelper());
                treesMapAsRightSide.put(eqValues, new RangeTreeSetHelper());
            }
//TODO 区分 id 和 tid的区别，不要误用

            treesMapAsLeftSide.get(eqValues).insert(ineqValuesLeft, i);
            treesMapAsRightSide.get(eqValues).insert(ineqValuesRight, i);
            allTuples.add(tid);
            if (violationCount.cardinality() > 0) {

                finalTMatches.put(tid, violationCount);
            }
/***
 * time computation
 */
            long tmp = System.nanoTime() - tStart;
            insertTimeSum += tmp;
            if (tmp > longestInsertTime) {
                longestInsertTime = tmp;
                longestTId = tid;
            }
            if ((tid + 1) % measureGranularity == 0) {
//                每1k次插入汇报一下情况
//                System.out.println(tid+1);
                timePerHundredth[(tid + 1) / measureGranularity] = insertTimeSum / 1000000;
                int sum = getSumOfViolationsForOneSide( finalTMatches) ;

                errorsPerHundredth[(tid + 1) / measureGranularity] =sum;
                try {
                    Class.forName("org.sqlite.JDBC");
                    Connection c = DriverManager.getConnection("jdbc:sqlite:" + dbName);
                    c.setAutoCommit(false);
                    var stmt = c.createStatement();
                    stmt.executeUpdate(String.format("INSERT INTO %s (run_id, tuples, time, violations) VALUES ('%s', %s, %s, %s);", "RA", 8, tid + 1, insertTimeSum / 1000000, sum));
                    stmt.close();
                    c.commit();
                    c.close();
                } catch (Exception e) {
                    System.out.println(e.getMessage());
                }



            }
        }
        System.out.println("====result=========");
        System.out.println(Arrays.toString(timePerHundredth));
        System.out.println(Arrays.toString(errorsPerHundredth));
        return 0;

    }
    private String reverseOp(String op) {
		if (op.equals(">")) return "<";
		if (op.equals("<")) return ">";
		if (op.equals(">=")) return "<=";
		if (op.equals("<=")) return ">=";
		return op;
	}
	
	private ArrayList<String> reverseOp(ArrayList<String> ops) {
		ArrayList<String> opsReversed = new ArrayList<>();
		for (String op : ops) {
			opsReversed.add(reverseOp(op));
		}
		return opsReversed;
	}
	
	private void computeBounds(int[] values, int[] upper, int[] lower, ArrayList<String> ops,boolean[] inclusive) {
		for (int k = 0; k < ops.size(); k++) {
//            TODO 竟然边界直接是加1 然后inclusive 默认设定都是true
//			if (ops.get(k).equals(">")) {lower[k] = values[k] + 1; upper[k] = Integer.MAX_VALUE; inclusive[k] = false; continue;}
//			if (ops.get(k).equals("<")) {lower[k] = Integer.MIN_VALUE; upper[k] = values[k] - 1; inclusive[k] = false; continue;}
//			if (ops.get(k).equals(">=")) {lower[k] = values[k]; upper[k] = Integer.MAX_VALUE;inclusive[k] = true; continue;}
//			if (ops.get(k).equals("<=")) {lower[k] = Integer.MIN_VALUE; upper[k] = values[k];inclusive[k] = true; continue;}
            if(ops.get(k).equals("==")) {lower[k] = values[k] ; upper[k] = values[k] ; inclusive[k] = true; continue;}
            if (ops.get(k).equals(">")) {lower[k] = values[k] ; upper[k] = Integer.MAX_VALUE; inclusive[k] = false; continue;}
            if (ops.get(k).equals("<")) {lower[k] = Integer.MIN_VALUE; upper[k] = values[k] ; inclusive[k] = false; continue;}
            if (ops.get(k).equals(">=")) {lower[k] = values[k]; upper[k] = Integer.MAX_VALUE;inclusive[k] = true; continue;}
            if (ops.get(k).equals("<=")) {lower[k] = Integer.MIN_VALUE; upper[k] = values[k];inclusive[k] = true; continue;}
		}
	}
	
	private long countViolationsRangeTreeHeteroEqualHomo(ArrayList<Integer> homoEqLocs, ArrayList<Integer> heteroEqLocs1, ArrayList<Integer> heteroEqLocs2, ArrayList<Integer> uneqLocs,
			ArrayList<String> ops, boolean earlyStop) {
	    /*
	     * Use range trees to find violations.
	     * The columns on the left-hand-side and the right-hand-side are the same.
	     */

		Map<List<Integer>, RangeTreeSetHelper> treesMapLeft = new HashMap<>();
        Map<List<Integer>, RangeTreeSetHelper> treesMapRight = new HashMap<>();
    	List<Integer> indices = new ArrayList<>();

    	for (int i = 0; i < input.data.length; i++) {
    	    indices.add(i);
    	}

//    	Collections.shuffle(indices);
        /*
        preparation
         */
        int  measureGranularity =1000;

        long insertTimeSum = 0;
        long longestInsertTime = 0;
        int longestTId = 0;

        long[] timePerHundredth = new long[indices.size() / measureGranularity + 1];
        int[] errorsPerHundredth = new int[indices.size() / measureGranularity + 1];
//




//    insert
        for (int i : indices) {
            long tStart = System.nanoTime();
            List<Integer> eqValuesLeft = new ArrayList<>();
            List<Integer> eqValuesRight = new ArrayList<>();
            for (int j : homoEqLocs) {
                eqValuesLeft.add(input.data[i][j]);
                eqValuesRight.add(input.data[i][j]);
            }
            for (int j: heteroEqLocs1){
                eqValuesLeft.add(input.data[i][j]);
            }
            for (int j: heteroEqLocs2){
                eqValuesRight.add(input.data[i][j]);
            }
            int[] ineqValues = new int[ops.size()];
            for (int k = 0; k < ops.size(); k++) {
                ineqValues[k] = input.data[i][uneqLocs.get(k)];
            }

            idTKey.add(ineqValues);
            int tid = maxTid++;
            /*
            每个tid 对应的operand ：violationCount
             */
            TIdSet violationCount = Utils.createNewTIdSet();
            TIdSet inter = Utils.createNewTIdSet();
            int[] upperBound = new int[ops.size()];
            int[] lowerBound = new int[ops.size()];
            boolean[] inclusive = new boolean[ops.size()];
            if (treesMapLeft.containsKey(eqValuesRight)) {


                computeBounds(ineqValues, upperBound, lowerBound, ops, inclusive);
                violationCount.union(treesMapLeft.get(eqValuesRight).rangeCount(lowerBound, upperBound, inclusive));

            }
            if(!treesMapLeft.containsKey(eqValuesLeft)){
                treesMapLeft.put(eqValuesLeft,new RangeTreeSetHelper());
            }
            treesMapLeft.get(eqValuesLeft).insert(ineqValues, tid);


            if (treesMapRight.containsKey(eqValuesLeft)) {
                computeBounds(ineqValues, upperBound, lowerBound, reverseOp(ops),inclusive);
                inter = treesMapRight.get(eqValuesLeft).rangeCount(lowerBound, upperBound,inclusive);
                violationCount.union(inter );
            }
            if(!treesMapRight.containsKey(eqValuesRight)){
                treesMapRight.put(eqValuesRight,new RangeTreeSetHelper());
            }
            treesMapRight.get(eqValuesRight).insert(ineqValues,tid);




            if(violationCount.cardinality() > 0){
                if (earlyStop && violationCount.cardinality() > 0) {
                    return violationCount.cardinality();
                }
            }

            allTuples.add(tid);
            if (violationCount.cardinality() > 0) {

                finalTMatches.put(tid, violationCount);
            }


//            operand = matches.get(id-1).union(violationCount);
//            matches.put(id,operand);
// end  insert
            long tmp = System.nanoTime() - tStart;
            insertTimeSum += tmp;
            if (tmp > longestInsertTime) {
                longestInsertTime = tmp;
                longestTId = tid;
            }
            if ((tid + 1) % measureGranularity == 0) {
//                每1k次插入汇报一下情况
//                System.out.println(tid+1);
                timePerHundredth[(tid + 1) / measureGranularity] = insertTimeSum / 1000000;
                int sum = getSumOfViolationsForOneSide( finalTMatches) ;

                    errorsPerHundredth[(tid + 1) / measureGranularity] =sum;
                try {
                    Class.forName("org.sqlite.JDBC");
                    Connection c = DriverManager.getConnection("jdbc:sqlite:" + dbName);
                    c.setAutoCommit(false);
                    var stmt = c.createStatement();
                    stmt.executeUpdate(String.format("INSERT INTO %s (run_id, tuples, time, violations) VALUES ('%s', %s, %s, %s);", "RA", 8, tid + 1, insertTimeSum / 1000000, sum));
                    stmt.close();
                    c.commit();
                    c.close();
                } catch (Exception e) {
                    System.out.println(e.getMessage());
                }



            }



		}
        System.out.println("====result=========");
        System.out.println(Arrays.toString(timePerHundredth));
        System.out.println(Arrays.toString(errorsPerHundredth));
		return 0;
	}

        private int getSumOfViolationsForOneSide(Int2ObjectOpenHashMap<TIdSet> map) {
            int sum = 0;
            boolean deleteOccurred =false;
            Iterator<Int2ObjectMap.Entry<TIdSet>> mapIter = map.int2ObjectEntrySet().iterator();
            while (mapIter.hasNext()) {
                var id2Matches = mapIter.next();
                TIdSet matches = id2Matches.getValue();
                if (deleteOccurred) {
                    matches.intersect(allTuples);
                    if (matches.isEmpty()) {
                        mapIter.remove();
                    } else {
                        sum += matches.cardinality();
                    }
                } else {
                    sum += matches.cardinality();
                }
            }
            return sum;
        }
//
//    private long countViolationsRangeTreeHeter(ArrayList<Integer> homoEqLocs, ArrayList<Integer> uneqLocsLeft,
//			ArrayList<Integer> uneqLocsRight, ArrayList<String> ops, boolean earlyStop) {
//	    /*
//	     * Use range trees to find violations.
//	     * The columns on the left-hand-side and the right-hand-side are different.
//	     */
//		long violationCount = 0;
//
//		Map<List<Integer>, RangeTreeHelper> treesMapAsLeftSide = new HashMap<>();
//		Map<List<Integer>, RangeTreeHelper> treesMapAsRightSide = new HashMap<>();
//
//    	List<Integer> indices = new ArrayList<>();
//    	for (int i = 0; i < input.data.length; i++) {
//    	    indices.add(i);
//    	}
//    	Collections.shuffle(indices);
//    	for (int i : indices) {
//			List<Integer> eqValues = new ArrayList<>();
//			for (int j : homoEqLocs) {
//				eqValues.add(input.data[i][j]);
//			}
//	        int[] ineqValuesLeft = new int[ops.size()];
//	        for (int k = 0; k < ops.size(); k++) {
//	            ineqValuesLeft[k] = input.data[i][uneqLocsLeft.get(k)];
//	        }
//	        int[] ineqValuesRight = new int[ops.size()];
//	        for (int k = 0; k < ops.size(); k++) {
//	            ineqValuesRight[k] = input.data[i][uneqLocsRight.get(k)];
//	        }
//
//			if (treesMapAsLeftSide.containsKey(eqValues)) {
//				int[] upperBound = new int[ops.size()];
//				int[] lowerBound = new int[ops.size()];
//				computeBounds(ineqValuesRight, upperBound, lowerBound, ops);
//				violationCount += treesMapAsLeftSide.get(eqValues).rangeCount(lowerBound, upperBound);
//
//				computeBounds(ineqValuesLeft, upperBound, lowerBound, reverseOp(ops));
//				violationCount += treesMapAsRightSide.get(eqValues).rangeCount(lowerBound, upperBound);
//
//				if (earlyStop && violationCount > 0) {
//					return violationCount;
//				}
//			} else {
//				treesMapAsLeftSide.put(eqValues, new RangeTreeHelper());
//				treesMapAsRightSide.put(eqValues, new RangeTreeHelper());
//			}
//
//			treesMapAsLeftSide.get(eqValues).insert(ineqValuesLeft, i);
//			treesMapAsRightSide.get(eqValues).insert(ineqValuesRight, i);
//		}
//		return violationCount;
//	}
//
//	private long countViolationsKDTreeHomo(ArrayList<Integer> homoEqLocs, ArrayList<Integer> uneqLocs,
//			ArrayList<String> ops, boolean earlyStop) throws KeySizeException, KeyDuplicateException {
//	    /*
//	     * Use kd trees to find violations.
//	     * The columns on the left-hand-side and the right-hand-side are the same.
//	     */
//		long violationCount = 0;
//		Map<List<Integer>, KDTreeHelper<Integer>> treesMap = new HashMap<>();
//    	List<Integer> indices = new ArrayList<>();
//    	for (int i = 0; i < input.data.length; i++) {
//    	    indices.add(i);
//    	}
//    	Collections.shuffle(indices);
//    	for (int i : indices) {
//			List<Integer> eqValues = new ArrayList<>();
//			for (int j : homoEqLocs) {
//				eqValues.add(input.data[i][j]);
//			}
//	        int[] ineqValues = new int[ops.size()];
//	        for (int k = 0; k < ops.size(); k++) {
//	            ineqValues[k] = input.data[i][uneqLocs.get(k)];
//	        }
//			if (treesMap.containsKey(eqValues)) {
//				int[] upperBound = new int[ops.size()];
//				int[] lowerBound = new int[ops.size()];
//				computeBounds(ineqValues, upperBound, lowerBound, ops);
//				violationCount += treesMap.get(eqValues).rangeCount(lowerBound, upperBound);
//				computeBounds(ineqValues, upperBound, lowerBound, reverseOp(ops));
//				violationCount += treesMap.get(eqValues).rangeCount(lowerBound, upperBound);
//				if (earlyStop && violationCount > 0) {
//					return violationCount;
//				}
//			} else {
//				treesMap.put(eqValues, new KDTreeHelper<>(ops.size()));
//			}
//			treesMap.get(eqValues).insert(ineqValues, i);
//		}
//		return violationCount;
//	}
//
//	private long countViolationsKDTreeHeter(ArrayList<Integer> homoEqLocs, ArrayList<Integer> uneqLocsLeft,
//			ArrayList<Integer> uneqLocsRight, ArrayList<String> ops, boolean earlyStop) throws KeySizeException, KeyDuplicateException {
//	    /*
//	     * Use KD trees to find violations.
//	     * The columns on the left-hand-side and the right-hand-side are different.
//	     */
//		long violationCount = 0;
//
//		Map<List<Integer>, KDTreeHelper<Integer>> treesMapAsLeftSide = new HashMap<>();
//		Map<List<Integer>, KDTreeHelper<Integer>> treesMapAsRightSide = new HashMap<>();
//
//    	List<Integer> indices = new ArrayList<>();
//    	for (int i = 0; i < input.data.length; i++) {
//    	    indices.add(i);
//    	}
//    	Collections.shuffle(indices);
//    	for (int i : indices) {
//			List<Integer> eqValues = new ArrayList<>();
//			for (int j : homoEqLocs) {
//				eqValues.add(input.data[i][j]);
//			}
//	        int[] ineqValuesLeft = new int[ops.size()];
//	        for (int k = 0; k < ops.size(); k++) {
//	            ineqValuesLeft[k] = input.data[i][uneqLocsLeft.get(k)];
//	        }
//	        int[] ineqValuesRight = new int[ops.size()];
//	        for (int k = 0; k < ops.size(); k++) {
//	            ineqValuesRight[k] = input.data[i][uneqLocsRight.get(k)];
//	        }
//
//			if (treesMapAsLeftSide.containsKey(eqValues)) {
//				int[] upperBound = new int[ops.size()];
//				int[] lowerBound = new int[ops.size()];
//				computeBounds(ineqValuesRight, upperBound, lowerBound, ops);
//				violationCount += treesMapAsLeftSide.get(eqValues).rangeCount(lowerBound, upperBound);
//
//				computeBounds(ineqValuesLeft, upperBound, lowerBound, reverseOp(ops));
//				violationCount += treesMapAsRightSide.get(eqValues).rangeCount(lowerBound, upperBound);
//
//				if (earlyStop && violationCount > 0) {
//					return violationCount;
//				}
//			} else {
//				treesMapAsLeftSide.put(eqValues, new KDTreeHelper<>(ops.size()));
//				treesMapAsRightSide.put(eqValues, new KDTreeHelper<>(ops.size()));
//			}
//
//			treesMapAsLeftSide.get(eqValues).insert(ineqValuesLeft, i);
//			treesMapAsRightSide.get(eqValues).insert(ineqValuesRight, i);
//		}
//		return violationCount;
//	}
//
	private long countViolationsAVLTreeHomo(ArrayList<Integer> homoEqLocs, Integer uneqLoc,
			String op, boolean earlyStop) {
	    /*
	     * Use AVL trees to find violations when there is only one inequality.
	     * The columns on the left-hand-side and the right-hand-side are the same.
	     */
		long violationCount = 0;
		Map<List<Integer>, AVLTree> treesMap = new HashMap<>();
		for (int i = 0; i < input.data.length; ++i) {
			List<Integer> eqValues = new ArrayList<>();
			for (int j : homoEqLocs) {
				eqValues.add(input.data[i][j]);
			}
			if (treesMap.containsKey(eqValues)) {
				violationCount += treesMap.get(eqValues).count(input.data[i][uneqLoc], op);
				violationCount += treesMap.get(eqValues).count(input.data[i][uneqLoc], reverseOp(op));
				if (earlyStop && violationCount > 0) {
					return violationCount;
				}
			} else {
				treesMap.put(eqValues, new AVLTree());
			}
			treesMap.get(eqValues).insert(input.data[i][uneqLoc]);
		}	
		return violationCount;
	}
//    使用平衡BST（AVL树）处理第二个不等式谓词


    private long countViolationsAVLTreeHomoInsertInOrder(ArrayList<Integer> homoEqLocs, Integer uneqSortLoc, String opSort,
			Integer uneqLoc, String op, boolean earlyStop) {
	    /*
	     * Applicable to constraints with two homogeneous inequality predicates.
	     * Insert one column in a sorted order, and use AVL trees to check the other one.
	     */
		long violationCount = 0;
		Map<List<Integer>, Integer> prevValueSortLoc = new HashMap<>();;
		Map<List<Integer>, List<Integer>> prevValuesUneqLoc = new HashMap<>();
		if (opSort.startsWith(">")) {
			Arrays.sort(input.data, (a, b) -> Integer.compare(a[uneqSortLoc], b[uneqSortLoc]));
		} else {
			Arrays.sort(input.data, (a, b) -> Integer.compare(-a[uneqSortLoc], -b[uneqSortLoc]));
		}
		
		Map<List<Integer>, AVLTree> treesMap = new HashMap<>();
		for (int i = 0; i < input.data.length; ++i) {
			List<Integer> eqValues = new ArrayList<>();
			for (int j : homoEqLocs) {
				eqValues.add(input.data[i][j]);
			}
			
			if (prevValueSortLoc.containsKey(eqValues) && input.data[i][uneqSortLoc] != prevValueSortLoc.get(eqValues)) {
				for (int value : prevValuesUneqLoc.get(eqValues)) {
					treesMap.get(eqValues).insert(value);
				}
				if (opSort.endsWith("=")) {
					AVLTree tempTree = new AVLTree();
					for (int value : prevValuesUneqLoc.get(eqValues)) {
						violationCount += tempTree.count(value, op);
						violationCount += tempTree.count(value, reverseOp(op));
						if (earlyStop && violationCount > 0) {
							return violationCount;
						}
						tempTree.insert(value);
					}
				}
				prevValuesUneqLoc.get(eqValues).clear();
			} 
			prevValueSortLoc.put(eqValues, input.data[i][uneqSortLoc]);
			if (!prevValuesUneqLoc.containsKey(eqValues)) {
				prevValuesUneqLoc.put(eqValues, new ArrayList<>());
			}
			prevValuesUneqLoc.get(eqValues).add(input.data[i][uneqLoc]);
			
			if (treesMap.containsKey(eqValues)) {
				violationCount += treesMap.get(eqValues).count(input.data[i][uneqLoc], reverseOp(op));
				if (earlyStop && violationCount > 0) {
					return violationCount;
				}
			} else {
				treesMap.put(eqValues, new AVLTree());
			}
		}
		if (opSort.endsWith("=")) {
			for (List<Integer> eqValues : prevValuesUneqLoc.keySet()) {
				AVLTree tempTree = new AVLTree();
				for (int value : prevValuesUneqLoc.get(eqValues)) {
					violationCount += tempTree.count(value, op);
					violationCount += tempTree.count(value, reverseOp(op));
					if (earlyStop && violationCount > 0) {
						return violationCount;
					}
					tempTree.insert(value);
				}
			}
		}
		return violationCount;
	}
	
	private long countViolationsAVLTreeHeter(ArrayList<Integer> homoEqLocs, Integer uneqLocLeft,
			Integer uneqLocRight, String op, boolean earlyStop) {
	    /*
	     * Use AVL trees to find violations when there is only one inequality.
	     * The columns on the left-hand-side and the right-hand-side are different.
	     */
		long violationCount = 0;
		Map<List<Integer>, AVLTree> treesMapAsLeftSide = new HashMap<>();
		Map<List<Integer>, AVLTree> treesMapAsRightSide = new HashMap<>();
		for (int i = 0; i < input.data.length; ++i) {
			List<Integer> eqValues = new ArrayList<>();
			for (int j : homoEqLocs) {
				eqValues.add(input.data[i][j]);
			}
			if (treesMapAsLeftSide.containsKey(eqValues)) {
				violationCount += treesMapAsLeftSide.get(eqValues).count(input.data[i][uneqLocRight], op);
				violationCount += treesMapAsRightSide.get(eqValues).count(input.data[i][uneqLocLeft], reverseOp(op));
				if (earlyStop && violationCount > 0) {
					return violationCount;
				}
			} else {
				treesMapAsLeftSide.put(eqValues, new AVLTree());
				treesMapAsRightSide.put(eqValues, new AVLTree());
			}
			treesMapAsLeftSide.get(eqValues).insert(input.data[i][uneqLocLeft]);
			treesMapAsRightSide.get(eqValues).insert(input.data[i][uneqLocRight]);
		}	
		return violationCount;
	}
	
	private long boolViolationsMinMax(ArrayList<Integer> homoEqLocs, Integer uneqLocLeft,
			Integer uneqLocRight, String op) {
	    /*
	     * Only keep track of the min/max value when there is only one inequality.
	     * For example, for NOT (s.A > t.B), when we insert x, we only need to make sure x.A is not larger than the min of existing B,
	     * and x.B is not smaller than the max of existing A.
	     */
		Map<List<Integer>, Integer> extremeAsLeftSide = new HashMap<>();
		Map<List<Integer>, Integer> extremeAsRightSide = new HashMap<>();
		for (int i = 0; i < input.data.length; ++i) {
			List<Integer> eqValues = new ArrayList<>();
			for (int j : homoEqLocs) {
				eqValues.add(input.data[i][j]);
			}
			if (extremeAsLeftSide.containsKey(eqValues)) {
				if (op.endsWith("=") && (input.data[i][uneqLocLeft] == extremeAsRightSide.get(eqValues) ||
						extremeAsLeftSide.get(eqValues) == input.data[i][uneqLocRight])) {
					return 1;
				}
				if (op.startsWith(">") && (input.data[i][uneqLocLeft] > extremeAsRightSide.get(eqValues) ||
						extremeAsLeftSide.get(eqValues) > input.data[i][uneqLocRight])) {
					return 1;
				}
				if (op.startsWith("<") && (input.data[i][uneqLocLeft] < extremeAsRightSide.get(eqValues) ||
						extremeAsLeftSide.get(eqValues) < input.data[i][uneqLocRight])) {
					return 1;
				}
			} else {
				extremeAsLeftSide.put(eqValues, input.data[i][uneqLocLeft]);
				extremeAsRightSide.put(eqValues, input.data[i][uneqLocRight]);
			}
			if (op.startsWith(">")) {
				extremeAsLeftSide.put(eqValues, Math.max(input.data[i][uneqLocLeft], extremeAsLeftSide.get(eqValues)));
				extremeAsRightSide.put(eqValues, Math.min(input.data[i][uneqLocRight], extremeAsRightSide.get(eqValues)));
			} else {
				extremeAsLeftSide.put(eqValues, Math.min(input.data[i][uneqLocLeft], extremeAsLeftSide.get(eqValues)));
				extremeAsRightSide.put(eqValues, Math.max(input.data[i][uneqLocRight], extremeAsRightSide.get(eqValues)));				
			}
		}	
		return 0;
	}
	
	private long countDups(ArrayList<Integer> colLocs, boolean earlyStop) {
	    /*
	     * Use a hash set to detect violations when the constraint only contains equalities.
	     */

		Map<List<Integer>, TIdSet> counter = new HashMap<>();


        List<Integer> indices = new ArrayList<>();

        for (int i = 0; i < input.data.length; i++) {
            indices.add(i);
        }

//    	Collections.shuffle(indices);
        /*
        preparation
         */
        int  measureGranularity =1000;

        long insertTimeSum = 0;
        long longestInsertTime = 0;
        int longestTId = 0;

        long[] timePerHundredth = new long[indices.size() / measureGranularity + 1];
        int[] errorsPerHundredth = new int[indices.size() / measureGranularity + 1];
//




//    insert
        for (int i : indices) {
            long tStart = System.nanoTime();

            List<Integer> eqValues = new ArrayList<>();
            for (int j : colLocs) {
                eqValues.add(input.data[i][j]);
            }


//            idTKey.add(ineqValues);
            int tid = maxTid++;
            /*
            每个tid 对应的operand ：violationCount
             */
            TIdSet violationCount = Utils.createNewTIdSet();

            if (counter.containsKey(eqValues)) {

                violationCount = counter.get(eqValues).clone();
                if(violationCount.cardinality() > 0){
                    if (earlyStop && violationCount.cardinality() > 0) {
                        return violationCount.cardinality();
                    }
                }

            } else {
                counter.put(eqValues, Utils.createNewTIdSet());
            }




            counter.get(eqValues).add( i);
            allTuples.add(tid);
            if (violationCount.cardinality() > 0) {

                finalTMatches.put(tid, violationCount);
            }


//            operand = matches.get(id-1).union(violationCount);
//            matches.put(id,operand);
// end  insert
            long tmp = System.nanoTime() - tStart;
            insertTimeSum += tmp;
            if (tmp > longestInsertTime) {
                longestInsertTime = tmp;
                longestTId = tid;
            }
            if ((tid + 1) % measureGranularity == 0) {
//                每1k次插入汇报一下情况
//                System.out.println(tid+1);
                timePerHundredth[(tid + 1) / measureGranularity] = insertTimeSum / 1000000;
                int sum = getSumOfViolationsForOneSide( finalTMatches) ;

                errorsPerHundredth[(tid + 1) / measureGranularity] =sum;
                try {
                    Class.forName("org.sqlite.JDBC");
                    Connection c = DriverManager.getConnection("jdbc:sqlite:" + dbName);
                    c.setAutoCommit(false);
                    var stmt = c.createStatement();
                    stmt.executeUpdate(String.format("INSERT INTO %s (run_id, tuples, time, violations) VALUES ('%s', %s, %s, %s);", "RA", 3, tid + 1, insertTimeSum / 1000000, sum));
                    stmt.close();
                    c.commit();
                    c.close();
                } catch (Exception e) {
                    System.out.println(e.getMessage());
                }



            }



        }
        System.out.println("====result=========");
        System.out.println(Arrays.toString(timePerHundredth));
        System.out.println(Arrays.toString(errorsPerHundredth));
     	return 0;
	}


}
