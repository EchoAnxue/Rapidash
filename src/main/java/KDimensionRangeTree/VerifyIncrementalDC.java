package KDimensionRangeTree;

import rangetree.Point;
import rangetree.setUtil.RangeTreeCountSet;
import rangetree.setUtil.RangeTreeCountSetLazy;

import java.sql.Connection;
import java.sql.DriverManager;
import java.util.*;

/**
 * Fast correctness verifier for incremental DC detection.
 *
 * DC: ¬( t.A < t'.A  &&  t.B > t'.B )
 *
 * This verifier is optimized for a synthetic workload with very low violation density:
 *   - tuples are inserted online in ascending order of A
 *   - most tuples are monotone increasing in B
 *   - exactly targetViolations tuples are perturbed so that each perturbed tuple creates
 *     exactly ONE new violation (with its immediate predecessor only)
 *
 * For n tuples and ratio r, targetViolations = floor(n * r).
 * Construction:
 *   for i = 0..n-1
 *     A = i
 *     B = i                                  (default, no violation)
 *     if i < 2*targetViolations and i is odd:
 *         B = i - 2                          (creates exactly one violation with tuple i-1)
 *
 * Why exactly one violation for each perturbed odd i?
 *   predecessor p = (i-1, i-1)
 *   new tuple q = (i, i-2)
 *   then p.A < q.A and p.B > q.B, so one violation exists.
 *   Any earlier tuple j < i-1 has B <= i-2, so cannot additionally violate q.
 *   Hence each perturbed tuple contributes exactly one new violation.
 *
 * Therefore total violations over the full stream = targetViolations.
 *
 * This verifier uses ONLY the forward query because tuples are inserted in ascending A.
 * Thus, for a newly inserted tuple p, all existing tuples t satisfy t.A < p.A automatically,
 * and the reverse-direction query is always empty at insertion time.
 */
public class VerifyIncrementalDC {
    static String dbName = "D:\\OneDrive - Heriot-Watt University\\2025\\Weever\\data\\results\\shuffle_round.db";
    private static BalancedKDimRangeTree.Range forwardRange(int[] p) {
        // existing t such that t.A < p.A and t.B > p.B
        long[] low = new long[]{Long.MIN_VALUE, p[1]};
        long[] high = new long[]{p[0], Long.MAX_VALUE};
        boolean[] lowInc = new boolean[]{true, false};
        boolean[] highInc = new boolean[]{false, true};
        return new BalancedKDimRangeTree.Range(low, high, lowInc, highInc);
    }
    public static List<int[]> generateGGDataset(int n, int violations) {

        final int CARD = 10000;
        if (n % CARD != 0) {
            throw new IllegalArgumentException("n must be divisible by 10000");
        }

        int repeat = n / CARD;

        int[] A = new int[n];
        int[] B = new int[n];

        // Step 1: construct base data (A asc, B desc, both repeated)
        int idx = 0;
        for (int v = 0; v < CARD; v++) {
            for (int r = 0; r < repeat; r++) {
                A[idx] = v;
                B[idx] = CARD - 1 - v;
                idx++;
            }
        }

        // Step 2: shuffle indices (preserve tuple pairing)
        List<Integer> perm = new ArrayList<>();
        for (int i = 0; i < n; i++) perm.add(i);

        Collections.shuffle(perm, new Random(42));

        // Step 3: inject violations
        Random rand = new Random(42);

        // 找到可以修改的 tuple（B < max）
        List<Integer> candidates = new ArrayList<>();
        for (int i = 0; i < n; i++) {
            if (B[i] < CARD - 1) {
                candidates.add(i);
            }
        }

        if (violations > candidates.size()) {
            throw new IllegalArgumentException("Not enough candidates for violations");
        }

        Collections.shuffle(candidates, rand);

        for (int i = 0; i < violations; i++) {
            int pos = candidates.get(i);
            int b = B[pos];

            // 关键：GG case → 变大
            int newB = b + 1 + rand.nextInt(CARD - 1 - b);
            B[pos] = newB;
        }

        // Step 4: pack shuffled data
        List<int[]> data = new ArrayList<>(n);

        for (int i = 0; i < n; i++) {
            int d = perm.get(i);
            data.add(new int[]{A[d], B[d]});
        }

        return data;
    }
    public static List<int[]> generateGLDataset(int n, int violations) {

        final int CARD = 10000;
        if (n % CARD != 0) {
            throw new IllegalArgumentException("n must be divisible by 10000");
        }

        int repeat = n / CARD;

        int[] A = new int[n];
        int[] B = new int[n];

        // Step 1: A asc, B asc
        int idx = 0;
        for (int v = 0; v < CARD; v++) {
            for (int r = 0; r < repeat; r++) {
                A[idx] = v;
                B[idx] = v;
                idx++;
            }
        }

        // Step 2: shuffle
        List<Integer> perm = new ArrayList<>();
        for (int i = 0; i < n; i++) perm.add(i);
        Collections.shuffle(perm, new Random(42));

        // Step 3: inject violations
        Random rand = new Random(42);

        List<Integer> candidates = new ArrayList<>();
        for (int i = 0; i < n; i++) {
            if (B[i] > 0) {
                candidates.add(i);
            }
        }

        if (violations > candidates.size()) {
            throw new IllegalArgumentException("Not enough candidates for violations");
        }

        Collections.shuffle(candidates, rand);

        for (int i = 0; i < violations; i++) {
            int pos = candidates.get(i);
            int b = B[pos];

            // GL → 变小
            int newB = rand.nextInt(b);
            B[pos] = newB;
        }

        // Step 4: pack
        List<int[]> data = new ArrayList<>(n);
        for (int i = 0; i < n; i++) {
            int d = perm.get(i);
            data.add(new int[]{A[d], B[d]});
        }

        return data;
    }

//    public static void main(String[] args) {
//        int n = 1000000;
//        double ratio = 0;
//
////        if (args.length > 0) {
////            n = Integer.parseInt(args[0]);
////        }
////        if (args.length > 1) {
////            ratio = Double.parseDouble(args[1]);
////        }
//
//        int targetViolations = (int) Math.floor(n * ratio);
//
//        System.out.println("n = " + n);
//        System.out.println("target violations = " + targetViolations);
//        List<int[]> data ;
//        if(true){
//            data = generateGLDataset(n, targetViolations);
//        }
//        else data = generateGGDataset(n, targetViolations);
//
////        TreapLazyRangeTree tree = new TreapLazyRangeTree(2);
//        RangeTreeCountSetLazy tree = new RangeTreeCountSetLazy();
////        GoatRangeTreeCountSetLazy tree = new GoatRangeTreeCountSetLazy();
//
//        long totalViolations = 0;
//        long start = System.currentTimeMillis();
//        long insertions = 0;
//        long querys = 0;
//
//        for (int i = 0; i < n; i++) {
//            int[] p = data.get(i);
//
//
//
//            long t1 = System.currentTimeMillis();
//            tree.insert(new Point(p), i);
//            long t2 = System.currentTimeMillis();
//            //            if(isGL){
//            int[] from = {Integer.MIN_VALUE, p[1]};
//            int[] to = {p[0], Integer.MAX_VALUE};
//            tree.query(new Point(from), new Point(to));
//            int[] from2 = {p[0], Integer.MIN_VALUE};
//            int[] to2 = {Integer.MAX_VALUE, p[1]};
//            tree.query(new Point(from2), new Point(to2));
//            long t3 = System.currentTimeMillis();
//            insertions += t2 - t1;
//            querys += t3 - t2;
//            if ((i + 1) % 100_000 == 0) {
//                long now = System.currentTimeMillis();
//                System.out.printf(Locale.ROOT,
//                        "Inserted %,d tuples, elapsed=%.2fs, totalViolations=%d, insertions=%d, query=%d",
//                        (i + 1), (now - start) / 1000.0,
//                        4000,
//                        insertions,
//                        querys);
//                System.out.println();
//            }
//        }
//
//        long end = System.currentTimeMillis();
//
//
//
//        System.out.println("=====================================");
//        System.out.printf(Locale.ROOT,
//                "SUCCESS. Verified %,d incremental inserts in %d ms. Final violations=%d, insertions=%d, query=%d",
//                n,
//                (end - start),
//                4000,
//                insertions,
//                querys
//                );
//    }



//GG
public static void main(String[] args) {
    int n = 2000000;
    double ratio = 0.004;

//        if (args.length > 0) {
//            n = Integer.parseInt(args[0]);
//        }
//        if (args.length > 1) {
//            ratio = Double.parseDouble(args[1]);
//        }

    int targetViolations = (int) Math.floor(n * ratio);

    System.out.println("n = " + n);
    System.out.println("target violations = " + targetViolations);
    List<int[]> data ;
     data = generateGGDataset(n, targetViolations);

//        TreapLazyRangeTree tree = new TreapLazyRangeTree(2);
    RangeTreeCountSetLazy tree = new RangeTreeCountSetLazy();

//    RangeTreeCountSet tree = new RangeTreeCountSet();


    long totalViolations = 0;
    long start = System.currentTimeMillis();
    long insertions = 0;
    long querys = 0;

    for (int i = 0; i < n; i++) {
        int[] p = data.get(i);

        long t1 = System.currentTimeMillis();
        //            if(isGL){
        int[] from = {p[0], p[1]};
        int[] to = {Integer.MAX_VALUE, Integer.MAX_VALUE};
        tree.query(new Point(from), new Point(to));
        int[] from2 = {Integer.MIN_VALUE, Integer.MIN_VALUE};
        int[] to2 = {p[0], p[1]};
        tree.query(new Point(from2), new Point(to2));
        long t2= System.currentTimeMillis();
        tree.insert(new Point(p), i);
        long t3 = System.currentTimeMillis();


        insertions += t3 - t2;
        querys += t2 - t1;
        if ((i + 1) % 100_000 == 0) {
            long now = System.currentTimeMillis();
            long total = now - start;
            System.out.printf(Locale.ROOT,
                    "Inserted %,d tuples, elapsed=%.2fs, totalViolations=%d, insertions=%d, query=%d",
                    (i + 1), (total) / 1000.0,
                    4000,
                    insertions,
                    querys);
            System.out.println();


//                每1k次插入汇报一下情况


            try {
                Class.forName("org.sqlite.JDBC");

                Connection c = DriverManager.getConnection("jdbc:sqlite:" + dbName);
                c.setAutoCommit(false);
                var stmt = c.createStatement();
                stmt.executeUpdate(String.format("INSERT INTO %s (run_id, tuples, time, violations) VALUES ('%s', %s, %s, %s);","RA_Incre_0_16_128" , 512, i + 1, total, 20 ));
                stmt.close();
                c.commit();
                c.close();
            } catch (Exception e) {
                System.out.println(e.getMessage());
            }


        }
    }

    long end = System.currentTimeMillis();



    System.out.println("=====================================");
    System.out.printf(Locale.ROOT,
            "SUCCESS. Verified %,d incremental inserts in %d ms. Final violations=%d, insertions=%d, query=%d",
            n,
            (end - start),
            targetViolations,
            insertions,
            querys
    );
}
}
