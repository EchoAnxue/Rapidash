package rangetree.lsm;

import rangetree.Point;
import rangetree.setUtil.RangeTreeCountSetLazy;
import rangetree.setUtil.Utils;
import tidset.TIdSet;

import java.util.ArrayList;
import java.util.List;
import java.util.Timer;

public class LSMRangeTree {

    private static final int T = 100;

    private List<PointTid> buffer = new ArrayList<>();
    private RangeTreeCountSetLazy level1 = new RangeTreeCountSetLazy();
    int[] selectiveDims = {0, 1}; // 例如 DC 中最 selective 的属性
    private L0KDTree l0 = new L0KDTree(2,T);

    public TIdSet rangeCount(Point low, Point up,Point p, int tid) {
//        1. query L0
        List<Integer> cands = l0.rangeQuery(low, up);



        // 2. insert into L0
         l0.insert(new PointTid(p, tid));
         buffer.add(new PointTid(p, tid));
        TIdSet can = Utils.createNewTIdSet();
         if (!level1.isEmpty()){
             can = level1.query(low, up);
         }

//        TODO list union tidset
        for(Integer cand : cands){
            can.add(cand);
        }
        insert(p,tid);
        return can;

    }

    public void insert(Point p, int tid) {
        // 4. maybe merge
        if (buffer.size() >= T) {
            mergeBuffer();
        }
        l0.clear();
    }
    private void mergeBuffer() {

        List<PointTid> all = new ArrayList<>(buffer);

            for (PointTid pointTid: all)
//                TODO: sort all ,make it balance
                level1.insert(pointTid.point, pointTid.tid);


//        else {
//            level1 = RangeTreeCountSetLazy.bulkBuild(all);
//        }



        buffer.clear();
    }

}
