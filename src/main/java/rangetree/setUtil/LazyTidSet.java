package rangetree.setUtil;

import tidset.TIdSet;

public class LazyTidSet {
    private TIdSet base;          // materialized bitmap
    private IntArray delta;       // newly inserted tids
    private static final int DELTA_THRESHOLD = 1024;

    public LazyTidSet() {
        this.base = Utils.createNewTIdSet();
        this.delta = new IntArray();
    }

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

    public void add(int tid){
        delta.add(tid);
        maybeFlush();
    }

    @Override
    public TIdSet clone(){
        base =  materialize();
        delta.clear();
        return base.clone();
    }
}