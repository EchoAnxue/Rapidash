package rangetree.lsm;

import rangetree.Point;

public class PointTid {
    public final Point point;
    public final int tid;

    public PointTid(Point point, int tid) {
        this.point = point;
        this.tid = tid;
    }
}
