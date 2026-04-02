package rangetree.setUtil;

import tidset.*;
import javax.management.*;
import javax.management.openmbean.CompositeData;
import java.lang.management.*;
import com.sun.management.GarbageCollectionNotificationInfo;
public class Utils{
    static TIdSetType type = TIdSetType.RoaringBitSet;
    public static boolean storeViolations =true;
    public static TIdSet createNewTIdSet() {
        switch (type) {
            case HashSet:
                return new HashTIdSet();
            case JavaBitSet:
                return new BitTidSet();
            case RoaringBitSet:
                return new RoaringTidSet();
        }
        return new RoaringTidSet();
    }


    public class GCMonitor {

        public static void install() {
            for (GarbageCollectorMXBean bean :
                    ManagementFactory.getGarbageCollectorMXBeans()) {

                if (bean instanceof NotificationEmitter emitter) {
                    emitter.addNotificationListener((n, hb) -> {
                        if (n.getType()
                                .equals(GarbageCollectionNotificationInfo
                                        .GARBAGE_COLLECTION_NOTIFICATION)) {

                            var info =
                                    GarbageCollectionNotificationInfo
                                            .from((CompositeData) n.getUserData());

                            long pause = info.getGcInfo().getDuration();

                            if (pause > 10) {
                                System.out.println(
                                        "GC PAUSE " + pause + "ms, cause=" +
                                                info.getGcCause());
                            }
                        }
                    }, null, null);
                }
            }
        }
    }

}
