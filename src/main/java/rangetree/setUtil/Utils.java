package rangetree.setUtil;

import tidset.*;

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

}
