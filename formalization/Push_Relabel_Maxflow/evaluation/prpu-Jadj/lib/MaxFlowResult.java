package lib;

public class MaxFlowResult {
    private long time, flowValue;
    private int dc, pc, rc,gc;


    public MaxFlowResult(long time, long flowValue, int dischargeCount, int pushCount, int relabelCount, int gapCount) {
        this.time = time;
        this.flowValue = flowValue;

        this.dc = dischargeCount;
        this.pc = pushCount;
        this.rc = relabelCount;
        this.gc = gapCount;
    }

    public long getTime() {
        return time;
    }

    public long getFlowValue() {
        return flowValue;
    }

    public int getDischargeCount() {
        return dc;
    }

    public int getPushCount() {
        return pc;
    }

    public int getRelabelCount() {
        return rc;
    }

    public int getGapCount() {
        return gc;
    }
    
}
