package lib;

public class MaxFlowResult {
    private long time, flowValue;
    private int dc, pc, rc;


    public MaxFlowResult(long time, long flowValue, int dischargeCount, int pushCount, int relabelCount) {
        this.time = time;
        this.flowValue = flowValue;

        this.dc = dischargeCount;
        this.pc = pushCount;
        this.rc = relabelCount;
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
    
}
