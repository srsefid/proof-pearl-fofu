package lib;

public class MaxFlowResult {
    private long time, flowValue;


    public MaxFlowResult(long time, long flowValue) {
        this.time = time;
        this.flowValue = flowValue;
    }

    public long getTime() {
        return time;
    }

    public long getFlowValue() {
        return flowValue;
    }
}
