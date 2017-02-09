package lib;

public class CounterPR {
    private int dc, pc, rc;

    public CounterPR() {
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

    public void incDischarge(){
        this.dc++;
    }

    public void incPush(){
        this.pc++;
    }

    public void incRelabel(){
        this.rc++;
    }
}
