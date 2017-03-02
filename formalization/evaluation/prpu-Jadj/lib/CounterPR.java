package lib;

public class CounterPR {
    private int dc, pc, rc, gc;

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

    public int getGapCount() {
        return gc;
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
    
    public void incGap(){
        this.gc++;
    }
    
}
