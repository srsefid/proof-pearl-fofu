package lib;

public class Edge {
    private int from, to, capacity, flow, index;

    public Edge(int from, int to, int capacity, int flow, int index) {
        this.from = from;
        this.to = to;
        this.capacity = capacity;
        this.flow = flow;
        this.index = index;
    }

    public int getFrom() {
        return from;
    }

    public int getTo() {
        return to;
    }

    public int getCapacity() {
        return capacity;
    }

    public int getFlow() {
        return flow;
    }

    public int getIndex() {
        return index;
    }

    public void changeFlow(int change){
        this.flow += change;
    }

    public void changeIndex(int change){
        this.flow += change;
    }
}