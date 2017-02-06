package lib;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.Queue;

import static java.lang.Integer.max;
import static java.lang.Long.min;
import static java.lang.Integer.min;

public class PushRelabel {
    private int N;
    private ArrayList<ArrayList<Edge>> G;
    private long[] excess;
    private boolean[] active;
    private int[] dist, count;
    private Queue<Integer> Q;

    public PushRelabel(int size) {
        this.N = size;

        this.G = new ArrayList<ArrayList<Edge>>(size);
        for (int i = 0; i < size; i++)
            G.add(new ArrayList<Edge>());

        this.excess = new long[size];

        this.dist = new int[size];
        this.active = new boolean[size];
        this.count = new int[2 * size];

        this.Q = new LinkedList<Integer>();
    }

    private void enqueue(int v) {
        if (!active[v] && excess[v] > 0) {
            active[v] = true;
            Q.add(v);
        }
    }

    private void push(Edge e) {
        int amt = (int) (min(excess[e.getFrom()], (e.getCapacity() - e.getFlow())));

        if (dist[e.getFrom()] <= dist[e.getTo()] || amt == 0)
            return;

        e.changeFlow(amt);
        G.get(e.getTo()).get(e.getIndex()).changeFlow(-amt);
        excess[e.getTo()] += amt;
        excess[e.getFrom()] -= amt;
        enqueue(e.getTo());
    }

    private void gap(int k) {
        for (int v = 0; v < N; v++) {
            if (dist[v] < k) continue;
            count[dist[v]]--;
            dist[v] = max(dist[v], N + 1);
            count[dist[v]]++;
            enqueue(v);
        }
    }

    private void relabel(int v) {
        count[dist[v]]--;
        dist[v] = 2 * N;
        for (int i = 0; i < G.get(v).size(); i++)
            if (G.get(v).get(i).getCapacity() - G.get(v).get(i).getFlow() > 0)
                dist[v] = min(dist[v], dist[G.get(v).get(i).getTo()] + 1);
        count[dist[v]]++;
        enqueue(v);
    }

    private void discharge(int v) {
        for (int i = 0; excess[v] > 0 && i < G.get(v).size(); i++)
            push(G.get(v).get(i));

        if (excess[v] > 0) {
            if (count[dist[v]] == 1)
                gap(dist[v]);
            else
                relabel(v);
        }
    }

    public int getSize() {
        return N;
    }

    public void addEdge(int from, int to, int cap) {
        G.get(from).add(new Edge(from, to, cap, 0, G.get(to).size()));

        if (from == to) {
            ArrayList<Edge> fromNode = G.get(from);
            fromNode.get(fromNode.size() - 1).changeIndex(1);
        }

        G.get(to).add(new Edge(to, from, 0, 0, G.get(from).size() - 1));
    }

    public long computeMaxFlow(int s, int t) {
        count[0] = N - 1;
        count[N] = 1;
        dist[s] = N;
        active[s] = active[t] = true;
        for (int i = 0; i < G.get(s).size(); i++) {
            excess[s] += G.get(s).get(i).getCapacity();
            push(G.get(s).get(i));
        }

        while (!Q.isEmpty()) {
            int v = Q.peek();
            Q.remove();
            active[v] = false;
            discharge(v);
        }

        long totflow = 0;
        for (int i = 0; i < G.get(s).size(); i++)
            totflow += G.get(s).get(i).getFlow();

        return totflow;
    }
}
