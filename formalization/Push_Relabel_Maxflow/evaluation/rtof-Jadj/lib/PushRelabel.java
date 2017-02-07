package lib;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.Queue;

import static java.lang.Integer.max;
import static java.lang.Long.min;
import static java.lang.Integer.min;

public class PushRelabel {
    private int N;
    private int[][] G;
    private long[] excess;
    private boolean[] active;
    private int[] dist, count;
    private Queue<Integer> Q;

    public PushRelabel(int size) {
        this.N = size;

        this.G = new int[size][size];
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

    private void push(int from, int to) {
        int amt = (int) (min(excess[from], G[from][to]));

        if (dist[from] <= dist[to] || amt == 0)
            return;

        G[from][to] -= amt;
        G[to][from] += amt;

        excess[to] += amt;
        excess[from] -= amt;

        enqueue(to);
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

       for (int i = 0; i < N; i++)
           if (G[v][i] > 0)
               dist[v] = min(dist[v], dist[i] + 1);

        count[dist[v]]++;
        enqueue(v);
    }

    private void discharge(int v) {
        for (int i = 0; excess[v] > 0 && i < N; i++)
            push(v, i);

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
        G[from][to] = cap;
    }

    public long computeMaxFlow(int s, int t) {
        count[0] = N - 1;
        count[N] = 1;
        dist[s] = N;
        active[s] = active[t] = true;

        for (int i = 0; i < N; i++) {
            excess[s] += G[s][i];
            push(s, i);
        }

        while (!Q.isEmpty()) {
            int v = Q.peek();
            Q.remove();
            active[v] = false;
            discharge(v);
        }

        long totflow = 0;
        for (int i = 0; i < N; i++)
            totflow += G[i][s];

        return totflow;
    }
}
