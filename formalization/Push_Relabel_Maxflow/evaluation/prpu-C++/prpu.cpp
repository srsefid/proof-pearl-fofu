/*
  Based on
  https://github.com/vujazzman/icpc/blob/master/notebook/PushRelable.cpp
*/
#include "time.h"
#include "stdio.h"
#include <cstring>
#include <cmath>
#include <vector>
#include <queue>
#include <iostream>
#include <fstream>

using namespace std;

typedef long LL;

struct Edge {
  int from, to, cap, flow, index;
  Edge(int from, int to, int cap, int flow, int index) :
    from(from), to(to), cap(cap), flow(flow), index(index) {}
};

struct PushRelabel {
  int N;
  vector<Edge>*  G;
  LL* excess;
  int *dist, *count;
  bool * active;
  queue<int> Q;

  PushRelabel(int N) : N(N) {
    this->G = new vector<Edge>[N];
    for(int i = 0; i < N; i++)
      G[i].reserve(10);

    this->excess = new LL[N];
    this->dist = new int[N];
    this->active = new bool[N];
    this->count = new int[2 * N];
  }

  void AddEdge(int from, int to, int cap) {
    G[from].push_back(Edge(from, to, cap, 0, G[to].size()));
    if (from == to) G[from].back().index++;
    G[to].push_back(Edge(to, from, 0, 0, G[from].size() - 1));
  }

  void Enqueue(int v) { 
    if (!active[v] && excess[v] > 0) { active[v] = true; Q.push(v); } 
  }

  void Push(Edge &e) {
    int amt = int(min(excess[e.from], LL(e.cap - e.flow)));
    if (dist[e.from] <= dist[e.to] || amt == 0) return;
    e.flow += amt;
    G[e.to][e.index].flow -= amt;
    excess[e.to] += amt;    
    excess[e.from] -= amt;
    Enqueue(e.to);
  }
  
  void Gap(int k) {
    for (int v = 0; v < N; v++) {
      if (dist[v] < k) continue;
      count[dist[v]]--;
      dist[v] = max(dist[v], N+1);
      count[dist[v]]++;
      Enqueue(v);
    }
  }

  void Relabel(int v) {
    count[dist[v]]--;
    dist[v] = 2*N;
    for (int i = 0; i < G[v].size(); i++) 
      if (G[v][i].cap - G[v][i].flow > 0)
        dist[v] = min(dist[v], dist[G[v][i].to] + 1);
    count[dist[v]]++;
    Enqueue(v);
  }

  void Discharge(int v) {
    for (int i = 0; excess[v] > 0 && i < G[v].size(); i++) Push(G[v][i]);
    if (excess[v] > 0) {
      if (count[dist[v]] == 1) 
        Gap(dist[v]); 
      else
        Relabel(v);
    }
  }

  LL GetMaxFlow(int s, int t) {
    count[0] = N-1;
    count[N] = 1;
    dist[s] = N;
    active[s] = active[t] = true;
    for (int i = 0; i < G[s].size(); i++) {
      excess[s] += G[s][i].cap;
      Push(G[s][i]);
    }
    
    while (!Q.empty()) {
      int v = Q.front();
      Q.pop();
      active[v] = false;
      Discharge(v);
    }
    
    LL totflow = 0;
    for (int i = 0; i < G[s].size(); i++) totflow += G[s][i].flow;
    return totflow;
  }
};


int main(int argc, char** argv) {
	if (argc < 2) {
		cout << "Usage: <GRAPH-PATH>\n";
	}
	else {
		ifstream fi(argv[1]);
		int V_size, E_size;
		fi >> V_size >> E_size;

    PushRelabel pr(V_size);

		for (int i = 0; i < E_size; i++) {
			int from, to, capacity;
			fi >> from >> to >> capacity;

      pr.AddEdge(from, to, capacity);
		}

		clock_t tStart = clock();
		LL maxFlow = pr.GetMaxFlow(0, V_size -1);

		printf("@@@time: %.0f ms\n", ((double)(clock() - tStart)/CLOCKS_PER_SEC) * 1000);
		printf("[Input (V E): %d %d]\n", V_size, E_size);
		printf("@@@max-flow: %ld\n", maxFlow);
	}

	return 0;
}
