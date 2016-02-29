#include "stdbool.h"
#include "string.h"
#include "time.h"
#include "stdio.h"
#include "stdlib.h"

/* This function creates a square matrix to store our graph,
 * It also initializes all the capacities to zero */
int** graph_init (int size) {
	int** graph = malloc(size * sizeof(int*));

	int i;
	for (i = 0; i < size; i++)
		graph[i] = calloc(size, sizeof(int));

	return graph;
}

/* As our matrix is a int** we have to clean it up in a loop */
void graph_free (int** graph, int size) {
	int i;
	for (i = 0; i < size; i++)
		free(graph[i]);

	free(graph);
}

/* After execution the "visited" array shows all those edges which where reached
 * during the dfs execution on "graph". Note that the "reverse" flag indicates
 * if we have to use the original graph or its reverse. We use this function to
 * computing the set of nodes that are reachable from source, and the set of no-
 * des that are reaching sink. */
void dfs (int** graph, bool* visited, int start, int size, bool reverse) {
	visited[start] = true;

	int i;
	for (i = 0; i < size; i++) {
		int edge_cap = (!reverse) ? graph[start][i] : graph[i][start];

		if (edge_cap != 0 && !visited[i])
			dfs(graph, visited, i, size, reverse);
	}
}

/* This function produces a random network which has no self loops. Also, there
 * will be no parallel edges in the output network.*/
void net_init (int** graph, int size, int try_count, int max_capacity) {
	srand(time(NULL));

	/* We assume the source is in index 0, and sink is in index size - 1. We put
	 * random edges between any vertex except these two. and we connect them later */
	int i;
	for (i = 0; i < try_count; i++) {
		int u = 1 + (rand() % (size - 2));
		int v = 1 + (rand() % (size - 2));
		int c = 1 + (rand() % max_capacity);

		if (u != v && graph[v][u] == 0)
			graph[u][v] = c;
	}

	/* compute the number of vertices that are connected to source and sink, we
	 *	have assumed this number is at most half of the size of  the vertex set */
	int sout_count = 1 + (rand() % (size / 2));
	int tin_count = 1 + (rand() % (size / 2));

	// onnecting source to some of the vertices
	for (i = 0; i < sout_count; i++) {
		int u = 1 + (rand() % (size - 2));
		int c = 1 + (rand() % max_capacity);

		graph[0][u] = c;
	}

	// conncting some of the vertices to sink
	for (i = 0; i < tin_count; i++) {
		int u = 1 + (rand() % (size - 2));
		int c = 1 + (rand() % max_capacity);

		graph[u][size - 1] = c;
	}
}

/* This function removes all those vertices that are not contained
 * in any path connecting the source to the sink. acc_nodes is the
 * vector which represents all the acceptable nodes */
void net_clean (int** graph, int size, bool* acc_nodes) {
	bool* s_reachable = calloc(size, sizeof(bool));
	bool* t_reaching = calloc(size, sizeof(bool));

	dfs(graph, s_reachable, 0, size, false);
	dfs(graph, t_reaching, size - 1, size, true);

	int i = 0;
	for (i = 0; i < size; i++)
		acc_nodes[i] = s_reachable[i] && t_reaching[i];

	free(t_reaching);
	free(s_reachable);
}

int main (int argc, char** argv) {
	if (argc < 2) {
		printf("Usage: <V_SIZE>\n");
	}
	else {
		int v_count = atoi(argv[1]);

		if (v_count > 0) {
			int e_tries = v_count * (v_count / 5);
			int max_c = v_count;

			char buffer[20];
			sprintf(buffer,"%d",v_count);

			int** G = graph_init(v_count);
			bool* acc_nodes = calloc(v_count, sizeof(bool));
			int* index_chg = calloc(v_count, sizeof(int));

			net_init(G, v_count, e_tries, max_c);
			net_clean(G, v_count, acc_nodes);

			/* For every node i we compute the count of vertices that have an
			 * index lower than i, and they are removed from the graph. */
			int i, j;
			for (i = 0; i < v_count; i++) {
				for (j = 0; j < i; j++) {
					if (!acc_nodes[j])
						index_chg[i]++;
				}
			}

			/* We count total number of edges. This loop can be used for printing*/
			int edge_count = 0;
			for (i = 0; i < v_count; i++) {
				if (acc_nodes[i]) {
					for (j = 0; j < v_count; j++) {
						if (acc_nodes[j]) {
							if (G[i][j] != 0)
								edge_count++;

							//printf("%d", G[i][j]);
						}

						//printf(" ");
					}
				}

				//printf("\n");
			}

			char* out_path = malloc(strlen(buffer) + 6);
			strcpy(out_path, "g-");
			strcat(out_path, buffer);
			strcat(out_path, ".txt");

			FILE* fw = fopen(out_path, "w");
			fprintf(fw, "%d %d\n", v_count - index_chg[v_count - 1], edge_count);
			for (i = 0; i < v_count; i++) {
				if (acc_nodes[i]) {
					for (j = 0; j < v_count; j++) {
						if (acc_nodes[j] && G[i][j] != 0)
							fprintf(fw, "%d %d %d\n", i - index_chg[i], j - index_chg[j], G[i][j]);
					}
				}
			}

			fclose(fw);

			free(index_chg);
			free(acc_nodes);
			graph_free(G, v_count);

			printf("Successfully generated a graph with %d nodes.\n", v_count);
		}
		else {
			printf("Number of vertices must be a value greater that zero.\n");
		}
	}

	return 0;
}

