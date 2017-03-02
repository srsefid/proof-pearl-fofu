#include "stdbool.h"
#include "string.h"
#include "time.h"
#include "stdio.h"
#include "stdlib.h"
#include "limits.h"

/* This function creates a square matrix to store our graph,
 * then parses the DIMACS input until either EOF is entered
 * or total edges are read. We add the source at index 0 
 * and sink at index size - 1. Then we connect DIMACS s t
 * to these new srouce sink. (Compatible with cleanup) */
long** graph_init (long* v_count, long* e_count) {
	long** graph;
    
    char dummy;
    char dummies[10]; 
    long in_edges = -1;
    bool graph_init = false;
    bool read_complete = false;
    while(!read_complete){
        
        char* line;
        size_t len = 0;
        if(getline(&line, &len, stdin)!= -1) {
            char command = line[0];

            switch (command) {
                /* Each Dimacs file must have only one p line, and it must occure before everything else. 
                 * Hence, no requirement to check for recreation of the graph, or its existance in orther 
                   cases either. (i assume all inputs are correct...) */
                case 'p':
                    {
                        long vs, es;
                        sscanf(line, "%c %s %ld %ld", &dummy, dummies, &vs, &es);

                        /* index 0 and index *v_count - 1, are used for s an t. no matter what the input is */
                        *v_count = vs + 2;
                        *e_count = es + 2;

                        /* set the counter for the loop. When all edges are read (in_edges = 0), exit */
                        in_edges = es;

                        graph = malloc(*v_count * sizeof(long*));
                        
                        long i;
                        for (i = 0; i < *v_count; i++)
		                    graph[i] = calloc(*v_count, sizeof(long));
                    }
                    break;

                /* Read souce and sink nodes*/
                case 'n':
                    {
                        char ts;
                        long id;
                        sscanf(line, "%c %ld %c", &dummy, &id, &ts);

                        /* if it is s, connect our s (index 0) to it with infinit capacity 
                         * if it is t, connect out t (index *v_count - 1) to it with infinite capacity */
                        if(ts == 's')
                            graph[0][id] = INT_MAX;
                        else
                            graph[id][*v_count - 1] = INT_MAX;                                
                    }
                    break;

                /* Add next edge to the graph and decrease in_edge. (termination check...)*/
                case 'a':
                    {
                        long from, to, cap;
                        sscanf(line, "%c %ld %ld %ld", &dummy, &from, &to, &cap);

                        /* no self-loop or parallel edge otw. ignore (according to DIMACS spec. this should never happer) */
                        if (graph[to][from] == 0 && from != to)
                            graph[from][to] = cap;

                        in_edges--;
                        if (in_edges == 0)
                            read_complete = true;
                    }                    
                    break;

                /* Ignore comment lines, and any other lines that start with unknown symbols */    
                case 'c':
                default:
                    break;
            }

            free(line);
        }
        else {
            read_complete = true;
        }
    }
    
	return graph;
}

/* As our matrix is a long** we have to clean it up in a loop */
void graph_free (long** graph, long size) {
	long i;
	for (i = 0; i < size; i++)
		free(graph[i]);

	free(graph);
}

/* After execution the "visited" array shows all those edges which where reached
 * during the dfs execution on "graph". Note that the "reverse" flag indicates
 * if we have to use the original graph or its reverse. We use this function to
 * computing the set of nodes that are reachable from source, and the set of no-
 * des that are reaching sink. */
void dfs (long** graph, bool* visited, long start, long size, bool reverse) {
	visited[start] = true;

	long i;
	for (i = 0; i < size; i++) {
		long edge_cap = (!reverse) ? graph[start][i] : graph[i][start];

		if (edge_cap != 0 && !visited[i])
			dfs(graph, visited, i, size, reverse);
	}
}


/* This function removes all those vertices that are not contained
 * in any path connecting the source to the sink. acc_nodes is the
 * vector which represents all the acceptable nodes */
void net_clean (long** graph, long size, bool* acc_nodes) {
	bool* s_reachable = calloc(size, sizeof(bool));
	bool* t_reaching = calloc(size, sizeof(bool));

	dfs(graph, s_reachable, 0, size, false);
	dfs(graph, t_reaching, size - 1, size, true);

	long i = 0;
	for (i = 0; i < size; i++)
		acc_nodes[i] = s_reachable[i] && t_reaching[i];

	free(t_reaching);
	free(s_reachable);
}

int main (int argc, char** argv) {
	if (argc != 2) {
		printf("Usage: <output-path>\n");
		printf("\t use STD instead of <output-path> to print in console\n");
	}
	else {
        long v_count = 0;
        long e_count = 0;

        long** G = graph_init(&v_count, &e_count);
		bool* acc_nodes = calloc(v_count, sizeof(bool));
		long* index_chg = calloc(v_count, sizeof(long));

		net_clean(G, v_count, acc_nodes);

		/* For every node i we compute the count of vertices that have an
		 * index lower than i, and they are removed from the graph. */
		long i, j;
		for (i = 0; i < v_count; i++) {
			for (j = 0; j < i; j++) {
				if (!acc_nodes[j])
					index_chg[i]++;
			}
		}

		/* We count total number of edges. This loop can be used for printing*/
        long node_count = v_count - index_chg[v_count - 1];
		long edge_count = 0;
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

        /* if STD was not used as argument, then a path is given. use it for output */
        FILE* fw = stdout;
        if (strcmp(argv[1], "STD") != 0)
            fw = fopen(argv[1], "w");

        fprintf(fw, "%ld %ld\n", node_count, edge_count);
        for (i = 0; i < v_count; i++) {
            if (acc_nodes[i]) {
                for (j = 0; j < v_count; j++) {
                    if (acc_nodes[j] && G[i][j] != 0)
                        fprintf(fw, "%ld %ld %ld\n", i - index_chg[i], j - index_chg[j], G[i][j]);
                }
            }
        }

        fclose(fw);

        free(index_chg);
        free(acc_nodes);
        graph_free(G, v_count);

        double density = (double)edge_count / (node_count * (node_count - 1));
    
        printf("Generated* a graph with %ld nodes and %ld edges. Density is %.2lf\n", node_count, edge_count, density);
	}

	return 0;
}

