/* Executor of MF code (for Push-Relabel) */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <values.h>
#include <time.h>

/* statistic variables */
long n_push  = 0;         /* number of pushes */
long n_rel   = 0;         /* number of relabels */
long n_up    = 0;         /* number of updates */
long n_gap   = 0;         /* number of gaps */
long n_gnode = 0;         /* number of nodes after gap */  
float t, t2;

/* definitions of types: node & arc */

#include "types_qpr.h"

/* parser for getting extended DIMACS format input and transforming the
   data to the internal representation */

#include "parser_fl.c"

/* function for constructing maximal flow */

#include "q_prf.c"

int main ( argc, argv )

int   argc;
char *argv[];

{

arc *arp, *a;
long *cap;
node *ndp, *source, *sink, *i;
long n, m, nmin; 
long ni, na;
double flow = 0;
int  cc, prt;
if (argc < 2) {
		printf("Usage: <GRAPH-PATH>\n");
}
else {
  
#define N_NODE( i ) ( (i) - ndp + nmin )
#define N_ARC( a )  ( ( a == NULL )? -1 : (a) - arp )

parse( argv[1], &n, &m, &ndp, &arp, &cap, &source, &sink, &nmin );

clock_t start = clock(), diff;
cc = prflow ( n, ndp, arp, cap, source, sink, &flow );
diff = clock() - start;

printf("@@@time: %.0f ms\n", ((double)(diff)/CLOCKS_PER_SEC) * 1000);
printf("@@@max-flow: %ld\n", (long)flow);

//    printf (">>> pushes:      %10ld\n", n_push);
//    printf (">>> relabels:    %10ld\n", n_rel);
//    printf (">>> updates:     %10ld\n", n_up);
//    printf (">>> gaps:        %10ld\n", n_gap);
//    printf (">>> gap nodes:   %10ld\n", n_gnode);


}

  return 0;
}
