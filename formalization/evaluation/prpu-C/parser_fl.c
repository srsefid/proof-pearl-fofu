#include "stdio.h"

/*
  parse (...) :
       1. Reads maximal flow problem in extended DIMACS format.
       2. Prepares internal data representation.
       
   types: 'arc' and 'node' must be predefined

   type arc  must contain fields 'head', 'sister', 'next', 'r_cap'

   typedef 
     struct arc_st
       {
         long             r_cap;     .. residual capasity
         struct node_st   *head;     .. head node 
         struct arc_st    *sister;   .. opposite arc 
         struct arc_st    *next;     .. next arc with the same tail 
         ..................
       }
   arc;

   type   node   must contain the field 'first': 

   typedef
     struct node_st
       {
          arc_st        *first;    ..  first outgoing arc 
          ....................
       }
    node;
*/

/* ----------------------------------------------------------------- */

int parse( path, n_ad, m_ad, nodes_ad, arcs_ad, cap_ad,
           source_ad, sink_ad, node_min_ad )

/* all parameters are output */
char    *path;                  /* address of the file to read data */
long    *n_ad;                 /* address of the number of nodes */
long    *m_ad;                 /* address of the number of arcs */
node    **nodes_ad;            /* address of the array of nodes */
arc     **arcs_ad;             /* address of the array of arcs */
long    **cap_ad;              /* address of the array of capasities */
node    **source_ad;           /* address of the pointer to the source */
node    **sink_ad;             /* address of the pointer to the source */
long    *node_min_ad;          /* address of the minimal node */

{

#define MAXLINE       100	/* max line length in the input file */
#define ARC_FIELDS      3	/* no of fields in arc line  */
#define NODE_FIELDS     2	/* no of fields in node line  */
#define P_FIELDS        3       /* no of fields in problem line */
#define PROBLEM_TYPE "max"      /* name of problem type*/


long    n,                      /* internal number of nodes */
        node_min,               /* minimal no of node  */
        node_max,               /* maximal no of nodes */
       *arc_first,              /* internal array for holding
                                     - node degree
                                     - position of the first outgoing arc */
       *arc_tail,               /* internal array: tails of the arcs */
        source,                 /* no of the source */
        sink,                   /* no of the sink */
        /* temporary variables carrying no of nodes */
        head, tail, i, source2;

long    m,                      /* internal number of arcs */
        /* temporary variables carrying no of arcs */
        last, arc_num, arc_new_num;

node    *nodes,                 /* pointer to the node structure */
        *head_p,
        *ndp;

arc     *arcs,                  /* pointer to the arc structure */
        *arc_current,
        *arc_new,
        *arc_tmp;

long    *acap,                  /* array of capasities */
        cap;                    /* capasity of the current arc */

long    no_lines=0,             /* no of current input line */
        no_plines=0,            /* no of problem-lines */
        no_nslines=0,           /* no of node-source-lines */
        no_nklines=0,           /* no of node-source-lines */
        no_alines=0,            /* no of arc-lines */
        pos_current=0;          /* 2*no_alines */

char    in_line[MAXLINE],       /* for reading input line */
        pr_type[3],             /* for reading type of the problem */
        nd;                     /* source (s) or sink (t) */

int     k,                      /* temporary */
        err_no;                 /* no of detected error */

char    *dummy;

/* -------------- error numbers & error messages ---------------- */
#define EN1   0
#define EN2   1
#define EN3   2
#define EN4   3
#define EN6   4
#define EN10  5
#define EN7   6
#define EN8   7
#define EN9   8
#define EN11  9
#define EN12 10
#define EN13 11
#define EN14 12
#define EN16 13
#define EN15 14
#define EN17 15
#define EN18 16
#define EN21 17
#define EN19 18
#define EN20 19
#define EN22 20

static char *err_message[] = 
  { 
/* 0*/    "more than one problem line.",
/* 1*/    "wrong number of parameters in the problem line.",
/* 2*/    "it is not a Max Flow problem line.",
/* 3*/    "bad value of a parameter in the problem line.",
/* 4*/    "can't obtain enough memory to solve this problem.",
/* 5*/    "more than one line with the problem name.",
/* 6*/    "can't read problem name.",
/* 7*/    "problem description must be before node description.",
/* 8*/    "this parser doesn't support multiply sources and sinks.",
/* 9*/    "wrong number of parameters in the node line.",
/*10*/    "wrong value of parameters in the node line.",
/*11*/    " ",
/*12*/    "source and sink descriptions must be before arc descriptions.",
/*13*/    "too many arcs in the input.",
/*14*/    "wrong number of parameters in the arc line.",
/*15*/    "wrong value of parameters in the arc line.",
/*16*/    "unknown line type in the input.",
/*17*/    "reading error.",
/*18*/    "not enough arcs in the input.",
/*19*/    "source or sink doesn't have incident arcs.",
/*20*/    "can't read anything from the input file."
  };
/* --------------------------------------------------------------- */

/* The main loop:
        -  reads the line of the input,
        -  analises its type,
        -  checks correctness of parameters,
        -  puts data to the arrays,
        -  does service functions
*/

FILE *fo = fopen(path, "r");
dummy = fgets(in_line, MAXLINE, fo);

sscanf(in_line, "%ld %ld", &n, &m);

nodes = (node*) calloc ( n+2, sizeof(node) );
arcs = (arc*)  calloc ( 2*m+1, sizeof(arc) );
arc_tail = (long*) calloc ( 2*m,   sizeof(long) ); 
arc_first = (long*) calloc ( n+2, sizeof(long) );
acap = (long*) calloc ( 2*m, sizeof(long) );

arc_current = arcs;

source = 1;
sink = n;
node_max = 0;
node_min = 2 * n;

for(k = 0; k < m; k++) {
  dummy = fgets(in_line, MAXLINE, fo);
  sscanf (in_line,"%ld %ld %ld", &tail, &head, &cap);

  //our inputs are indexed from zero, so change their index by 1
  tail++;
  head++;

	arc_first[tail + 1] ++; 
	arc_first[head + 1] ++;

	arc_tail[pos_current] = tail;
	arc_tail[pos_current+1] = head;
	arc_current -> head  = nodes + head;
	arc_current -> r_cap = cap;
	arc_current -> sister = arc_current + 1;
  ( arc_current + 1 ) -> head = nodes + tail;
  ( arc_current + 1 ) -> r_cap = 0;
  ( arc_current + 1 ) -> sister = arc_current;

  if ( head < node_min ) node_min = head;
  if ( tail < node_min ) node_min = tail;
  if ( head > node_max ) node_max = head;
  if ( tail > node_max ) node_max = tail;

	no_alines++;
	arc_current += 2;
	pos_current += 2;
}
 

fclose(fo);

/********** ordering arcs - linear time algorithm ***********/

/* first arc from the first node */
( nodes + node_min ) -> first = arcs;

/* before below loop arc_first[i+1] is the number of arcs outgoing from i;
   after this loop arc_first[i] is the position of the first 
   outgoing from node i arcs after they would be ordered;
   this value is transformed to pointer and written to node.first[i]
   */
 
for ( i = node_min + 1; i <= node_max + 1; i ++ ) 
  {
    arc_first[i]          += arc_first[i-1];
    ( nodes + i ) -> first = arcs + arc_first[i];
  }


for ( i = node_min; i < node_max; i ++ ) /* scanning all the nodes  
                                            exept the last*/
  {

    last = ( ( nodes + i + 1 ) -> first ) - arcs;
                             /* arcs outgoing from i must be cited    
                              from position arc_first[i] to the position
                              equal to initial value of arc_first[i+1]-1  */

    for ( arc_num = arc_first[i]; arc_num < last; arc_num ++ )
      { tail = arc_tail[arc_num];

	while ( tail != i )
          /* the arc no  arc_num  is not in place because arc cited here
             must go out from i;
             we'll put it to its place and continue this process
             until an arc in this position would go out from i */

	  { arc_new_num  = arc_first[tail];
	    arc_current  = arcs + arc_num;
	    arc_new      = arcs + arc_new_num;
	    
	    /* arc_current must be cited in the position arc_new    
	       swapping these arcs:                                 */

	    head_p               = arc_new -> head;
	    arc_new -> head      = arc_current -> head;
	    arc_current -> head  = head_p;

	    cap                 = arc_new -> r_cap;
	    arc_new -> r_cap     = arc_current -> r_cap;
	    arc_current -> r_cap = cap;

	    if ( arc_new != arc_current -> sister )
	      {
	        arc_tmp                = arc_new -> sister;
	        arc_new  -> sister     = arc_current -> sister;
	        arc_current -> sister  = arc_tmp;

                ( arc_current -> sister ) -> sister = arc_current;
		( arc_new     -> sister ) -> sister = arc_new;
	      }

	    arc_tail[arc_num] = arc_tail[arc_new_num];
	    arc_tail[arc_new_num] = tail;

	    /* we increase arc_first[tail]  */
	    arc_first[tail] ++ ;

            tail = arc_tail[arc_num];
	  }
      }
    /* all arcs outgoing from  i  are in place */
  }       
/* -----------------------  arcs are ordered  ------------------------- */

/*----------- constructing lists ---------------*/


  for ( ndp = nodes + node_min; ndp <= nodes + node_max;  ndp ++ )
      ndp -> first = (arc*) NULL;

  for ( arc_current = arcs + (2*m-1); arc_current >= arcs; arc_current -- )
    {
      arc_num = arc_current - arcs;
      tail = arc_tail [arc_num];
      ndp = nodes + tail;
      arc_current -> next = ndp -> first;
      ndp -> first = arc_current;
    }


/* ----------- assigning output values ------------*/
*m_ad = m;
*n_ad = node_max - node_min + 1;
*source_ad = nodes + source;
*sink_ad   = nodes + sink;
*node_min_ad = node_min;
*nodes_ad = nodes + node_min;
*arcs_ad = arcs;
*cap_ad = acap;

for ( arc_current = arcs, arc_num = 0; 
      arc_num < 2*m;
      arc_current ++, arc_num ++
    )
     acap [ arc_num ] = arc_current -> r_cap; 


/* free internal memory */
free ( arc_first ); free ( arc_tail );

/* Thanks God! all is done */
return (0);
}
/* --------------------   end of parser  -------------------*/
