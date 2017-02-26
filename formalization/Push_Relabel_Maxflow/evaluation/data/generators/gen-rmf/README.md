RMFGEN Network Generator
========================

This generator produces the RMFGEN networks developed by Goldfarb and Grigoriadis. It 
was submitted by Tamas Badics to [DIMACS maximum flow problems](ftp://dimacs.rutgers.edu/pub/netflow/generators/network/)

> This generator produces the RMFGEN networks developed by 
> Goldfarb and Grigoriadis (see ``A computational comparison of the Dinic
> and Network Simplex methods for maximum flow,'' Annals of Operations 
> Research 13 (1988), pp 83--123. 

Without providing an outut path, this prgoram prints the generated network into the standard output. Usage:

```
EXECUTABLE [-out out_file]
       -a frame_size -b depth
       -c1 cap_range1 -c2 cap_range2

	The generated network is as follows:
		It has b pieces of frames of size (a x a).
		(So alltogether the number of vertices is a*a*b)
			
		In each frame all the vertices are connected with 
		their neighbours. (forth and back)
		In addition the vertices of a frame are connected
		one to one with the vertices of next frame using 
		a random permutation of those vertices.

		The source is the lower left vertex of the first frame,
		the sink is the upper right vertex of the b'th frame. 
               
		The capacities are randomly chosen integers
		from the range of (c1, c2) in the case of 
        interconnecting edges, and c2 * a * a for 
        the in-frame edges.
```



