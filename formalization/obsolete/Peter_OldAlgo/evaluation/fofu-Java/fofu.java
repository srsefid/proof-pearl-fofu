import lib.FlowNetwork;
import lib.FordFulkerson;

public class fofu {
    // test client that reads input network, solves max flow, and prints results
    public static void main(String[] args) throws Exception {
    	if (args.length == 0) {
    		System.out.println("Usage: <GRAPH-PATH>");
    	}
    	else {
	        FlowNetwork G = new FlowNetwork(args[0]);
	        int V_size = G.V();
	        int E_size = G.E();
	
	        if (V_size > 0 && V_size <= 10000) {
            // Warm up
	          new FordFulkerson(G, 0, V_size - 1);
	          
	          G = new FlowNetwork(args[0]);
	        
	        	long startTime = System.currentTimeMillis();
	        	
	        	FordFulkerson maxflow = new FordFulkerson(G, 0, V_size - 1);
	        
	        	long endTime   = System.currentTimeMillis();
	        
	        	System.out.format("@@@ Execution Time: %d milliseconds\n", endTime - startTime);
	        	System.out.format("\t[Input (V E): %d %d]\n", V_size, E_size);
	        	System.out.format("\t=> Maximum flow value: %d\n", (int)maxflow.value());
	        	System.out.format("\touter_c: %d\n\tinner_c: %d\n", maxflow.outer_c, maxflow.inner_c);
	        }
	        else {
	        	System.out.println("Input Graph is invalid");	        	
	        }
    	}
    }

}
