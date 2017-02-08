import lib.*;

import java.io.FileNotFoundException;
import java.io.FileReader;
import java.util.Scanner;

public class rtof {
    private static PushRelabel initializePR(String path) throws FileNotFoundException {
        Scanner in = new Scanner(new FileReader(path));
        int nodeCount = in.nextInt();
        int edgeCount = in.nextInt();

        PushRelabel prob = new PushRelabel(nodeCount);


        for(int i = 0; i < edgeCount; i++) {
            int u = in.nextInt();
            int v = in.nextInt();
            int c = in.nextInt();

            prob.addEdge(u, v, c);
        }

        return prob;
    }

    private static MaxFlowResult doTest(PushRelabel G) {
        int V_size = G.getSize();

        System.gc();

        long startTime = System.currentTimeMillis();
        long maxflow = G.computeMaxFlow(0, V_size - 1);
        long endTime  = System.currentTimeMillis();

        CounterPR stat = G.getCounter();

        return new MaxFlowResult(endTime - startTime, maxflow, stat.getDischargeCount(), stat.getPushCount(), stat.getRelabelCount());
    }

    // test client that reads input network, solves max flow, and prints results
    public static void main(String[] args) throws Exception {
        if (args.length > 2 || args.length < 1) {
            System.out.println("Usage: [<WARMUP-PATH>] <GRAPH-PATH>");
        }
        else {
            int i=0;

            if (args.length == 2) {
                // warm up
                PushRelabel G = initializePR(args[i]);
                doTest(G);
                doTest(G);
                doTest(G);
                doTest(G);
                i++;
            }

            PushRelabel G = initializePR(args[i]);
            MaxFlowResult result = doTest(G);
            System.out.format("@@@time: %d ms\n", result.getTime());
            System.out.format("@@@max-flow: %d\n", result.getFlowValue());

            System.out.format(">>>disc: %d\n", result.getDischargeCount());
            System.out.format(">>>push: %d\n", result.getPushCount());
            System.out.format(">>>rlbl: %d\n", result.getRelabelCount());

        }
    }
}
