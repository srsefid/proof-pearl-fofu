*** Obsolete ***
theory Temporary_Graph_Add
imports Misc Graph
begin

  (* Graph: Paths *)  
  context Graph 
  begin

  end
  

  (* Graph: Distance and shortest Path *)  
  context Graph
  begin


    subsubsection \<open>Shortest Paths\<close>

    (*definition isShortestPath :: "node \<Rightarrow> path \<Rightarrow> node \<Rightarrow> bool" 
      -- \<open>A shortest path between two nodes\<close> (* TODO: Rename: isShortestPath *)
      where  
      "isShortestPath u p v \<equiv> isPath u p v \<and> (\<forall>p'. isPath u p' v \<longrightarrow> length p \<le> length p')"
    *)  



  end    


end
