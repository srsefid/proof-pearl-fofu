open Util
module G = Graph.DirectedGraph

let time f x y z =
    let start = Sys.time() in
    let fx = f x y z in
    let stop = Sys.time() in
    let () = Printf.printf "@@@ Execution time: %.4f millisec\n"
        ((stop -. start) *. 1000.0) in
    fx;;

let read_file filename = 
let lines = ref [] in
let chan = open_in filename in
try
  while true; do
    lines := input_line chan :: !lines
  done; !lines
with End_of_file ->
  close_in chan;
  List.rev !lines ;;

let all_lines = read_file Sys.argv.(1);;
let v_e = Str.split (Str.regexp " ") (List.hd all_lines);;
let v = (int_of_string (List.hd v_e));;
let e = (int_of_string (List.nth v_e 1));;
let g = G.empty v;;
for i = 1 to e do 
    let edge = Str.split (Str.regexp " ") (List.nth all_lines i) in
	let a = int_of_string (List.hd edge) in
	let b = int_of_string (List.nth edge 1) in
	let c = int_of_string (List.nth edge 2) in
	G.add (a, b) c g
done;;

let max_flow = time Main.max_flow 0 (v - 1) g;;
Printf.printf "\t[Input (V E)]: %d %d\n" v e;;
Printf.printf "\t=> Maximum flow value: %d\n" max_flow;;
