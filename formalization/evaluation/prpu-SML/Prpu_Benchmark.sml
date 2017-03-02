open Prpu

structure Profile = MLton.Profile

val profData = Profile.Data.malloc ()

exception FAILED

fun fail msg = (print (msg ^ "\n"); raise FAILED)

fun 
  the_fail NONE msg = fail msg
| the_fail (SOME x) msg = x

val int_of_gi = IntInf.toInt o integer_of_int
val gi_of_int = Int_of_integer o IntInf.fromInt
val int_of_gn = IntInf.toInt o integer_of_nat
val gn_of_int = nat_of_integer o IntInf.fromInt


fun readList (infile : string) = let
  val ins = TextIO.openIn infile
  fun loop ins =
   case TextIO.inputLine ins of
      NONE      => []
    | SOME line => line :: loop ins
in
  let 
    fun parse_integer s = case Int.fromString s of
      SOME i => i
    | NONE => fail ("Expected integer, but got '" ^ s ^"'")  

    val parse_int = gi_of_int o parse_integer
    val parse_nat = gn_of_int o parse_integer

    val tokenize = String.tokens (fn c => c = #" ")
    
    fun parse_edge s = let
      val l = tokenize s
    in
      case l of 
        [u,v,c] => (parse_nat u, (parse_nat v, parse_int c))
      | _ => fail ("Expected edge in format 'u v c', but got " ^ s)
    end
    
    fun parse_counts s = let 
      val l = tokenize s
    in
      case l of 
        [numV,numE] => (parse_integer numV, parse_integer numE)
      | _ => fail ("Expected counts in format 'numV numE', but got " ^ s)
    end    


    fun parse_graph (counts :: edges) = (parse_counts counts, map parse_edge edges)
      | parse_graph _ = fail "Empty graph file"
    

    val lines = (loop ins before TextIO.closeIn ins)
    val ((numV,numE),edges) = parse_graph lines
    
    
    (*  
    fun rem_opt i = 
    case i of
      NONE   => nat_of_integer (0)
    | SOME x => nat_of_integer (x) 

    fun rem_opti i = 
    case i of
      NONE   => Int_of_integer (0)
    | SOME x => Int_of_integer (x) 
    
    fun line_parse lines = 
     case lines of
        []        => []
      | (l :: ls) => let val toks = ((String.tokens (fn c => c = #" ")) l)
        in
          (rem_opt (Int.fromString(hd toks)),
           (rem_opt (Int.fromString(hd (tl toks))),
           rem_opti (Int.fromString(hd (tl (tl toks)))))) :: line_parse ls 
        end 
    *)      
  in
    (numV,edges)
  end
end





fun the (SOME x) = x

local        
  fun measure f = let
    val _ = MLton.GC.collect ();
    val _ = MLton.GC.unpack ();   
    val ts = Time.now ()
    val raw_res = Profile.withData (profData,f)
    val ts = Time.- (Time.now (), ts) 
  in (ts,raw_res) end  

  fun iterate n t f = let
      val _ = print (Int.toString n)
      val (ts, raw_res) = measure f
      val t = Time.+ (t,ts)
      val _ = print ("(" ^ Time.toString ts ^ "s). ")
    in 
      if n>1 then 
        iterate (n-1) t f
      else  
        (t,raw_res)
    end
  
in  
  fun measure n { prepare, run , compres } = let
    val _ = print ("Netcheck ...");
    val G = prepare ()  
    val G = the_fail G "Failed"
    val _ = print ("Done\n");
    
    val _ = print ("Fifo");
    val (t,res) = iterate n Time.zeroTime (run G)
    val t = Time.fromNanoseconds (Time.toNanoseconds t div (IntInf.fromInt n))
    val res = compres res
    val _ = print ("\n");
    val _ = print ("@@@time: " ^ IntInf.toString (Time.toMilliseconds t) ^ " ms\n");
    val _ = print ("@@@max-flow: " ^ res ^ "\n")
  in () end

end


fun fifo_fun s t G = let
  val s = gn_of_int s
  val t = gn_of_int t
in
  {
    prepare = fn () => let 
      val pr = the_fail (fifo_push_relabel_prepare_impl G s t ()) "prepareNet failed"
    in
      SOME pr
    end  ,

    run = fn (N,(am,(c,cf))) => fn () => (N,c,am,fifo_push_relabel_run_impl s t N am cf ()),
    compres = fn (N,c,am,cf) => let
        val flow = compute_flow_val_impl c s N am cf ()
      in
        Int.toString (int_of_gi flow) 
      end
  }
end



fun main () = let
  val args = CommandLine.arguments ();
  
  fun perform s t G = (
    measure 1 (fifo_fun s t G);
    print ("stat_push_c = " ^ Int.toString (!stat.push_c) ^ "\n");
    print ("stat_relabel_c = " ^ Int.toString (!stat.relabel_c) ^ "\n");
    print ("stat_gap_c = " ^ Int.toString (!stat.gap_c) ^ "\n");
    Profile.Data.write(profData,"mlmon.prof.out");
    Profile.Data.free(profData)
  )
  
in 
  case args of 
    [s,t,gname] => let
      val s = the (Int.fromString s)
      val t = the (Int.fromString t)
      val (_,G) = readList gname
    in  
      perform s t G
    end
  | [gname] => let
      val (N,G) = readList gname
      val s = 0
      val t = N - 1
    in    
      perform s t G
    end
    | _ => print "Usage: Fifo [<s> <t>] <file-name>\n  If s and t not specified, nodes 0 and |V|-1 are taken."
end

val _ = if MLton.isMLton then main() else ()
