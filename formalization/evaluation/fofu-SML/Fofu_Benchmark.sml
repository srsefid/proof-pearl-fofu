open Fofu

structure Profile = MLton.Profile

val profData = Profile.Data.malloc ()


fun readList (infile : string) = let
  val ins = TextIO.openIn infile
  fun loop ins =
   case TextIO.inputLine ins of
      NONE      => []
    | SOME line => line :: loop ins
in
  let 
    val lines = (loop ins before TextIO.closeIn ins)
    
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
  in
    line_parse (tl lines)
  end
end


exception FAILED

fun 
  the_fail NONE msg = (print (msg ^ "\n"); raise FAILED)
| the_fail (SOME x) msg = x



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
      val _ = print (IntInf.toString n)
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
  fun measure n { prepare, run, compres } = let
    val _ = print ("Netcheck ...");
    val G = prepare ()  
    val G = the_fail G "Failed"
    val _ = print ("Done\n");
    
    val _ = print ("Fofu ");
    val (t,res) = iterate n Time.zeroTime (run G)
    val t = Time.fromNanoseconds (Time.toNanoseconds t div n)
    val res = compres res
    val _ = print ("\n");
    val _ = print ("Result: " ^ res ^ "\n");
    val _ = print ("@@@ Execution time: " ^ IntInf.toString (Time.toMilliseconds t) ^ "ms\n")
    
  in () end

end


fun fofu_fun s t G = let
  val s = nat_of_integer s
  val t = nat_of_integer t
in
  {
    prepare = fn () => prepareNet G s t,
    run = fn (c,(ps,N)) => fn () => (N,c,edka_imp c s t N ps ()),
    compres = fn (N,c,f) => let
        val flow = get_flow c N s f ()
      in
        IntInf.toString (integer_of_int flow) 
      end  
  }
end



fun main () = let
  val args = CommandLine.arguments ();
in 
  case args of 
    [s,t,gname] => 
      let
        val s = the (Int.fromString s)
        val t = the (Int.fromString t)
        val G = readList gname
      in  
        measure 1 (fofu_fun s t G);
        print ("stat_outer_c = " ^ IntInf.toString (!stat.outer_c) ^ "\n");
        print ("stat_inner_c = " ^ IntInf.toString (!stat.inner_c) ^ "\n");
        Profile.Data.write(profData,"mlmon.prof.out");
        Profile.Data.free(profData)
      end
    | _ => print "Usage: Fofu <s> <t> <file-name>\n"
end

val _ = if MLton.isMLton then main() else ()




