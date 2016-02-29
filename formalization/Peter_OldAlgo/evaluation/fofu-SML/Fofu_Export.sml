
structure Uint : sig
  val set_bit : Word.word -> IntInf.int -> bool -> Word.word
  val shiftl : Word.word -> IntInf.int -> Word.word
  val shiftr : Word.word -> IntInf.int -> Word.word
  val shiftr_signed : Word.word -> IntInf.int -> Word.word
  val test_bit : Word.word -> IntInf.int -> bool
end = struct

fun set_bit x n b =
  let val mask = Word.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))
  in if b then Word.orb (x, mask)
     else Word.andb (x, Word.notb mask)
  end

fun shiftl x n =
  Word.<< (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr x n =
  Word.>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr_signed x n =
  Word.~>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun test_bit x n =
  Word.andb (x, Word.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))) <> Word.fromInt 0

end; (* struct Uint *)


      structure stat = struct
        val outer_c = ref 0;
        fun outer_c_incr () = (outer_c := !outer_c + 1; ())
        val inner_c = ref 0;
        fun inner_c_incr () = (inner_c := !inner_c + 1; ())
      end
      

(* Test that words can handle numbers between 0 and 31 *)
val _ = if 5 <= Word.wordSize then () else raise (Fail ("wordSize less than 5"));

structure Uint32 : sig
  val set_bit : Word32.word -> IntInf.int -> bool -> Word32.word
  val shiftl : Word32.word -> IntInf.int -> Word32.word
  val shiftr : Word32.word -> IntInf.int -> Word32.word
  val shiftr_signed : Word32.word -> IntInf.int -> Word32.word
  val test_bit : Word32.word -> IntInf.int -> bool
end = struct

fun set_bit x n b =
  let val mask = Word32.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))
  in if b then Word32.orb (x, mask)
     else Word32.andb (x, Word32.notb mask)
  end

fun shiftl x n =
  Word32.<< (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr x n =
  Word32.>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr_signed x n =
  Word32.~>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun test_bit x n =
  Word32.andb (x, Word32.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))) <> Word32.fromInt 0

end; (* struct Uint32 *)


structure STArray = struct

datatype 'a Cell = Invalid | Value of 'a array;

exception AccessedOldVersion;

type 'a array = 'a Cell Unsynchronized.ref;

fun fromList l = Unsynchronized.ref (Value (Array.fromList l));
fun array (size, v) = Unsynchronized.ref (Value (Array.array (size,v)));
fun tabulate (size, f) = Unsynchronized.ref (Value (Array.tabulate(size, f)));
fun sub (Unsynchronized.ref Invalid, idx) = raise AccessedOldVersion |
    sub (Unsynchronized.ref (Value a), idx) = Array.sub (a,idx);
fun update (aref,idx,v) =
  case aref of
    (Unsynchronized.ref Invalid) => raise AccessedOldVersion |
    (Unsynchronized.ref (Value a)) => (
      aref := Invalid;
      Array.update (a,idx,v);
      Unsynchronized.ref (Value a)
    );

fun length (Unsynchronized.ref Invalid) = raise AccessedOldVersion |
    length (Unsynchronized.ref (Value a)) = Array.length a

fun grow (aref, i, x) = case aref of 
  (Unsynchronized.ref Invalid) => raise AccessedOldVersion |
  (Unsynchronized.ref (Value a)) => (
    let val len=Array.length a;
        val na = Array.array (len+i,x) 
    in
      aref := Invalid;
      Array.copy {src=a, dst=na, di=0};
      Unsynchronized.ref (Value na)
    end
    );

fun shrink (aref, sz) = case aref of
  (Unsynchronized.ref Invalid) => raise AccessedOldVersion |
  (Unsynchronized.ref (Value a)) => (
    if sz > Array.length a then 
      raise Size
    else (
      aref:=Invalid;
      Unsynchronized.ref (Value (Array.tabulate (sz,fn i => Array.sub (a,i))))
    )
  );

structure IsabelleMapping = struct
type 'a ArrayType = 'a array;

fun new_array (a:'a) (n:int) = array (n, a);

fun array_length (a:'a ArrayType) = length a;

fun array_get (a:'a ArrayType) (i:int) = sub (a, i);

fun array_set (a:'a ArrayType) (i:int) (e:'a) = update (a, i, e);

fun array_of_list (xs:'a list) = fromList xs;

fun array_grow (a:'a ArrayType) (i:int) (x:'a) = grow (a, i, x);

fun array_shrink (a:'a ArrayType) (sz:int) = shrink (a,sz);

end;

end;

structure FArray = struct
  datatype 'a Cell = Value of 'a Array.array | Upd of (int*'a*'a Cell Unsynchronized.ref);

  type 'a array = 'a Cell Unsynchronized.ref;

  fun array (size,v) = Unsynchronized.ref (Value (Array.array (size,v)));
  fun tabulate (size, f) = Unsynchronized.ref (Value (Array.tabulate(size, f)));
  fun fromList l = Unsynchronized.ref (Value (Array.fromList l));

  fun sub (Unsynchronized.ref (Value a), idx) = Array.sub (a,idx) |
      sub (Unsynchronized.ref (Upd (i,v,cr)),idx) =
        if i=idx then v
        else sub (cr,idx);

  fun length (Unsynchronized.ref (Value a)) = Array.length a |
      length (Unsynchronized.ref (Upd (i,v,cr))) = length cr;

  fun realize_aux (aref, v) =
    case aref of
      (Unsynchronized.ref (Value a)) => (
        let
          val len = Array.length a;
          val a' = Array.array (len,v);
        in
          Array.copy {src=a, dst=a', di=0};
          Unsynchronized.ref (Value a')
        end
      ) |
      (Unsynchronized.ref (Upd (i,v,cr))) => (
        let val res=realize_aux (cr,v) in
          case res of
            (Unsynchronized.ref (Value a)) => (Array.update (a,i,v); res)
        end
      );

  fun realize aref =
    case aref of
      (Unsynchronized.ref (Value _)) => aref |
      (Unsynchronized.ref (Upd (i,v,cr))) => realize_aux(aref,v);

  fun update (aref,idx,v) =
    case aref of
      (Unsynchronized.ref (Value a)) => (
        let val nref=Unsynchronized.ref (Value a) in
          aref := Upd (idx,Array.sub(a,idx),nref);
          Array.update (a,idx,v);
          nref
        end
      ) |
      (Unsynchronized.ref (Upd _)) =>
        let val ra = realize_aux(aref,v) in
          case ra of
            (Unsynchronized.ref (Value a)) => Array.update (a,idx,v);
          ra
        end
      ;

  fun grow (aref, inc, x) = case aref of 
    (Unsynchronized.ref (Value a)) => (
      let val len=Array.length a;
          val na = Array.array (len+inc,x) 
      in
        Array.copy {src=a, dst=na, di=0};
        Unsynchronized.ref (Value na)
      end
      )
  | (Unsynchronized.ref (Upd _)) => (
    grow (realize aref, inc, x)
  );

  fun shrink (aref, sz) = case aref of
    (Unsynchronized.ref (Value a)) => (
      if sz > Array.length a then 
        raise Size
      else (
        Unsynchronized.ref (Value (Array.tabulate (sz,fn i => Array.sub (a,i))))
      )
    ) |
    (Unsynchronized.ref (Upd _)) => (
      shrink (realize aref,sz)
    );

structure IsabelleMapping = struct
type 'a ArrayType = 'a array;

fun new_array (a:'a) (n:int) = array (n, a);

fun array_length (a:'a ArrayType) = length a;

fun array_get (a:'a ArrayType) (i:int) = sub (a, i);

fun array_set (a:'a ArrayType) (i:int) (e:'a) = update (a, i, e);

fun array_of_list (xs:'a list) = fromList xs;

fun array_grow (a:'a ArrayType) (i:int) (x:'a) = grow (a, i, x);

fun array_shrink (a:'a ArrayType) (sz:int) = shrink (a,sz);

fun array_get_oo (d:'a) (a:'a ArrayType) (i:int) = 
  sub (a,i) handle Subscript => d

fun array_set_oo (d:(unit->'a ArrayType)) (a:'a ArrayType) (i:int) (e:'a) = 
  update (a, i, e) handle Subscript => d ()

end;
end;





    fun array_blit src si dst di len = 
      ArraySlice.copy {
        di=di,
        src = ArraySlice.slice (src,si,SOME len),
        dst=dst}

    fun array_nth_oo v a i () = Array.sub(a,i) handle Subscript => v
    fun array_upd_oo f i x a () = 
      (Array.update(a,i,x); a) handle Subscript => f ()

    


  structure Statistics : sig
    type stat_entry = string * (unit -> bool) * (unit -> string)
  
    val register_stat : stat_entry -> unit
    val get_active_stats : unit -> (string * string) list
    val pretty_stats : (string * string) list -> string

  end = struct
    type stat_entry = string * (unit -> bool) * (unit -> string)
    val stats : stat_entry list Unsynchronized.ref = Unsynchronized.ref []
  
    fun register_stat e = stats := e :: !stats

    fun get_active_stats () = let
      fun flt [] = []
        | flt ((n,a,s)::l) = if a () then (n,s ()) :: flt l else flt l

    in flt (!stats)
    end

    fun pretty_stats [] = ""
      | pretty_stats ((n,s)::l) = "=== " ^ n ^ " ===\n" ^ s ^ "\n" ^ pretty_stats l
  end

(* Argh! Functors not compatible with ML_val command!
  functor Timer () : sig 
    val reset : unit -> unit
    val start : unit -> unit
    val stop : unit -> unit
    val set : Time.time -> unit
    val get : unit -> Time.time
    val pretty : unit -> string
  end = struct

    open Time;

    val time : Time.time Unsynchronized.ref = Unsynchronized.ref Time.zeroTime
    val running : bool Unsynchronized.ref = Unsynchronized.ref false
    val start_time : Time.time Unsynchronized.ref = Unsynchronized.ref Time.zeroTime
        
    fun reset () = (
      time := Time.zeroTime;
      running := false;
      start_time := Time.zeroTime
    )

    fun start () = 
      if !running then 
        () 
      else (
        running := true;
        start_time := Time.now ()
      )

    fun this_runs_time () = 
      if !running then 
        Time.now () - !start_time 
      else 
        Time.zeroTime

    fun stop () = (
      time := !time + this_runs_time ();
      running := false
    )

    fun get () = !time + this_runs_time ()
    fun set t = time := t - this_runs_time ()
  
    fun pretty () = Time.toString (!time) ^ "s"
  end
  *)



structure Bits_Integer : sig
  val set_bit : IntInf.int -> IntInf.int -> bool -> IntInf.int
  val shiftl : IntInf.int -> IntInf.int -> IntInf.int
  val shiftr : IntInf.int -> IntInf.int -> IntInf.int
  val test_bit : IntInf.int -> IntInf.int -> bool
end = struct

val maxWord = IntInf.pow (2, Word.wordSize);

fun set_bit x n b =
  if n < maxWord then
    if b then IntInf.orb (x, IntInf.<< (1, Word.fromLargeInt (IntInf.toLarge n)))
    else IntInf.andb (x, IntInf.notb (IntInf.<< (1, Word.fromLargeInt (IntInf.toLarge n))))
  else raise (Fail ("Bit index too large: " ^ IntInf.toString n));

fun shiftl x n =
  if n < maxWord then IntInf.<< (x, Word.fromLargeInt (IntInf.toLarge n))
  else raise (Fail ("Shift operand too large: " ^ IntInf.toString n));

fun shiftr x n =
  if n < maxWord then IntInf.~>> (x, Word.fromLargeInt (IntInf.toLarge n))
  else raise (Fail ("Shift operand too large: " ^ IntInf.toString n));

fun test_bit x n =
  if n < maxWord then IntInf.andb (x, IntInf.<< (1, Word.fromLargeInt (IntInf.toLarge n))) <> 0
  else raise (Fail ("Bit index too large: " ^ IntInf.toString n));

end; (*struct Bits_Integer*)

structure Fofu : sig
  type nat
  val integer_of_nat : nat -> IntInf.int
  val nat_of_integer : IntInf.int -> nat
  val get_flow : (nat * nat -> nat) -> nat -> nat -> nat array -> (unit -> nat)
  val edka_imp :
    (nat * nat -> nat) ->
      nat -> nat -> nat -> (nat -> nat list) -> (unit -> (nat array))
  val prepareNet :
    (nat * (nat * nat)) list ->
      nat -> nat -> ((nat * nat -> nat) * ((nat -> nat list) * nat)) option
  val edmonds_karp :
    (nat * (nat * nat)) list ->
      nat -> nat -> (unit -> ((nat * nat array) option))
end = struct

datatype nat = Nat of IntInf.int;

fun integer_of_nat (Nat x) = x;

fun equal_nata m n = (((integer_of_nat m) : IntInf.int) = (integer_of_nat n));

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

val equal_nat = {equal = equal_nata} : nat equal;

datatype typerepa = Typerep of string * typerepa list;

datatype nibble = Nibble0 | Nibble1 | Nibble2 | Nibble3 | Nibble4 | Nibble5 |
  Nibble6 | Nibble7 | Nibble8 | Nibble9 | NibbleA | NibbleB | NibbleC | NibbleD
  | NibbleE | NibbleF;

datatype 'a itself = Type;

fun typerep_nata t = Typerep ("Nat.nat", []);

type 'a typerep = {typerep : 'a itself -> typerepa};
val typerep = #typerep : 'a typerep -> 'a itself -> typerepa;

type 'a countable = {};

type 'a heap = {countable_heap : 'a countable, typerep_heap : 'a typerep};
val countable_heap = #countable_heap : 'a heap -> 'a countable;
val typerep_heap = #typerep_heap : 'a heap -> 'a typerep;

val countable_nat = {} : nat countable;

val typerep_nat = {typerep = typerep_nata} : nat typerep;

val heap_nat = {countable_heap = countable_nat, typerep_heap = typerep_nat} :
  nat heap;

datatype num = One | Bit0 of num | Bit1 of num;

val one_nata : nat = Nat (1 : IntInf.int);

type 'a one = {one : 'a};
val one = #one : 'a one -> 'a;

val one_nat = {one = one_nata} : nat one;

val zero_nata : nat = Nat (0 : IntInf.int);

type 'a zero = {zero : 'a};
val zero = #zero : 'a zero -> 'a;

val zero_nat = {zero = zero_nata} : nat zero;

fun less_eq_nat m n = IntInf.<= (integer_of_nat m, integer_of_nat n);

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

fun less_nat m n = IntInf.< (integer_of_nat m, integer_of_nat n);

val ord_nat = {less_eq = less_eq_nat, less = less_nat} : nat ord;

type 'a preorder = {ord_preorder : 'a ord};
val ord_preorder = #ord_preorder : 'a preorder -> 'a ord;

type 'a order = {preorder_order : 'a preorder};
val preorder_order = #preorder_order : 'a order -> 'a preorder;

val preorder_nat = {ord_preorder = ord_nat} : nat preorder;

val order_nat = {preorder_order = preorder_nat} : nat order;

fun max A_ a b = (if less_eq A_ a b then b else a);

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int ord;

fun nat_of_integer k = Nat (max ord_integer (0 : IntInf.int) k);

fun def_hashmap_size_nat x = (fn _ => nat_of_integer (16 : IntInf.int)) x;

type 'a hashable =
  {hashcode : 'a -> Word32.word, def_hashmap_size : 'a itself -> nat};
val hashcode = #hashcode : 'a hashable -> 'a -> Word32.word;
val def_hashmap_size = #def_hashmap_size : 'a hashable -> 'a itself -> nat;

datatype int = Int_of_integer of IntInf.int;

fun int_of_nat n = Int_of_integer (integer_of_nat n);

fun integer_of_int (Int_of_integer k) = k;

fun uint32_of_int i = Word32.fromLargeInt (IntInf.toLarge (integer_of_int i));

fun hashcode_nat n = uint32_of_int (int_of_nat n);

val hashable_nat =
  {hashcode = hashcode_nat, def_hashmap_size = def_hashmap_size_nat} :
  nat hashable;

type 'a linorder = {order_linorder : 'a order};
val order_linorder = #order_linorder : 'a linorder -> 'a order;

val linorder_nat = {order_linorder = order_nat} : nat linorder;

fun typerep_lista A_ t = Typerep ("List.list", [typerep A_ Type]);

fun countable_list A_ = {} : ('a list) countable;

fun typerep_list A_ = {typerep = typerep_lista A_} : ('a list) typerep;

fun heap_list A_ =
  {countable_heap = countable_list (countable_heap A_),
    typerep_heap = typerep_list (typerep_heap A_)}
  : ('a list) heap;

fun typerep_optiona A_ t = Typerep ("Option.option", [typerep A_ Type]);

fun countable_option A_ = {} : ('a option) countable;

fun typerep_option A_ = {typerep = typerep_optiona A_} : ('a option) typerep;

fun heap_option A_ =
  {countable_heap = countable_option (countable_heap A_),
    typerep_heap = typerep_option (typerep_heap A_)}
  : ('a option) heap;

fun eq A_ a b = equal A_ a b;

fun equal_proda A_ B_ (x1, x2) (y1, y2) = eq A_ x1 y1 andalso eq B_ x2 y2;

fun equal_prod A_ B_ = {equal = equal_proda A_ B_} : ('a * 'b) equal;

fun plus_nat m n = Nat (IntInf.+ (integer_of_nat m, integer_of_nat n));

fun def_hashmap_size_prod A_ B_ =
  (fn _ => plus_nat (def_hashmap_size A_ Type) (def_hashmap_size B_ Type));

fun snd (x1, x2) = x2;

fun fst (x1, x2) = x1;

fun hashcode_prod A_ B_ x =
  Word32.+ (Word32.* (hashcode A_
                        (fst x), Word32.fromLargeInt (IntInf.toLarge (33 : IntInf.int))), hashcode
            B_ (snd x));

fun hashable_prod A_ B_ =
  {hashcode = hashcode_prod A_ B_,
    def_hashmap_size = def_hashmap_size_prod A_ B_}
  : ('a * 'b) hashable;

datatype 'a set = Set of 'a list | Coset of 'a list;

datatype 'a dres = DSUCCEEDi | DFAILi | DRETURN of 'a;

datatype ('a, 'b) hashmapa =
  HashMapa of (('a * 'b) list) FArray.IsabelleMapping.ArrayType * nat;

datatype ('b, 'a) hashmap = HashMap of ('b, 'a) hashmapa;

datatype ('a, 'b) hashmapb =
  HashMapb of (('a * 'b) list) FArray.IsabelleMapping.ArrayType * nat;

datatype ('a, 'b, 'c, 'd) gen_g_impl_ext = Gen_g_impl_ext of 'a * 'b * 'c * 'd;

datatype 'a pre_network_ext =
  Pre_network_ext of
    ((nat * nat), nat) hashmap * (nat, unit) hashmap *
      (nat, (nat list)) hashmap * (nat, (nat list)) hashmap *
      (nat, (nat list)) hashmap * bool * bool * 'a;

datatype ('a, 'b, 'c) simple_state_nos_impl_ext =
  Simple_state_nos_impl_ext of 'a * 'b * 'c;

fun suc n = plus_nat n one_nata;

fun upt i j = (if less_nat i j then i :: upt (suc i) j else []);

fun len A_ a =
  (fn () => let
              val i = (fn () => Array.length a) ();
            in
              nat_of_integer i
            end);

fun new A_ = (fn a => fn b => (fn () => Array.array (a, b))) o integer_of_nat;

fun nth A_ a n = (fn () => Array.sub (a, integer_of_nat n));

fun upd A_ i x a =
  (fn () =>
    let
      val _ = (fn () => Array.update (a, integer_of_nat i, x)) ();
    in
      a
    end);

fun fold f (x :: xs) s = fold f xs (f x s)
  | fold f [] s = s;

fun map f [] = []
  | map f (x21 :: x22) = f x21 :: map f x22;

fun image f (Set xs) = Set (map f xs);

fun make A_ n f =
  (fn () => Array.tabulate (integer_of_nat n, f o nat_of_integer));

fun map_of A_ ((l, v) :: ps) k = (if eq A_ l k then SOME v else map_of A_ ps k)
  | map_of A_ [] k = NONE;

fun removeAll A_ x [] = []
  | removeAll A_ x (y :: xs) =
    (if eq A_ x y then removeAll A_ x xs else y :: removeAll A_ x xs);

fun membera A_ [] y = false
  | membera A_ (x :: xs) y = eq A_ x y orelse membera A_ xs y;

fun inserta A_ x xs = (if membera A_ xs x then xs else x :: xs);

fun insert A_ x (Coset xs) = Coset (removeAll A_ x xs)
  | insert A_ x (Set xs) = Set (inserta A_ x xs);

fun member A_ x (Coset xs) = not (membera A_ xs x)
  | member A_ x (Set xs) = membera A_ xs x;

fun filter p [] = []
  | filter p (x :: xs) = (if p x then x :: filter p xs else filter p xs);

fun bind NONE f = NONE
  | bind (SOME x) f = f x;

fun update A_ k v [] = [(k, v)]
  | update A_ k v (p :: ps) =
    (if eq A_ (fst p) k then (k, v) :: ps else p :: update A_ k v ps);

fun foldli [] c f sigma = sigma
  | foldli (x :: xs) c f sigma =
    (if c sigma then foldli xs c f (f x sigma) else sigma);

fun hd (x21 :: x22) = x21;

fun minus_nat m n =
  Nat (max ord_integer (0 : IntInf.int)
        (IntInf.- (integer_of_nat m, integer_of_nat n)));

fun times_nat m n = Nat (IntInf.* (integer_of_nat m, integer_of_nat n));

fun mtx_get A_ n mtx e = nth A_ mtx (plus_nat (fst e) (times_nat (snd e) n));

fun imp_nfoldli (x :: ls) c f s =
  (fn () =>
    let
      val b = c s ();
    in
      (if b then (fn f_ => fn () => f_ ((f x s) ()) ()) (imp_nfoldli ls c f)
        else (fn () => s))
        ()
    end)
  | imp_nfoldli [] c f s = (fn () => s);

fun get_flow c n s fi =
  imp_nfoldli (upt zero_nata n) (fn _ => (fn () => true))
    (fn v => fn cap =>
      let
        val csv = c (s, v);
      in
        (fn () =>
          let
            val cfsv = mtx_get heap_nat n fi (s, v) ();
          in
            let
              val fsv = minus_nat csv cfsv;
            in
              (fn () => (plus_nat cap fsv))
            end
              ()
          end)
      end)
    zero_nata;

fun maxa A_ (Set (x :: xs)) =
  fold (max ((ord_preorder o preorder_order o order_linorder) A_)) xs x;

fun sup_set A_ (Coset xs) a = Coset (filter (fn x => not (member A_ x a)) xs)
  | sup_set A_ (Set xs) a = fold (insert A_) xs a;

fun ln_N el =
  plus_nat
    (maxa linorder_nat
      (sup_set equal_nat (image fst (Set el)) (image (fst o snd) (Set el))))
    one_nata;

fun pn_t_node_update pn_t_nodea
  (Pre_network_ext
    (pn_c, pn_V, pn_succ, pn_pred, pn_psucc, pn_s_node, pn_t_node, more))
  = Pre_network_ext
      (pn_c, pn_V, pn_succ, pn_pred, pn_psucc, pn_s_node, pn_t_nodea pn_t_node,
        more);

fun pn_s_node_update pn_s_nodea
  (Pre_network_ext
    (pn_c, pn_V, pn_succ, pn_pred, pn_psucc, pn_s_node, pn_t_node, more))
  = Pre_network_ext
      (pn_c, pn_V, pn_succ, pn_pred, pn_psucc, pn_s_nodea pn_s_node, pn_t_node,
        more);

fun pn_psucc_update pn_psucca
  (Pre_network_ext
    (pn_c, pn_V, pn_succ, pn_pred, pn_psucc, pn_s_node, pn_t_node, more))
  = Pre_network_ext
      (pn_c, pn_V, pn_succ, pn_pred, pn_psucca pn_psucc, pn_s_node, pn_t_node,
        more);

fun pn_succ_update pn_succa
  (Pre_network_ext
    (pn_c, pn_V, pn_succ, pn_pred, pn_psucc, pn_s_node, pn_t_node, more))
  = Pre_network_ext
      (pn_c, pn_V, pn_succa pn_succ, pn_pred, pn_psucc, pn_s_node, pn_t_node,
        more);

fun pn_pred_update pn_preda
  (Pre_network_ext
    (pn_c, pn_V, pn_succ, pn_pred, pn_psucc, pn_s_node, pn_t_node, more))
  = Pre_network_ext
      (pn_c, pn_V, pn_succ, pn_preda pn_pred, pn_psucc, pn_s_node, pn_t_node,
        more);

fun pn_c_update pn_ca
  (Pre_network_ext
    (pn_c, pn_V, pn_succ, pn_pred, pn_psucc, pn_s_node, pn_t_node, more))
  = Pre_network_ext
      (pn_ca pn_c, pn_V, pn_succ, pn_pred, pn_psucc, pn_s_node, pn_t_node,
        more);

fun pn_V_update pn_Va
  (Pre_network_ext
    (pn_c, pn_V, pn_succ, pn_pred, pn_psucc, pn_s_node, pn_t_node, more))
  = Pre_network_ext
      (pn_c, pn_Va pn_V, pn_succ, pn_pred, pn_psucc, pn_s_node, pn_t_node,
        more);

fun pn_t_node
  (Pre_network_ext
    (pn_c, pn_V, pn_succ, pn_pred, pn_psucc, pn_s_node, pn_t_node, more))
  = pn_t_node;

fun pn_s_node
  (Pre_network_ext
    (pn_c, pn_V, pn_succ, pn_pred, pn_psucc, pn_s_node, pn_t_node, more))
  = pn_s_node;

fun new_array v = FArray.IsabelleMapping.new_array v o integer_of_nat;

fun new_hashmap_with A_ size = HashMapa (new_array [] size, zero_nata);

fun ahm_emptya A_ = (fn _ => new_hashmap_with A_ (def_hashmap_size A_ Type));

fun ahm_empty_const A_ = HashMap (ahm_emptya A_ ());

fun ahm_empty A_ = (fn _ => ahm_empty_const A_);

fun empty_ahm_basic_ops A_ = ahm_empty A_;

fun pn_psucc
  (Pre_network_ext
    (pn_c, pn_V, pn_succ, pn_pred, pn_psucc, pn_s_node, pn_t_node, more))
  = pn_psucc;

fun pn_succ
  (Pre_network_ext
    (pn_c, pn_V, pn_succ, pn_pred, pn_psucc, pn_s_node, pn_t_node, more))
  = pn_succ;

fun pn_pred
  (Pre_network_ext
    (pn_c, pn_V, pn_succ, pn_pred, pn_psucc, pn_s_node, pn_t_node, more))
  = pn_pred;

fun sgn_integer k =
  (if ((k : IntInf.int) = (0 : IntInf.int)) then (0 : IntInf.int)
    else (if IntInf.< (k, (0 : IntInf.int)) then (~1 : IntInf.int)
           else (1 : IntInf.int)));

fun abs_integer k = (if IntInf.< (k, (0 : IntInf.int)) then IntInf.~ k else k);

fun apsnd f (x, y) = (x, f y);

fun divmod_integer k l =
  (if ((k : IntInf.int) = (0 : IntInf.int))
    then ((0 : IntInf.int), (0 : IntInf.int))
    else (if ((l : IntInf.int) = (0 : IntInf.int)) then ((0 : IntInf.int), k)
           else (apsnd o (fn a => fn b => IntInf.* (a, b)) o sgn_integer) l
                  (if (((sgn_integer k) : IntInf.int) = (sgn_integer l))
                    then IntInf.divMod (IntInf.abs k, IntInf.abs l)
                    else let
                           val (r, s) =
                             IntInf.divMod (IntInf.abs k, IntInf.abs l);
                         in
                           (if ((s : IntInf.int) = (0 : IntInf.int))
                             then (IntInf.~ r, (0 : IntInf.int))
                             else (IntInf.- (IntInf.~ r, (1 : IntInf.int)),
                                    IntInf.- (abs_integer l, s)))
                         end)));

fun mod_integer k l = snd (divmod_integer k l);

fun mod_nat m n = Nat (mod_integer (integer_of_nat m) (integer_of_nat n));

fun nat_of_uint32 x =
  nat_of_integer (IntInf.fromLarge (Word32.toLargeInt x) : IntInf.int);

fun nat_of_hashcode x = nat_of_uint32 x;

fun bounded_hashcode_nat A_ n x = mod_nat (nat_of_hashcode (hashcode A_ x)) n;

fun array_length x = (nat_of_integer o FArray.IsabelleMapping.array_length) x;

fun array_set a = FArray.IsabelleMapping.array_set a o integer_of_nat;

fun array_get a = FArray.IsabelleMapping.array_get a o integer_of_nat;

fun is_none (SOME x) = false
  | is_none NONE = true;

fun ahm_update_aux (A1_, A2_) (HashMapa (a, n)) k v =
  let
    val h = bounded_hashcode_nat A2_ (array_length a) k;
    val m = array_get a h;
    val insert = is_none (map_of A1_ m k);
  in
    HashMapa
      (array_set a h (update A1_ k v m),
        (if insert then plus_nat n one_nata else n))
  end;

fun idx_iteratei_aux_array_get sz i l c f sigma =
  (if equal_nata i zero_nata orelse not (c sigma) then sigma
    else idx_iteratei_aux_array_get sz (minus_nat i one_nata) l c f
           (f (array_get l (minus_nat sz i)) sigma));

fun idx_iteratei_array_length_array_get l c f sigma =
  idx_iteratei_aux_array_get (array_length l) (array_length l) l c f sigma;

fun ahm_iteratei_aux A_ a c f sigma =
  idx_iteratei_array_length_array_get a c (fn x => foldli x c f) sigma;

fun ahm_rehash_auxa A_ n kv a =
  let
    val h = bounded_hashcode_nat A_ n (fst kv);
  in
    array_set a h (kv :: array_get a h)
  end;

fun ahm_rehash_aux A_ a sz =
  ahm_iteratei_aux A_ a (fn _ => true) (ahm_rehash_auxa A_ sz)
    (new_array [] sz);

fun ahm_rehash A_ (HashMapa (a, n)) sz = HashMapa (ahm_rehash_aux A_ a sz, n);

val load_factor : nat = nat_of_integer (75 : IntInf.int);

fun ahm_filled A_ (HashMapa (a, n)) =
  less_eq_nat (times_nat (array_length a) load_factor)
    (times_nat n (nat_of_integer (100 : IntInf.int)));

fun hm_grow A_ (HashMapa (a, n)) =
  plus_nat (times_nat (nat_of_integer (2 : IntInf.int)) (array_length a))
    (nat_of_integer (3 : IntInf.int));

fun ahm_updatea (A1_, A2_) k v hm =
  let
    val hma = ahm_update_aux (A1_, A2_) hm k v;
  in
    (if ahm_filled A2_ hma then ahm_rehash A2_ hma (hm_grow A2_ hma) else hma)
  end;

fun impl_of B_ (HashMap x) = x;

fun ahm_update (A1_, A2_) k v hm =
  HashMap (ahm_updatea (A1_, A2_) k v (impl_of A2_ hm));

fun ins_ahm_basic_ops (A1_, A2_) x s = ahm_update (A1_, A2_) x () s;

fun pn_c
  (Pre_network_ext
    (pn_c, pn_V, pn_succ, pn_pred, pn_psucc, pn_s_node, pn_t_node, more))
  = pn_c;

fun pn_V
  (Pre_network_ext
    (pn_c, pn_V, pn_succ, pn_pred, pn_psucc, pn_s_node, pn_t_node, more))
  = pn_V;

fun ahm_alpha_aux (A1_, A2_) a k =
  map_of A1_ (array_get a (bounded_hashcode_nat A2_ (array_length a) k)) k;

fun ahm_alpha (A1_, A2_) (HashMapa (a, uu)) = ahm_alpha_aux (A1_, A2_) a;

fun ahm_lookupa (A1_, A2_) k hm = ahm_alpha (A1_, A2_) hm k;

fun ahm_lookup (A1_, A2_) k hm = ahm_lookupa (A1_, A2_) k (impl_of A2_ hm);

fun the_default uu (SOME x) = x
  | the_default x NONE = x;

fun ahm_ld (B1_, B2_) a ahm k = the_default a (ahm_lookup (B1_, B2_) k ahm);

fun read [] uu uv =
  SOME (Pre_network_ext
         (ahm_empty (hashable_prod hashable_nat hashable_nat) (),
           empty_ahm_basic_ops hashable_nat (), ahm_empty hashable_nat (),
           ahm_empty hashable_nat (), ahm_empty hashable_nat (), false, false,
           ()))
  | read ((u, (v, c)) :: es) s t =
    (case read es s t of NONE => NONE
      | SOME x =>
        (if equal_nata
              (ahm_ld
                (equal_prod equal_nat equal_nat,
                  hashable_prod hashable_nat hashable_nat)
                zero_nata (pn_c x) (u, v))
              zero_nata andalso
              (equal_nata
                 (ahm_ld
                   (equal_prod equal_nat equal_nat,
                     hashable_prod hashable_nat hashable_nat)
                   zero_nata (pn_c x) (v, u))
                 zero_nata andalso
                less_nat zero_nata c)
          then (if equal_nata u v orelse (equal_nata v s orelse equal_nata u t)
                 then NONE
                 else SOME (pn_t_node_update
                             (fn _ => pn_t_node x orelse equal_nata v t)
                             (pn_s_node_update
                               (fn _ => pn_s_node x orelse equal_nata u s)
                               (pn_psucc_update
                                 (fn _ =>
                                   ahm_update (equal_nat, hashable_nat) u
                                     (v :: ahm_ld (equal_nat, hashable_nat) []
     (pn_psucc x) u)
                                     (ahm_update (equal_nat, hashable_nat) v
                                       (u ::
 ahm_ld (equal_nat, hashable_nat) [] (pn_psucc x) v)
                                       (pn_psucc x)))
                                 (pn_pred_update
                                   (fn _ =>
                                     ahm_update (equal_nat, hashable_nat) v
                                       (u ::
 ahm_ld (equal_nat, hashable_nat) [] (pn_pred x) v)
                                       (pn_pred x))
                                   (pn_succ_update
                                     (fn _ =>
                                       ahm_update (equal_nat, hashable_nat) u
 (v :: ahm_ld (equal_nat, hashable_nat) [] (pn_succ x) u) (pn_succ x))
                                     (pn_V_update
                                       (fn _ =>
 ins_ahm_basic_ops (equal_nat, hashable_nat) u
   (ins_ahm_basic_ops (equal_nat, hashable_nat) v (pn_V x)))
                                       (pn_c_update
 (fn _ =>
   ahm_update
     (equal_prod equal_nat equal_nat, hashable_prod hashable_nat hashable_nat)
     (u, v) c (pn_c x))
 x))))))))
          else NONE));

fun blit A_ src si dst di len =
  (fn () => 
    array_blit src (integer_of_nat
                     si) dst (integer_of_nat di) (integer_of_nat len));

fun gen_ball it s p = it s (fn x => x) (fn x => fn _ => p x) true;

fun the (SOME x2) = x2;

fun gen_pick it s =
  the (it s (fn a => (case a of NONE => true | SOME _ => false))
         (fn x => fn _ => SOME x)
        NONE);

fun nth_oo A_ v a = (fn b => array_nth_oo v a b) o integer_of_nat;

fun upd_oo A_ f =
  (fn a => fn b => fn c => array_upd_oo f a b c) o integer_of_nat;

fun min A_ a b = (if less_eq A_ a b then a else b);

fun bottleNeck_imp_0 n cfi x =
  (case x of ([], s) => (fn () => s)
    | (xa :: ls, s) =>
      (if true
        then (fn () =>
               let
                 val xb = mtx_get heap_nat n cfi xa ();
               in
                 bottleNeck_imp_0 n cfi (ls, min ord_nat xb s) ()
               end)
        else (fn () => s)));

fun bottleNeck_imp n cfi pi =
  (case pi of [] => (fn () => zero_nata)
    | x_b :: xs =>
      (fn () =>
        let
          val x_c = mtx_get heap_nat n cfi x_b ();
        in
          bottleNeck_imp_0 n cfi (xs, x_c) ()
        end));

fun heap_WHILET b f s =
  (fn () =>
    let
      val bv = b s ();
    in
      (if bv then (fn f_ => fn () => f_ ((f s) ()) ()) (heap_WHILET b f)
        else (fn () => s))
        ()
    end);

fun mtx_set A_ n mtx e v =
  upd A_ (plus_nat (fst e) (times_nat (snd e) n)) v mtx;

fun swap p = (snd p, fst p);

fun augment_imp_0 n capi x =
  (case x of ([], a2) => (fn () => a2)
    | (x_d :: xs, a2) =>
      (fn () =>
        let
          val xa = mtx_get heap_nat n a2 x_d ();
          val xb = mtx_set heap_nat n a2 x_d (minus_nat xa capi) ();
          val x_e =
            let
              val x_g = swap x_d;
            in
              (fn f_ => fn () => f_ ((mtx_get heap_nat n xb x_g) ()) ())
                (fn x_i => mtx_set heap_nat n xb x_g (plus_nat x_i capi))
            end
              ();
        in
          augment_imp_0 n capi (xs, x_e) ()
        end));

fun augment_imp n cfi pi capi = augment_imp_0 n capi (pi, cfi);

fun div_integer k l = fst (divmod_integer k l);

fun div_nat m n = Nat (div_integer (integer_of_nat m) (integer_of_nat n));

fun mtx_new A_ n c =
  make A_ (times_nat n n) (fn i => c (mod_nat i n, div_nat i n));

fun equal_bool p true = p
  | equal_bool p false = not p
  | equal_bool true p = p
  | equal_bool false p = not p;

fun array_grow A_ a s x =
  (fn () =>
    let
      val l = len A_ a ();
    in
      (if equal_nata l s then (fn () => a)
        else (fn f_ => fn () => f_ ((new A_ s x) ()) ())
               (fn aa =>
                 (fn f_ => fn () => f_ ((blit A_ a zero_nata aa zero_nata l) ())
                   ())
                   (fn _ => (fn () => aa))))
        ()
    end);

fun iam_update A_ k v a =
  upd_oo (heap_option A_)
    (fn () =>
      let
        val l = len (heap_option A_) a ();
      in
        let
          val newsz =
            max ord_nat (plus_nat k one_nata)
              (plus_nat (times_nat (nat_of_integer (2 : IntInf.int)) l)
                (nat_of_integer (3 : IntInf.int)));
        in
          (fn f_ => fn () => f_ ((array_grow (heap_option A_) a newsz NONE) ())
            ())
            (upd (heap_option A_) k (SOME v))
        end
          ()
      end)
    k (SOME v) a;

val iam_initial_size : nat = nat_of_integer (8 : IntInf.int);

fun iam_new_sz A_ sz = new (heap_option A_) sz NONE;

fun iam_new A_ = iam_new_sz A_ iam_initial_size;

fun init_state_impl srci =
  (fn () =>
    let
      val x = iam_new heap_nat ();
      val xa = iam_update heap_nat srci srci x ();
    in
      (false, (xa, ([srci], ([], zero_nata))))
    end);

fun is_None a = (case a of NONE => true | SOME _ => false);

fun is_Nil a = (case a of [] => true | _ :: _ => false);

fun rev_append [] ac = ac
  | rev_append (x :: xs) ac = rev_append xs (x :: ac);

fun glist_delete_aux eq x [] asa = asa
  | glist_delete_aux eq x (y :: ys) asa =
    (if eq x y then rev_append asa ys else glist_delete_aux eq x ys (y :: asa));

fun glist_delete eq x l = glist_delete_aux eq x l [];

fun iam_lookup A_ k a = nth_oo (heap_option A_) NONE a k;

fun bfs_impl n c s t =
  (if equal_nata s t then (fn () => (SOME []))
    else (fn () =>
           let
             val x_d = init_state_impl s ();
             val x_e =
               heap_WHILET
                 (fn (a1, (_, (a1b, (_, _)))) =>
                   (fn () => (equal_bool a1 false andalso not (is_Nil a1b))))
                 (fn (_, (a1a, (a1b, (a1c, a2c)))) =>
                   let
                     val x_e = hd a1b;
                     val x_f = glist_delete equal_nata x_e a1b;
                   in
                     (fn f_ => fn () => f_ ((n c x_e) ()) ())
                       (fn x_h =>
                         (fn f_ => fn () => f_
                           ((imp_nfoldli x_h
                              (fn (a1d, (_, _)) => (fn () => (not a1d)))
                              (fn xg => fn (a1d, (a1e, a2e)) =>
                                (fn f_ => fn () => f_ (stat.inner_c_incr ()) ())
                                  (fn _ =>
                                    (fn f_ => fn () => f_
                                      ((iam_lookup heap_nat xg a1e) ()) ())
                                      (fn x =>
(if not (is_None x) then (fn () => (a1d, (a1e, a2e)))
  else (fn f_ => fn () => f_ ((iam_update heap_nat xg x_e a1e) ()) ())
         (fn x_l => (fn () => (equal_nata xg t, (x_l, xg :: a2e))))))))
                              (false, (a1a, a1c)))
                           ()) ())
                           (fn (a1d, (a1e, a2e)) =>
                             (fn () =>
                               (if a1d
                                 then (a1d,
(a1e, (x_f, (a2e, plus_nat a2c one_nata))))
                                 else (if is_Nil x_f
then (a1d, (a1e, (a2e, ([], plus_nat a2c one_nata))))
else (a1d, (a1e, (x_f, (a2e, a2c)))))))))
                   end)
                 x_d ();
           in
             (case (case x_e of (true, (a1a, (_, (_, a2c)))) => SOME (a2c, a1a)
                     | (false, (_, (_, (_, _)))) => NONE)
               of NONE => (fn () => NONE)
               | SOME (_, a2) =>
                 (fn f_ => fn () => f_
                   ((heap_WHILET
                      (fn (a1a, _) => (fn () => (not (equal_nata a1a s))))
                      (fn (a1a, a2a) =>
                        (fn f_ => fn () => f_ ((iam_lookup heap_nat a1a a2) ())
                          ())
                          (fn x =>
                            let
                              val x_i = the x;
                            in
                              (fn () => (x_i, (x_i, a1a) :: a2a))
                            end))
                      (t, []))
                   ()) ())
                   (fn x_h => (fn () => (SOME let
        val (_, b) = x_h;
      in
        b
      end))))
               ()
           end));

fun succ_imp_0 n cfi ui x =
  (case x of [] => (fn () => [])
    | x_d :: xs =>
      (fn () =>
        let
          val x_e = succ_imp_0 n cfi ui xs ();
          val x_f = mtx_get heap_nat n cfi (ui, x_d) ();
        in
          (if less_nat zero_nata x_f then x_d :: x_e else x_e)
        end));

fun ps_get_imp A_ psi u = nth A_ psi u;

fun succ_imp n psi cfi ui =
  (fn () =>
    let
      val x = ps_get_imp (heap_list heap_nat) psi ui ();
    in
      succ_imp_0 n cfi ui x ()
    end);

fun bfsi n s t psi cfi = bfs_impl (fn (a, b) => succ_imp n a b) (psi, cfi) s t;

fun edka_imp n ps c s t =
  (fn () =>
    let
      val x = mtx_new heap_nat s n ();
      val x_a = make (heap_list heap_nat) s t ();
      val a =
        heap_WHILET (fn (_, b) => (fn () => (not b)))
          (fn (a1, _) =>
            (fn f_ => fn () => f_ (stat.outer_c_incr ()) ())
              (fn _ =>
                (fn f_ => fn () => f_ ((bfsi s ps c x_a a1) ()) ())
                  (fn a =>
                    (case a of NONE => (fn () => (a1, true))
                      | SOME x_d =>
                        (fn f_ => fn () => f_ ((bottleNeck_imp s a1 x_d) ()) ())
                          (fn x_e =>
                            (fn f_ => fn () => f_ ((augment_imp s a1 x_d x_e)
                              ()) ())
                              (fn x_f => (fn () => (x_f, false))))))))
          (x, false) ();
    in
      let
        val (a1, _) = a;
      in
        (fn () => a1)
      end
        ()
    end);

fun rev_graph_of_impl pn t =
  Gen_g_impl_ext
    ((fn _ => true), ahm_ld (equal_nat, hashable_nat) [] (pn_pred pn), [t], ());

fun ssnos_visited_impl_update ssnos_visited_impla
  (Simple_state_nos_impl_ext (ssnos_stack_impl, ssnos_visited_impl, more)) =
  Simple_state_nos_impl_ext
    (ssnos_stack_impl, ssnos_visited_impla ssnos_visited_impl, more);

fun ssnos_stack_impl_update ssnos_stack_impla
  (Simple_state_nos_impl_ext (ssnos_stack_impl, ssnos_visited_impl, more)) =
  Simple_state_nos_impl_ext
    (ssnos_stack_impla ssnos_stack_impl, ssnos_visited_impl, more);

fun ssnos_visited_impl
  (Simple_state_nos_impl_ext (ssnos_stack_impl, ssnos_visited_impl, more)) =
  ssnos_visited_impl;

fun ssnos_stack_impl
  (Simple_state_nos_impl_ext (ssnos_stack_impl, ssnos_visited_impl, more)) =
  ssnos_stack_impl;

fun ras_singleton B_ x = (FArray.IsabelleMapping.array_of_list [x], one B_);

fun ras_is_empty s = equal_nata (snd s) zero_nata;

fun ras_empty B_ uu = (FArray.IsabelleMapping.array_of_list [], zero B_);

fun list_map_update_aux eq k v [] accu = (k, v) :: accu
  | list_map_update_aux eq k v (x :: xs) accu =
    (if eq (fst x) k then (k, v) :: xs @ accu
      else list_map_update_aux eq k v xs (x :: accu));

fun list_map_update eq k v m = list_map_update_aux eq k v m [];

fun list_map_lookup eq uu [] = NONE
  | list_map_lookup eq k (y :: ys) =
    (if eq (fst y) k then SOME (snd y) else list_map_lookup eq k ys);

fun ahm_update_auxa eq bhc (HashMapb (a, n)) k v =
  let
    val h = bhc (array_length a) k;
    val m = array_get a h;
    val insert = is_none (list_map_lookup eq k m);
  in
    HashMapb
      (array_set a h (list_map_update eq k v m),
        (if insert then plus_nat n one_nata else n))
  end;

fun idx_iteratei_aux get sz i l c f sigma =
  (if equal_nata i zero_nata orelse not (c sigma) then sigma
    else idx_iteratei_aux get sz (minus_nat i one_nata) l c f
           (f (get l (minus_nat sz i)) sigma));

fun idx_iteratei get sz l c f sigma =
  idx_iteratei_aux get (sz l) (sz l) l c f sigma;

fun ahm_iteratei_auxa a c f sigma =
  idx_iteratei array_get array_length a c (fn x => foldli x c f) sigma;

fun ahm_rehash_auxc bhc n kv a =
  let
    val h = bhc n (fst kv);
  in
    array_set a h (kv :: array_get a h)
  end;

fun ahm_rehash_auxb bhc a sz =
  ahm_iteratei_auxa a (fn _ => true) (ahm_rehash_auxc bhc sz) (new_array [] sz);

fun ahm_rehasha bhc (HashMapb (a, n)) sz =
  HashMapb (ahm_rehash_auxb bhc a sz, n);

val load_factora : nat = nat_of_integer (75 : IntInf.int);

fun ahm_filleda (HashMapb (a, n)) =
  less_eq_nat (times_nat (array_length a) load_factora)
    (times_nat n (nat_of_integer (100 : IntInf.int)));

fun hm_growa (HashMapb (a, n)) =
  plus_nat (times_nat (nat_of_integer (2 : IntInf.int)) (array_length a))
    (nat_of_integer (3 : IntInf.int));

fun ahm_updateb eq bhc k v hm =
  let
    val hma = ahm_update_auxa eq bhc hm k v;
  in
    (if ahm_filleda hma then ahm_rehasha bhc hma (hm_growa hma) else hma)
  end;

fun ahm_lookup_aux eq bhc k a =
  list_map_lookup eq k (array_get a (bhc (array_length a) k));

fun ahm_lookupb eq bhc k (HashMapb (a, uu)) = ahm_lookup_aux eq bhc k a;

fun array_growa a = FArray.IsabelleMapping.array_grow a o integer_of_nat;

fun ras_push x s =
  let
    val a = s;
    val (aa, n) = a;
    val ab =
      (if equal_nata n (array_length aa)
        then array_growa aa
               (max ord_nat (nat_of_integer (4 : IntInf.int))
                 (times_nat (nat_of_integer (2 : IntInf.int)) n))
               x
        else aa);
    val ac = array_set ab n x;
  in
    (ac, plus_nat n one_nata)
  end;

fun new_hashmap_witha size = HashMapb (new_array [] size, zero_nata);

fun ahm_emptyb def_size = new_hashmap_witha def_size;

fun gi_V0 (Gen_g_impl_ext (gi_V, gi_E, gi_V0, more)) = gi_V0;

fun ras_top s =
  let
    val a = s;
    val (aa, n) = a;
  in
    array_get aa (minus_nat n one_nata)
  end;

fun array_shrink a = FArray.IsabelleMapping.array_shrink a o integer_of_nat;

fun ras_shrink s =
  let
    val a = s;
    val (aa, n) = a;
    val ab =
      (if less_eq_nat (times_nat (nat_of_integer (128 : IntInf.int)) n)
            (array_length aa) andalso
            less_nat (nat_of_integer (4 : IntInf.int)) n
        then array_shrink aa n else aa);
  in
    (ab, n)
  end;

fun ras_pop s =
  let
    val a = s;
    val (aa, n) = a;
  in
    ras_shrink (aa, minus_nat n one_nata)
  end;

fun gi_E (Gen_g_impl_ext (gi_V, gi_E, gi_V0, more)) = gi_E;

fun map2set_insert i k s = i k () s;

fun map2set_memb l k s = (case l k s of NONE => false | SOME _ => true);

fun whilea b c s = (if b s then whilea b c (c s) else s);

fun find_reachable_codeT eq bhc sz gi =
  let
    val a =
      let
        val a =
          let
            val a = ();
          in
            Simple_state_nos_impl_ext (ras_empty zero_nat (), ahm_emptyb sz, a)
          end;
      in
        foldli (gi_V0 gi) (fn _ => not false)
          (fn xa => fn sigma =>
            let
              val _ = sigma;
            in
              (if map2set_memb (ahm_lookupb eq bhc) xa
                    (ssnos_visited_impl sigma)
                then sigma
                else let
                       val aa =
                         let
                           val xc =
                             let
                               val xd =
                                 ssnos_stack_impl_update
                                   (fn _ =>
                                     ras_singleton one_nat (xa, gi_E gi xa))
                                   sigma;
                               val xe =
                                 ssnos_visited_impl_update
                                   (fn _ =>
                                     map2set_insert (ahm_updateb eq bhc) xa
                                       (ssnos_visited_impl xd))
                                   xd;
                             in
                               xe
                             end;
                           val _ = ();
                         in
                           xc
                         end;
                     in
                       whilea
                         (fn xd =>
                           not false andalso
                             not (ras_is_empty (ssnos_stack_impl xd)))
                         (fn xd =>
                           (case let
                                   val ab = ras_top (ssnos_stack_impl xd);
                                   val (ac, b) = ab;
                                 in
                                   (if is_Nil b then (ac, (NONE, xd))
                                     else let
    val xf = gen_pick foldli b;
    val xg = glist_delete eq xf b;
    val xh =
      ssnos_stack_impl_update
        (fn _ => ras_push (ac, xg) (ras_pop (ssnos_stack_impl xd))) xd;
  in
    (ac, (SOME xf, xh))
  end)
                                 end
                             of (_, (NONE, ba)) =>
                               let
                                 val xf =
                                   let
                                     val xg =
                                       ssnos_stack_impl_update
 (fn _ => ras_pop (ssnos_stack_impl ba)) ba;
                                   in
                                     xg
                                   end;
                                 val _ = ();
                               in
                                 xf
                               end
                             | (_, (SOME xf, ba)) =>
                               (if map2set_memb (ahm_lookupb eq bhc) xf
                                     (ssnos_visited_impl ba)
                                 then let
val xg = ba;
val _ = ();
                                      in
xg
                                      end
                                 else let
val xg =
  let
    val xh =
      ssnos_stack_impl_update
        (fn _ => ras_push (xf, gi_E gi xf) (ssnos_stack_impl ba)) ba;
    val xi =
      ssnos_visited_impl_update
        (fn _ => map2set_insert (ahm_updateb eq bhc) xf (ssnos_visited_impl xh))
        xh;
  in
    xi
  end;
val _ = ();
                                      in
xg
                                      end)))
                         aa
                     end)
            end)
          a
      end;
  in
    ssnos_visited_impl a
  end;

fun the_res (DRETURN x) = x;

fun reachable_impl gi =
  the_res
    (DRETURN
      (find_reachable_codeT equal_nata (bounded_hashcode_nat hashable_nat)
        (def_hashmap_size_nat Type) gi));

fun graph_of_impl pn s =
  Gen_g_impl_ext
    ((fn _ => true), ahm_ld (equal_nat, hashable_nat) [] (pn_succ pn), [s], ());

fun ahm_iterateia A_ (HashMapa (a, n)) = ahm_iteratei_aux A_ a;

fun ahm_iteratei A_ hm = ahm_iterateia A_ (impl_of A_ hm);

fun iteratei_bset_op_list_it_dflt_basic_ops_ahm_basic_ops A_ s =
  (fn c => fn f => ahm_iteratei A_ s c (f o fst));

fun g_ball_dflt_basic_ops_ahm_basic_ops A_ s p =
  iteratei_bset_op_list_it_dflt_basic_ops_ahm_basic_ops A_ s (fn c => c)
    (fn x => fn _ => p x) true;

fun set_iterator_image g it = (fn c => fn f => it c (fn x => f (g x)));

fun map_iterator_dom it = set_iterator_image fst it;

fun ahm_iterateib (HashMapb (a, n)) = ahm_iteratei_auxa a;

fun memb_ahm_basic_ops (A1_, A2_) x s =
  not (is_none (ahm_lookup (A1_, A2_) x s));

fun it_to_list it s = it s (fn _ => true) (fn x => fn l => l @ [x]) [];

fun gen_subseteq ball1 mem2 s1 s2 = ball1 s1 (fn x => mem2 x s2);

fun gen_equal ss1 ss2 s1 s2 = ss1 s1 s2 andalso ss2 s2 s1;

fun sets_eq_impl ai bi =
  gen_equal
    (gen_subseteq (g_ball_dflt_basic_ops_ahm_basic_ops hashable_nat)
      (map2set_memb
        (ahm_lookupb equal_nata (bounded_hashcode_nat hashable_nat))))
    (gen_subseteq
      (gen_ball
        (fn x =>
          foldli
            (it_to_list (map_iterator_dom o (foldli o it_to_list ahm_iterateib))
              x)))
      (memb_ahm_basic_ops (equal_nat, hashable_nat)))
    ai bi;

fun net_alpha (A1_, A2_) B_ (C1_, C2_) (ci, psucci) =
  (ahm_ld (A1_, A2_) (zero B_) ci, ahm_ld (C1_, C2_) [] psucci);

fun checkNet4 el s t =
  (if equal_nata s t then NONE
    else (case read el s t of NONE => NONE
           | SOME xa =>
             (if pn_s_node xa andalso pn_t_node xa
               then let
                      val xb = reachable_impl (graph_of_impl xa s);
                      val xc = reachable_impl (rev_graph_of_impl xa t);
                    in
                      (if sets_eq_impl (pn_V xa) xb andalso
                            sets_eq_impl (pn_V xa) xc
                        then SOME (net_alpha
                                    (equal_prod equal_nat equal_nat,
                                      hashable_prod hashable_nat hashable_nat)
                                    zero_nat (equal_nat, hashable_nat)
                                    (pn_c xa, pn_psucc xa))
                        else NONE)
                    end
               else NONE)));

fun prepareNet el s t =
  bind (checkNet4 el s t)
    (fn (c, psucc) => let
                        val n = ln_N el;
                      in
                        SOME (c, (psucc, n))
                      end);

fun edmonds_karp el s t =
  (case prepareNet el s t of NONE => (fn () => NONE)
    | SOME (c, (ps, n)) =>
      (fn () => let
                  val f = edka_imp c s t n ps ();
                in
                  SOME (n, f)
                end));

end; (*struct Fofu*)
