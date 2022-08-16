(*  Title:      Pure/General/basics.ML
    Author:     Florian Haftmann and Makarius, TU Muenchen

Fundamental concepts.
*)

infix 1 |> |-> |>> ||> ||>>
infix 1 #> #-> #>> ##> ##>>

signature BASICS =
sig
  (*functions*)
  val |> : 'a * ('a -> 'b) -> 'b
  val |-> : ('c * 'a) * ('c -> 'a -> 'b) -> 'b
  val |>> : ('a * 'c) * ('a -> 'b) -> 'b * 'c
  val ||> : ('c * 'a) * ('a -> 'b) -> 'c * 'b
  val ||>> : ('c * 'a) * ('a -> 'd * 'b) -> ('c * 'd) * 'b
  val #> : ('a -> 'b) * ('b -> 'c) -> 'a -> 'c
  val #-> : ('a -> 'c * 'b) * ('c -> 'b -> 'd) -> 'a -> 'd
  val #>> : ('a -> 'c * 'b) * ('c -> 'd) -> 'a -> 'd * 'b
  val ##> : ('a -> 'c * 'b) * ('b -> 'd) -> 'a -> 'c * 'd
  val ##>> : ('a -> 'c * 'b) * ('b -> 'e * 'd) -> 'a -> ('c * 'e) * 'd
  val ` : ('b -> 'a) -> 'b -> 'a * 'b
  val tap: ('b -> 'a) -> 'b -> 'b

  (*options*)
  val is_some: 'a option -> bool
  val is_none: 'a option -> bool
  val the: 'a option -> 'a
  val these: 'a list option -> 'a list
  val the_list: 'a option -> 'a list
  val the_default: 'a -> 'a option -> 'a
  val perhaps: ('a -> 'a option) -> 'a -> 'a
  val merge_options: 'a option * 'a option -> 'a option
  val eq_option: ('a * 'b -> bool) -> 'a option * 'b option -> bool

  (*partiality*)
  (*
  val try: ('a -> 'b) -> 'a -> 'b option
  val can: ('a -> 'b) -> 'a -> bool*)

  (*lists*)
  val cons: 'a -> 'a list -> 'a list
  val append: 'a list -> 'a list -> 'a list
  val fold: ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val fold_rev: ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val fold_map: ('a -> 'b -> 'c * 'b) -> 'a list -> 'b -> 'c list * 'b
end;

structure Basics: BASICS =
struct

(* functions *)

(*application and structured results*)
fun x |> f = f x;
fun (x, y) |-> f = f x y;
fun (x, y) |>> f = (f x, y);
fun (x, y) ||> f = (x, f y);
fun (x, y) ||>> f = let val (z, y') = f y in ((x, z), y') end;

(*composition and structured results*)
fun (f #> g) x   = x |> f |> g;
fun (f #-> g) x  = x |> f |-> g;
fun (f #>> g) x  = x |> f |>> g;
fun (f ##> g) x  = x |> f ||> g;
fun (f ##>> g) x = x |> f ||>> g;

(*result views*)
fun `f = fn x => (f x, x);
fun tap f = fn x => (f x; x);


(* options *)

fun is_some (SOME _) = true
  | is_some NONE = false;

fun is_none (SOME _) = false
  | is_none NONE = true;

fun the (SOME x) = x
  | the NONE = raise Option.Option;

fun these (SOME x) = x
  | these NONE = [];

fun the_list (SOME x) = [x]
  | the_list NONE = []

fun the_default x (SOME y) = y
  | the_default x NONE = x;

fun perhaps f x = the_default x (f x);

fun merge_options (x, y) = if is_some x then x else y;

fun eq_option eq (SOME x, SOME y) = eq (x, y)
  | eq_option _ (NONE, NONE) = true
  | eq_option _ _ = false;


(* partiality *)
(*)
fun try f x = SOME (f x)
  handle exn => if Exn.is_interrupt exn then Exn.reraise exn else NONE;

fun can f x = is_some (try f x);*)


(* lists *)

fun cons x xs = x :: xs;

fun append xs ys = xs @ ys;

fun fold _ [] y = y
  | fold f (x :: xs) y = fold f xs (f x y);

fun fold_rev _ [] y = y
  | fold_rev f (x :: xs) y = f x (fold_rev f xs y);

fun fold_map _ [] y = ([], y)
  | fold_map f (x :: xs) y =
      let
        val (x', y') = f x y;
        val (xs', y'') = fold_map f xs y';
      in (x' :: xs', y'') end;

end;

open Basics;


(*  Title:      Pure/General/seq.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Author:     Markus Wenzel, TU Munich
    Author:     Daniel Raggi (2021), Cambridge University Computer Laboratory

Unbounded sequences implemented by closures.  RECOMPUTES if sequence
is re-inspected.  Memoing, using polymorphic refs, was found to be
slower!  (More GCs)
*)

signature SEQ =
sig
  type 'a seq
  val make: (unit -> ('a * 'a seq) option) -> 'a seq
  val pull: 'a seq -> ('a * 'a seq) option
  val empty: 'a seq
  val cons: 'a -> 'a seq -> 'a seq
  val single: 'a -> 'a seq
  (*val try: ('a -> 'b) -> 'a -> 'b seq*)
  val hd: 'a seq -> 'a
  val tl: 'a seq -> 'a seq
  val chop: int -> 'a seq -> 'a list * 'a seq
  val take: int -> 'a seq -> 'a seq
  val list_of: 'a seq -> 'a list
  val of_list: 'a list -> 'a seq
  val append: 'a seq -> 'a seq -> 'a seq
  val mapp: ('a -> 'b) -> 'a seq -> 'b seq -> 'b seq
  val interleave: 'a seq * 'a seq -> 'a seq
  val filter: ('a -> bool) -> 'a seq -> 'a seq
  val flat: 'a seq seq -> 'a seq
  val map: ('a -> 'b) -> 'a seq -> 'b seq
  val maps: ('a -> 'b seq) -> 'a seq -> 'b seq
  val map_filter: ('a -> 'b option) -> 'a seq -> 'b seq
  val lift: ('a -> 'b -> 'c) -> 'a seq -> 'b -> 'c seq
  val lifts: ('a -> 'b -> 'c seq) -> 'a seq -> 'b -> 'c seq
  val singleton: ('a list -> 'b list seq) -> 'a -> 'b seq
  (*val print: (int -> 'a -> unit) -> int -> 'a seq -> unit*)
  val it_right : ('a * 'b seq -> 'b seq) -> 'a seq * 'b seq -> 'b seq
  datatype 'a result = Result of 'a | Error of unit -> string
  val make_results: 'a seq -> 'a result seq
  val filter_results: 'a result seq -> 'a seq
  val maps_results: ('a -> 'b result seq) -> 'a result seq -> 'b result seq
  val maps_result: ('a -> 'b seq) -> 'a result seq -> 'b result seq
  val map_result: ('a -> 'b) -> 'a result seq -> 'b result seq
  (*)
  val first_result: string -> 'a result seq -> 'a * 'a seq
  val the_result: string -> 'a result seq -> 'a*)
  val succeed: 'a -> 'a seq
  val fail: 'a -> 'b seq
  val THEN: ('a -> 'b seq) * ('b -> 'c seq) -> 'a -> 'c seq
  val ORELSE: ('a -> 'b seq) * ('a -> 'b seq) -> 'a -> 'b seq
  val APPEND: ('a -> 'b seq) * ('a -> 'b seq) -> 'a -> 'b seq
  val EVERY: ('a -> 'a seq) list -> 'a -> 'a seq
  val FIRST: ('a -> 'b seq) list -> 'a -> 'b seq
  val TRY: ('a -> 'a seq) -> 'a -> 'a seq
  val REPEAT: ('a -> 'a seq) -> 'a -> 'a seq
  val REPEAT1: ('a -> 'a seq) -> 'a -> 'a seq
  val INTERVAL: (int -> 'a -> 'a seq) -> int -> int -> 'a -> 'a seq
  val DETERM: ('a -> 'b seq) -> 'a -> 'b seq
  (*added by draggi*)
  val insert : 'a -> 'a seq -> ('a * 'a -> order) -> 'a seq
  val sort : 'a seq -> ('a * 'a -> order) -> 'a seq
  val insertMany : 'a seq -> 'a seq -> ('a * 'a -> order) -> 'a seq
  val insertNoRepetition : 'a -> 'a seq -> ('a * 'a -> order) -> ('a * 'a -> bool) -> 'a seq
  val insertNoRepetitionLimited : 'a -> 'a seq -> ('a * 'a -> order) -> ('a * 'a -> bool) -> int -> 'a seq
  val insertManyNoRepetition : 'a seq -> 'a seq -> ('a * 'a -> order) -> ('a * 'a -> bool) -> 'a seq
  val insertManyNoRepetitionLimited : 'a seq -> 'a seq -> ('a * 'a -> order) -> ('a * 'a -> bool) -> int -> 'a seq
  val findFirst : ('a -> bool) -> 'a seq -> 'a option
  val exists : ('a -> bool) -> 'a seq -> bool
end;

structure Seq: SEQ =
struct


(** lazy sequences **)

datatype 'a seq = Seq of unit -> ('a * 'a seq) option;

(*the abstraction for making a sequence*)
val make = Seq;

(*return next sequence element as NONE or SOME (x, xq)*)
fun pull (Seq f) = f ();


(*the empty sequence*)
val empty = Seq (fn () => NONE);

(*prefix an element to the sequence -- use cons (x, xq) only if
  evaluation of xq need not be delayed, otherwise use
  make (fn () => SOME (x, xq))*)
fun cons x xq = make (fn () => SOME (x, xq));

fun single x = cons x empty;

(*head and tail -- beware of calling the sequence function twice!!*)
fun hd xq = #1 (Option.valOf (pull xq))
and tl xq = #2 (Option.valOf (pull xq));

(*)
(*partial function as procedure*)
fun try f x =
  (case Basics.try f x of
    SOME y => single y
  | NONE => empty);


(*the list of the first n elements, paired with rest of sequence;
  if length of list is less than n, then sequence had less than n elements*)
fun chop n xq =
  if n <= (0 : int) then ([], xq)
  else
    (case pull xq of
      NONE => ([], xq)
    | SOME (x, xq') => apfst (Basics.cons x) (chop (n - 1) xq'));
    *)

(*truncate the sequence after n elements*)
(*)
fun take n xq =
  if n <= (0 : int) then empty
  else make (fn () =>
    (Option.map o apsnd) (take (n - 1)) (pull xq));*)
exception Negative
fun chop 0 xq = ([],xq)
  | chop n xq =
    if n < 0 then raise Negative else
      (case pull xq of
        NONE => ([],empty)
      | SOME (x, xq') => let val (wL,wS) = chop (n-1) xq' in (x::wL,wS) end);
fun take 0 xq = empty
  | take n xq =
      if n < 0 then raise Negative else
        make (fn () =>
          (case pull xq of
              NONE => NONE
            | SOME (x, xq') => SOME (x, take (n-1) xq')));

(*conversion from sequence to list*)
fun list_of xq =
  (case pull xq of
    NONE => []
  | SOME (x, xq') => x :: list_of xq');

(*conversion from list to sequence*)
fun of_list xs = fold_rev cons xs empty;


(*sequence append: put the elements of xq in front of those of yq*)
fun append xq yq =
  let
    fun copy s =
      make (fn () =>
        (case pull s of
          NONE => pull yq
        | SOME (x, s') => SOME (x, copy s')))
  in copy xq end;

(*map over a sequence xq, append the sequence yq*)
fun mapp f xq yq =
  let
    fun copy s =
      make (fn () =>
        (case pull s of
          NONE => pull yq
        | SOME (x, s') => SOME (f x, copy s')))
  in copy xq end;

(*interleave elements of xq with those of yq -- fairer than append*)
fun interleave (xq, yq) =
  make (fn () =>
    (case pull xq of
      NONE => pull yq
    | SOME (x, xq') => SOME (x, interleave (yq, xq'))));

(*filter sequence by predicate*)
fun filter pred xq =
  let
    fun copy s =
      make (fn () =>
        (case pull s of
          NONE => NONE
        | SOME (x, s') => if pred x then SOME (x, copy s') else pull (copy s')));
  in copy xq end;

(*flatten a sequence of sequences to a single sequence*)
fun flat xqq =
  make (fn () =>
    (case pull xqq of
      NONE => NONE
    | SOME (xq, xqq') => pull (append xq (flat xqq'))));

(*map the function f over the sequence, making a new sequence*)
fun map f xq =
  make (fn () =>
    (case pull xq of
      NONE => NONE
    | SOME (x, xq') => SOME (f x, map f xq')));

fun maps f xq =
  make (fn () =>
    (case pull xq of
      NONE => NONE
    | SOME (x, xq') => pull (append (f x) (maps f xq'))));

fun map_filter f = maps (fn x => (case f x of NONE => empty | SOME y => single y));

fun lift f xq y = map (fn x => f x y) xq;
fun lifts f xq y = maps (fn x => f x y) xq;

fun singleton f x = f [x] |> map (fn [y] => y | _ => raise List.Empty);

(*)
(*print a sequence, up to "count" elements*)
fun print print_elem count =
  let
    fun prnt (k: int) xq =
      if k > count then ()
      else
        (case pull xq of
          NONE => ()
        | SOME (x, xq') => (print_elem k x; writeln ""; prnt (k + 1) xq'));
  in prnt 1 end;*)

(*accumulating a function over a sequence; this is lazy*)
fun it_right f (xq, yq) =
  let
    fun its s =
      make (fn () =>
        (case pull s of
          NONE => pull yq
        | SOME (a, s') => pull (f (a, its s'))))
  in its xq end;


(* embedded errors *)

datatype 'a result = Result of 'a | Error of unit -> string;

fun make_results xq = map Result xq;
fun filter_results xq = map_filter (fn Result x => SOME x | Error _ => NONE) xq;

fun maps_results f xq =
  make (fn () =>
    (case pull xq of
      NONE => NONE
    | SOME (Result x, xq') => pull (append (f x) (maps_results f xq'))
    | SOME (Error msg, xq') => SOME (Error msg, maps_results f xq')));

fun maps_result f = maps_results (map Result o f);
fun map_result f = maps_result (single o f);

(*)
(*first result or first error within sequence*)
fun first_result default_msg seq =
  let
    fun result opt_msg xq =
      (case (opt_msg, pull xq) of
        (_, SOME (Result x, xq')) => (x, filter_results xq')
      | (SOME _, SOME (Error _, xq')) => result opt_msg xq'
      | (NONE, SOME (Error msg, xq')) => result (SOME msg) xq'
      | (SOME msg, NONE) => error (msg ())
      | (NONE, NONE) => error (if default_msg = "" then "Empty result sequence" else default_msg));
  in result NONE seq end;

fun the_result default_msg seq = #1 (first_result default_msg seq);
*)


(** sequence functions **)      (*cf. Pure/tactical.ML*)

fun succeed x = single x;
fun fail _ = empty;

fun op THEN (f, g) x = maps g (f x);

fun op ORELSE (f, g) x =
  (case pull (f x) of
    NONE => g x
  | some => make (fn () => some));

fun op APPEND (f, g) x =
  append (f x) (make (fn () => pull (g x)));


fun EVERY fs = fold_rev (curry op THEN) fs succeed;
fun FIRST fs = fold_rev (curry op ORELSE) fs fail;

fun TRY f = ORELSE (f, succeed);

fun REPEAT f =
  let
    fun rep qs x =
      (case pull (f x) of
        NONE => SOME (x, make (fn () => repq qs))
      | SOME (x', q) => rep (q :: qs) x')
    and repq [] = NONE
      | repq (q :: qs) =
          (case pull q of
            NONE => repq qs
          | SOME (x, q) => rep (q :: qs) x);
  in fn x => make (fn () => rep [] x) end;

fun REPEAT1 f = THEN (f, REPEAT f);

fun INTERVAL f (i: int) j x =
  if i > j then single x
  else op THEN (f j, INTERVAL f i (j - 1)) x;

fun DETERM f x =
  (case pull (f x) of
    NONE => empty
  | SOME (x', _) => cons x' empty);

fun insert x xq f =
  make (fn () =>
    case pull xq of
      NONE => SOME (x,empty)
    | SOME (x',q) => if f(x,x') = GREATER then SOME (x',insert x q f) else SOME (x,xq));

fun sort xq f =
  case pull xq of
    NONE => empty
  | SOME (x,q) => insert x (sort q f) f;


fun insertNoRepetition x xq f eq =
  make (fn () =>
    case pull xq of
      NONE => SOME (x,empty)
    | SOME (x',q) => if f(x,x') = GREATER then SOME (x',insertNoRepetition x q f eq)
                     else if f(x,x') = LESS then SOME (x,xq)
                     else if eq(x,x') then SOME (x',q)
                          else SOME (x',insertNoRepetition x q f eq));

fun insertNoRepetitionLimited x xq f eq n =
  let
    fun inrl xx xxq i =
      make (fn () =>
        if i = n then NONE else
          case pull xxq of
            NONE => SOME (xx,empty)
          | SOME (x',q) => if f(xx,x') = GREATER then SOME (x',insertNoRepetitionLimited xx q f eq (i+1))
                           else if f(xx,x') = LESS then SOME (xx,xxq)
                           else if eq(xx,x') then SOME (x',q)
                                else SOME (x',insertNoRepetitionLimited xx q f eq (i+1)));
  in inrl x xq 0
  end

fun insertMany xq yq f =
  (case pull xq of
    NONE => yq
  | SOME (x,q) => insert x (insertMany q yq f) f);

fun insertManyNoRepetition xq yq f eq =
  (case pull xq of
    NONE => yq
  | SOME (x,q) => insertNoRepetition x (insertManyNoRepetition q yq f eq) f eq);

fun insertManyNoRepetitionLimited xq yq f eq n =
  (case pull xq of
    NONE => yq
  | SOME (x,q) => insertNoRepetitionLimited x (insertManyNoRepetitionLimited q yq f eq n) f eq n);

fun findFirst f xq =
  (case pull xq of
    NONE => NONE
  | SOME (x,q) => if f x then SOME x else findFirst f q);

fun exists f xq = case findFirst f xq of NONE => false | SOME _ => true;

fun fiterThenMap f m xq =
  make (fn () =>
    (case pull xq of
      NONE => NONE
    | SOME (x, xq') => if f x then SOME (m x, fiterThenMap f m xq') else pull (fiterThenMap f m xq')));
end;
