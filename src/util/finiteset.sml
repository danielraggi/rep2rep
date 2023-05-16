import "util.sequence";
import "util.rpc";

signature FINITESET =
sig
  type ''a set
  val set_rpc: ''a Rpc.Datatype.t -> ''a set Rpc.Datatype.t;
  val empty : ''a set;
  val ofList : ''a list -> ''a set;
  val ofListEq : (''a * ''a -> bool) -> ''a list -> ''a set;
  val ofListQuick : ''a list -> ''a set;
  val listOf : ''a set -> ''a list;
  val elementOf : ''a -> ''a set -> bool;
  val insert : ''a -> ''a set -> ''a set;
  val singleton : ''a -> ''a set;
  val minus : ''a set -> ''a set -> ''a set;
  val union : ''a set -> ''a set -> ''a set;
  val intersection : ''a set -> ''a set -> ''a set;
  val filter : (''a -> bool) -> ''a set -> ''a set;
  val all : (''a -> bool) -> ''a set -> bool;
  val exists :  (''a -> bool) -> ''a set -> bool;
  val find : (''a -> bool) -> ''a set -> ''a option;
  val map : (''a -> ''b) -> ''a set -> ''b set;
  val maps : (''a -> ''b set) -> ''a set -> ''b set;
  val toSeq : ''a set -> ''a Seq.seq
  val pull : ''a set -> ''a * ''a set;
  val isEmpty : ''a set -> bool;
  val size : ''a set -> int;
end;

structure FiniteSet : FINITESET =
struct
  type 'a set = 'a list;

  fun set_rpc a_rpc = Rpc.Datatype.alias
                          ((Rpc.Datatype.name a_rpc) ^ " FiniteSet.set")
                          (List.list_rpc a_rpc);

  val empty = [];
  fun ofList (n::ns) = n :: List.filter (fn x => not (x = n)) (ofList ns)
    | ofList [] = empty;
  fun ofListEq eq (n::ns) = n :: List.filter (fn x => not (eq (x, n))) (ofList ns)
    | ofListEq _ [] = empty

  (*the following assumes L has no duplicates *)
  fun ofListQuick L = L;
  fun listOf L = L;

  fun elementOf x S = List.exists (fn y => x = y) S

  fun insert x S = if elementOf x S then S else x :: S
  fun singleton x = [x]
  fun minus S1 S2 = List.filter (fn x => not (List.exists (fn y => x = y) S2)) S1
  fun intersection S1 S2 = List.filter (fn x => (List.exists (fn y => x = y) S1)) S2
  fun union S1 S2 = S1 @ (minus S2 S1)
  val filter = List.filter
  val all = List.all
  val exists = List.exists
  val find = List.find
  fun map f = ofList o (List.map f)
  fun maps f = ofList o (List.maps f)
  val toSeq = Seq.of_list

  fun pull x = (hd x, tl x)
  val isEmpty = null
  val size = length
end;

(*

set.sml

Provide a set structure for use throughout robin. Sets are backed by
dictionaries: the values are stored as keys, all associated with unit.
This means any improvements made to the dictionary data structure are
automatically inherited by the set structure.

*)

import "util.dictionary";


(* An abstract interface for what a set can do. *)
signature ISET =
sig
    type t;
    type 'a set;

    val empty : unit -> t set;
    val fromList : t list -> t set;
    val toList : t set -> t list;
    val toString : t set -> string;

    val insert : t set -> t -> t set;
    val remove : t set -> t -> unit;

    val union : t set -> t set -> t set;
    val intersection : t set -> t set -> t set;
    val difference : t set -> t set -> t set;

    val unionAll : t set list -> t set;
    val intersectionAll : t set list -> t set;

    val map : (t -> 'a) -> t set -> 'a list;
    val endomap : (t -> t) -> t set -> t set;
    val filter : (t -> bool) -> t set -> t set;
    val foldl : (t * 'a -> 'a) -> 'a -> t set -> 'a;
    val foldr : (t * 'a -> 'a) -> 'a -> t set -> 'a;
    val find : (t -> bool) -> t set -> t option;

    val size : t set -> int;

    val equal : t set * t set -> bool;
    val isEmpty : t set -> bool;
    val contains : t set -> t -> bool;
    val subset : t set -> t set -> bool;

    val getFirst : t set -> t;
end;



(* A functor to create set structures.
   We use a functor so that different sets will "just work" for
   different types. In this case any structure that has compare will
   work fine.
 *)
functor FiniteSet(O :
            sig
                type t;
                val compare : t * t -> order;
                val toString : t -> string;
            end
           ) :> ISET where type t = O.t =
struct

type t = O.t;
structure D = Dictionary(struct
                          type k = t;
                          val compare = O.compare;
                          val toString = O.toString;
                          end);
type 'a set = ('a, unit) D.dict;

val empty = D.empty;
fun fromList xs = D.fromPairList (map (fn x => (x, ())) xs);
fun toList xs = map (fn (x,_) => x) (D.toPairList xs);
fun toString items =
    let
        val printThreshold = 100;
        val stringItems = D.map (fn (k, _) => O.toString k) items;
        val tooLong = (D.size items) > printThreshold;
        val mostItems = if tooLong
                        then (List.take (stringItems, printThreshold))
                        else stringItems;
        val joined = String.concatWith ", " mostItems;
    in
        "{" ^ joined ^ (if tooLong then "..." else "") ^ "}"
    end;


fun insert xs x = D.insert xs (x, ());
fun remove xs x = D.remove xs x;

fun union xs ys = D.unionWith (fn (_, _, _) => ()) xs ys;
fun intersection xs ys = D.intersectionWith (fn (_, _, _) => ()) xs ys;
fun difference xs ys = (* D.foldl (fn ((v,_), s) => (remove s v)) xs ys; *)
    let
        val xs' = toList xs;
        val ys' = toList ys;
        fun remove [] _ = []
          | remove (z::zs) k = if O.compare(z,k) = EQUAL then zs
                               else if O.compare(z,k) = LESS then z::(remove zs k)
                               else zs; (* Already past where it would be *)
        val result = foldr (fn (v, st) => remove st v) xs' ys';
    in
        fromList result
    end;

fun unionAll xs = D.unionAllWith (fn (_, _, _) => ()) xs;
fun intersectionAll xs = D.intersectionAllWith (fn (_, _, _) => ()) xs;

fun map f xs = D.map (fn (k, v) => f k) xs;
fun endomap f xs = fromList (map f xs);
fun filter f xs = D.filter (fn (k, v) => f k) xs;
fun foldl f s xs = D.foldl (fn ((k, v), x) => f(k, x)) s xs;
fun foldr f s xs = D.foldr (fn ((k, v), x) => f (k, x)) s xs;
fun find p xs = Option.map #1 (D.find (fn (k, v) => p k) xs);

fun size xs = D.size xs;

fun equal (xs, ys) = D.equal (xs, ys);
fun isEmpty xs = D.isEmpty xs;
fun contains xs x =
  (case D.get xs x of
      NONE => false
    | SOME _ => true)
fun subset xs ys =
    let val contained = fn x => contains ys x;
    in List.all contained (toList xs) end;

fun getFirst xs = #1 (D.getFirst xs);

end;
