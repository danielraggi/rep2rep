(*

set.sml

Provide a set structure for use throughout robin. Sets are backed by
dictionaries: the values are stored as keys, all associated with unit.
This means any improvements made to the dictionary data structure are
automatically inherited by the set structure.

*)

import "util.dictionary";


(* An abstract interface for what a set can do. *)
signature SET =
sig
    type t;
    type 'a set;

    val empty : unit -> t set;
    val fromList : t list -> t set;
    val toList : t set -> t list;
    val toString : t set -> string;

    val insert : t set -> t -> unit;
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
functor Set(O :
            sig
                type t;
                val compare : t * t -> order;
                val fmt : t -> string;
            end
           ) :> SET where type t = O.t =
struct

type t = O.t;
structure D = Dictionary(struct
                          type k = t;
                          val compare = O.compare;
                          val fmt = O.fmt;
                          end);
type 'a set = ('a, unit) D.dict;

val empty = D.empty;
fun fromList xs = D.fromPairList (map (fn x => (x, ())) xs);
fun toList xs = map (fn (x,_) => x) (D.toPairList xs);
fun toString items =
    let
        val printThreshold = 100;
        val stringItems = D.map (fn (k, _) => O.fmt k) items;
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
    let val v = D.get xs x
    in true end
    handle KeyError => false;
fun subset xs ys =
    let val contained = fn x => contains ys x;
    in List.all contained (toList xs) end;

fun getFirst xs = #1 (D.getFirst xs);

end;
