import "util.finiteset";

signature SET =
sig
  type ''a set(*)
  val compare : ''a set * ''a set -> order;*)
  val elementOf : ''a -> ''a set -> bool;
  val empty : ''a set;
  val make : (''a -> bool) -> ''a set;
  val ofList : ''a list -> ''a set;
  val ofFiniteSet : ''a FiniteSet.set -> ''a set;

  val minus : ''a set -> ''a set -> ''a set;
  val union : ''a set -> ''a set -> ''a set;
  val intersection : ''a set -> ''a set -> ''a set;
  val filter : (''a -> bool) -> ''a set -> ''a set;
end;

structure Set : SET =
struct
  type 'a set = 'a -> bool;

  fun elementOf x S = S x;
  val empty = fn _ => false;
  fun ofList L = fn x => List.exists (fn y => x = y) L
  fun ofFiniteSet F = fn x => FiniteSet.exists (fn s => x = s) F
  fun make x = x

  fun minus S1 S2 = fn x => S1 x andalso not (S2 x)
  fun intersection S1 S2 = fn x => S1 x andalso S2 x
  fun union S1 S2 = fn x => S1 x orelse S2 x
  fun filter f S = intersection S (make f)

end;
