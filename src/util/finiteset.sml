signature FINITESET =
sig
  type ''a set
  val ofList : ''a list -> ''a set;
  val listOf : ''a set -> ''a list;
  val elementOf : ''a -> ''a set -> bool;
  val minus : ''a set -> ''a set -> ''a set;
  val union : ''a set -> ''a set -> ''a set;
  val intersection : ''a set -> ''a set -> ''a set;
  val filter : (''a -> bool) -> ''a set -> ''a set;
  val all : (''a -> bool) -> ''a set -> bool;
  val exists :  (''a -> bool) -> ''a set -> bool;
  val find : (''a -> bool) -> ''a set -> ''a option;
  val map : (''a -> ''b) -> ''a set -> ''b set;
  val toSeq : ''a set -> ''a Seq.seq
end;

structure FiniteSet : FINITESET =
struct
  type 'a set = 'a list;

  val empty = [];
  fun ofList (n::ns) = n :: List.filter (fn x => not (x = n)) (ofList ns)
    | ofList [] = empty
  fun listOf L = L;

  fun elementOf x S = List.exists (fn y => x = y) S
  fun minus S1 S2 = List.filter (fn x => not (List.exists (fn y => x = y) S2)) S1
  fun intersection S1 S2 = List.filter (fn x => (List.exists (fn y => x = y) S1)) S2
  fun union S1 S2 = S1 @ (minus S2 S1)
  val filter = List.filter
  val all = List.all
  val exists = List.exists
  val find = List.find
  val map = List.map
  val toSeq = Seq.of_list
end;
