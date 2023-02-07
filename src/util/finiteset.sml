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
  val map = List.map
  val maps = List.maps
  val toSeq = Seq.of_list

  fun pull x = (hd x, tl x)
  val isEmpty = null
  val size = length
end;
