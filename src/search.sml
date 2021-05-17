import "util.sequence";
import "state";

signature SEARCH =
sig
  type state;
  val sort : (state -> state Seq.seq) -> (state * state -> order) -> int -> state -> state Seq.seq;
end;

structure Search : SEARCH =
struct
  type state = State.T;

(* I think that if the next function returns an ordered sequence, performance of sort should be much better*)
fun sort next h n state =
  let
    fun sort' new old i =
      if i < n then
        case Seq.pull new of
          NONE => (new,old)
        | SOME (x, q) => sort' (Seq.insertMany (next x) q h) (Seq.insert x old h) (i+1)
      else (new,old)
    val (x,y) = sort' (Seq.single state) Seq.empty 0
  in
    Seq.insertMany x y h
  end;

end;
