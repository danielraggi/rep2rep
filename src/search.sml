import "util.sequence";

signature SEARCH =
sig
  val sort : ('a -> 'a Seq.seq) -> ('a * 'a -> order) -> int -> 'a -> 'a Seq.seq;
  val sortNoRepetition : ('a -> 'a Seq.seq) -> ('a * 'a -> order) -> ('a * 'a -> bool) -> int -> 'a -> 'a Seq.seq;
end;

structure Search : SEARCH =
struct

(* I think that if the next function returns an ordered sequence,
performance of sort should be much better *)
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

  fun sortNoRepetition next h eq n state =
    let
      fun sort' new old i =
        if i < n then
          case Seq.pull new of
            NONE => (new,old)
          | SOME (x, q) => sort' (Seq.insertManyNoRepetition (next x) q h eq) (Seq.insertNoRepetition x old h eq) (i+1)
        else (new,old)
      val (x,y) = sort' (Seq.single state) Seq.empty 0
    in
      Seq.insertManyNoRepetition x y h eq
    end;

end;
