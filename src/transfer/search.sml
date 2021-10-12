import "util.sequence";

signature SEARCH =
sig
  val depthFirst : ('a -> 'a Seq.seq) -> int -> 'a -> 'a Seq.seq;
  val graphDepthFirst : ('a -> 'a Seq.seq) -> ('a * 'a -> bool) -> int -> 'a -> 'a Seq.seq;
  val graphDepthFirstSorting : ('a -> 'a Seq.seq) -> ('a * 'a -> order) -> ('a * 'a -> bool) -> int -> 'a -> 'a Seq.seq;
end;

structure Search : SEARCH =
struct

  fun depthFirst next n state =
    let fun df s i =
          if i < n then
            (case Seq.pull s of
              NONE => s
            | SOME (st,s') => case Seq.pull (next st) of
                                  NONE => Seq.make (fn () => SOME (st,df s' (i+1)))
                                | SOME (st',s'') => df (Seq.make (fn () => SOME (st', Seq.append s'' (Seq.make (fn () => (SOME (st,s'))))))) (i+1) )
          else s
    in df (Seq.single state) 0
    end

  fun graphDepthFirst next eq n state =
    let fun gdf s i acc =
          if i < n then
            (case Seq.pull s of
              NONE => (s,s)
            | SOME (st,s') =>
                if List.exists (fn x => eq (x,st)) acc then
                  gdf s' i acc
                else
                  (case Seq.pull (next st) of
                      NONE => let val (new,old) = gdf s' i (st::acc)
                              in (new,Seq.append (Seq.single st) old) end
                    | SOME (st',s'') => let val (new,old) = gdf (Seq.make (fn () => SOME (st', Seq.append s'' s'))) (i+1) (st::acc)
                                        in (new, Seq.append old (Seq.single st)) end))
          else (Seq.empty,s)
        val (new,old) = gdf (Seq.single state) 0 []
    in Seq.append new old
    end

  fun graphDepthFirstSorting next h eq n state =
    let fun gdf s i acc =
          if i < n then
            (case Seq.pull s of
              NONE => (s,s)
            | SOME (st,s') =>
                if List.exists (fn x => eq (x,st)) acc then
                  gdf s' (i+1) acc
                else
                  (case Seq.pull (next st) of
                      NONE => let val (new,old) = gdf s' (i+1) (st::acc)
                              in (new,Seq.insert st old h) end
                    | SOME (st',s'') => let val (new,old) = gdf (Seq.make (fn () => SOME (st', Seq.append s'' s'))) (i+1) (st::acc)
                                        in (new, Seq.insert st old h) end))
          else (Seq.empty,s)
        val (new,old) = gdf (Seq.single state) 0 []
    in Seq.append new old
    end

end;
