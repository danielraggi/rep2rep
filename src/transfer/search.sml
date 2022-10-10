import "util.sequence";

signature SEARCH =
sig
  val depthFirst : ('a -> 'a Seq.seq) -> int -> 'a -> 'a Seq.seq;
  val graphDepthFirst : ('a -> 'a Seq.seq) -> ('a * 'a -> bool) -> int -> 'a -> 'a Seq.seq;
  val depthFirstSortAndIgnore : ('a -> 'a Seq.seq) -> ('a * 'a -> order) -> ('a * 'a list -> bool) -> 'a -> 'a Seq.seq;
  val depthFirstSortIgnoreForget : ('a -> 'a Seq.seq) -> ('a * 'a -> order) -> ('a * 'a list -> bool) -> ('a * 'a list -> bool) -> 'a -> 'a Seq.seq;
  val breadthFirstSortAndIgnore : ('a -> 'a Seq.seq) -> ('a * 'a -> order) -> ('a * 'a list -> bool) -> 'a -> 'a Seq.seq;
  val breadthFirstSortIgnoreForget : ('a -> 'a Seq.seq) -> ('a * 'a -> order) -> ('a * 'a list -> bool) -> ('a * 'a list -> bool) -> 'a -> 'a Seq.seq;
  val bestFirstSortAndIgnore : ('a -> 'a Seq.seq) -> ('a * 'a -> order) -> ('a * 'a list -> bool) -> 'a -> 'a Seq.seq;
  val bestFirstSortIgnoreForget : ('a -> 'a Seq.seq) -> ('a * 'a -> order) -> ('a * 'a list -> bool) -> ('a * 'a list -> bool) -> 'a -> 'a Seq.seq;
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
              NONE => s
            | SOME (st,s') =>
                if List.exists (fn x => eq (x,st)) acc then
                  gdf s' i acc
                else
                  (case Seq.pull (next st) of
                      NONE => let val visited = gdf s' i (st::acc)
                              in Seq.append (Seq.single st) visited end
                    | SOME (st',s'') => let val visited = gdf (Seq.make (fn () => SOME (st', Seq.append s'' s'))) (i+1) (st::acc)
                                        in Seq.append visited (Seq.single st) end))
          else s
    in gdf (Seq.single state) 0 []
    end

  fun depthFirstSortAndIgnore next h ign state =
    let fun dfsi frontier acc =
          (case Seq.pull frontier of
            NONE => Seq.empty
          | SOME (st,s') =>
              if ign (st,acc) then
                dfsi s' acc
              else
                (case Seq.pull (next st) of
                    NONE => let val recdfsi = dfsi s' (st::acc)
                            in Seq.insert st recdfsi h end
                  | SOME (st',s'') => let val newFrontier = Seq.append (Seq.cons st' s'') s'
                                          val recdfsi = dfsi newFrontier (st::acc)
                                      in Seq.insert st recdfsi h end))
    in dfsi (Seq.single state) []
    end

  fun depthFirstSortIgnoreForget next h ign forg state =
    let fun dfsi frontier acc =
          (case Seq.pull frontier of
            NONE => Seq.empty
          | SOME (st,s') =>
              if ign (st,acc) then
                dfsi s' acc
              else
                (case Seq.pull (next st) of
                    NONE => let val recdfsi = dfsi s' (st::acc)
                            in if forg (st,acc) then recdfsi else Seq.insert st recdfsi h end
                  | SOME (st',s'') => let val newFrontier = Seq.append (Seq.cons st' s'') s'
                                          val recdfsi = dfsi newFrontier (st::acc)
                                      in if forg (st,acc) then recdfsi else Seq.insert st recdfsi h end))
    in dfsi (Seq.single state) []
    end

  fun breadthFirstSortAndIgnore next h ign state =
    let fun dfsi frontier acc =
          (case Seq.pull frontier of
            NONE => Seq.empty
          | SOME (st,s') =>
              if ign (st,acc) then
                dfsi s' acc
              else
                (case Seq.pull (next st) of
                    NONE => let val recdfsi = dfsi s' (st::acc)
                            in Seq.insert st recdfsi h end
                  | SOME (st',s'') => let val newFrontier = Seq.append s' (Seq.cons st' s'')
                                          val recdfsi = dfsi newFrontier (st::acc)
                                      in Seq.insert st recdfsi h end))
    in dfsi (Seq.single state) []
    end

  fun breadthFirstSortIgnoreForget next h ign forg state =
    let fun dfsi frontier acc =
          (case Seq.pull frontier of
            NONE => Seq.empty
          | SOME (st,s') =>
              if ign (st,acc) then
                dfsi s' acc
              else
                (case Seq.pull (next st) of
                    NONE => let val recdfsi = dfsi s' (st::acc)
                            in if forg (st,acc) then recdfsi else Seq.insert st recdfsi h end
                  | SOME (st',s'') => let val newFrontier = Seq.append s' (Seq.cons st' s'')
                                          val recdfsi = dfsi newFrontier (st::acc)
                                      in if forg (st,acc) then recdfsi else Seq.insert st recdfsi h end))
    in dfsi (Seq.single state) []
    end

  fun bestFirstSortAndIgnore next h ign state =
    let fun dfsi frontier acc =
          (case Seq.pull frontier of
            NONE => Seq.empty
          | SOME (st,s') =>
              if ign (st,acc) then
                dfsi s' acc
              else
                (case Seq.pull (next st) of
                    NONE => let val recdfsi = dfsi s' (st::acc)
                            in Seq.insert st recdfsi h end
                  | SOME (st',s'') => let val newFrontier = Seq.insertMany s'' (Seq.insert st' s' h) h
                                          val recdfsi = dfsi newFrontier (st::acc)
                                      in Seq.insert st recdfsi h end))
    in dfsi (Seq.single state) []
    end

  fun bestFirstSortIgnoreForget next h ign forg state =
    let fun dfsi frontier acc =
          (case Seq.pull frontier of
            NONE => Seq.empty
          | SOME (st,s') =>
              if ign (st,acc) then
                dfsi s' acc
              else
                (case Seq.pull (next st) of
                    NONE => let val recdfsi = dfsi s' (st::acc)
                            in if forg (st,acc) then recdfsi else Seq.insert st recdfsi h end
                  | SOME (st',s'') => let val newFrontier = Seq.insertMany s'' (Seq.insert st' s' h) h
                                          val recdfsi = dfsi newFrontier (st::acc)
                                      in if forg (st,acc) then recdfsi else Seq.insert st recdfsi h end))
    in dfsi (Seq.single state) []
    end

end;
