import "util.sequence";

signature SEARCH =
sig
  val depthFirstIgnore : ('a -> 'a Seq.seq) -> ('a * 'a list -> bool) -> ('a -> bool) -> 'a -> 'a Seq.seq;
  val depthFirstAll : ('a -> 'a Seq.seq) -> ('a * 'a list -> bool) -> ('a * 'a list -> bool) -> ('a -> bool) -> 'a -> 'a Seq.seq;
  val depthFirstIgnoreForget : ('a -> 'a Seq.seq) -> ('a * 'a list -> bool) -> ('a * 'a list -> bool) -> 'a -> 'a Seq.seq;
  val breadthFirstIgnore : ('a -> 'a Seq.seq) -> ('a * 'a list -> bool) -> 'a -> 'a Seq.seq;
  val breadthFirstIgnoreForget : ('a -> 'a Seq.seq) -> ('a * 'a list -> bool) -> ('a * 'a list -> bool) -> 'a -> 'a Seq.seq;
  val bestFirstIgnore : ('a -> 'a Seq.seq) -> ('a * 'a -> order) -> ('a * 'a list -> bool) -> 'a -> 'a Seq.seq;
  val bestFirstIgnoreForget : ('a -> 'a Seq.seq) -> ('a * 'a -> order) -> ('a * 'a list -> bool) -> ('a * 'a list -> bool) -> 'a -> 'a Seq.seq;
  val bestFirstAll : ('a -> 'a Seq.seq) -> ('a * 'a -> order) -> ('a * 'a list -> bool) -> ('a * 'a list -> bool) -> ('a -> bool) -> 'a -> 'a Seq.seq;
end;

structure Search : SEARCH =
struct

  fun depthFirstIgnore unfold ign stop state =
    let fun dfsi frontier acc =
          (case Seq.pull frontier of
            NONE => Seq.empty
          | SOME (st,s') =>
              if stop st then frontier
              else if ign (st,acc) then dfsi s' acc
              else let val unfolded = unfold st
                   in case Seq.pull unfolded of
                          NONE => let val recdfsi = dfsi s' (st::acc)
                                  in Seq.append recdfsi (Seq.single st)
                                  end
                        | SOME (st',s'') => let val newFrontier = Seq.append unfolded s'
                                                val recdfsi = dfsi newFrontier (st::acc)
                                            in Seq.append recdfsi (Seq.single st)
                                            end
                   end
          )
    in dfsi (Seq.single state) []
    end

  fun depthFirstIgnoreForget next ign forg state =
    let fun dfsi frontier acc =
          (case Seq.pull frontier of
            NONE => Seq.empty
          | SOME (st,s') =>
              if ign (st,acc) then
                dfsi s' acc
              else
                (case Seq.pull (next st) of
                    NONE => let val recdfsi = dfsi s' (st::acc)
                            in if forg (st,acc) then recdfsi else Seq.append recdfsi (Seq.single st) end
                  | SOME (st',s'') => let val newFrontier = Seq.append (Seq.cons st' s'') s'
                                          val recdfsi = dfsi newFrontier (st::acc)
                                      in if forg (st,acc) then recdfsi else Seq.append recdfsi (Seq.single st) end))
    in dfsi (Seq.single state) []
    end

  fun depthFirstAll unfold ign forg stop state =
    let fun dfsi frontier acc =
          (case Seq.pull frontier of
            NONE => Seq.empty
          | SOME (st,s') =>
              if stop st then frontier
              else if ign (st,acc) then dfsi s' acc
              else let val unfolded = unfold st
                   in case Seq.pull unfolded of
                          NONE => let val recdfsi = dfsi s' (st::acc)
                                  in if forg (st,acc) then recdfsi else Seq.append recdfsi (Seq.single st)
                                  end
                        | SOME (st',s'') => let val newFrontier = Seq.append unfolded s'
                                                val recdfsi = dfsi newFrontier (st::acc)
                                            in if forg (st,acc) then recdfsi else Seq.append recdfsi (Seq.single st)
                                            end
                   end
          )
    in dfsi (Seq.single state) []
    end

  fun breadthFirstIgnore next ign state =
    let fun dfsi frontier acc =
          (case Seq.pull frontier of
            NONE => Seq.empty
          | SOME (st,s') =>
              if ign (st,acc) then
                dfsi s' acc
              else
                (case Seq.pull (next st) of
                    NONE => let val recdfsi = dfsi s' (st::acc)
                            in Seq.append recdfsi (Seq.single st) end
                  | SOME (st',s'') => let val newFrontier = Seq.append s' (Seq.cons st' s'')
                                          val recdfsi = dfsi newFrontier (st::acc)
                                      in Seq.append recdfsi (Seq.single st) end))
    in dfsi (Seq.single state) []
    end

  fun breadthFirstIgnoreForget next ign forg state =
    let fun dfsi frontier acc =
          (case Seq.pull frontier of
            NONE => Seq.empty
          | SOME (st,s') =>
              if ign (st,acc) then
                dfsi s' acc
              else
                (case Seq.pull (next st) of
                    NONE => let val recdfsi = dfsi s' (st::acc)
                            in if forg (st,acc) then recdfsi else Seq.append recdfsi (Seq.single st) end
                  | SOME (st',s'') => let val newFrontier = Seq.append s' (Seq.cons st' s'')
                                          val recdfsi = dfsi newFrontier (st::acc)
                                      in if forg (st,acc) then recdfsi else Seq.append recdfsi (Seq.single st) end))
    in dfsi (Seq.single state) []
    end


  fun bestFirstIgnore next h ign state =
    let fun dfsi frontier acc =
          (case Seq.pull frontier of
            NONE => Seq.empty
          | SOME (st,s') =>
              if ign (st,acc) then dfsi s' acc
              else
                (case Seq.pull (next st) of
                    NONE => let val recdfsi = dfsi s' (st::acc)
                            in Seq.insertNoEQUAL st recdfsi h end
                  | SOME (st',s'') => let val newFrontier = Seq.insertManyNoEQUAL s'' (Seq.insertNoEQUAL st' s' h) h
                                          val recdfsi = dfsi newFrontier (st::acc)
                                      in Seq.insertNoEQUAL st recdfsi h end))
    in dfsi (Seq.single state) []
    end

  fun bestFirstIgnoreForget next h ign forg state =
    let fun dfsi frontier acc =
          (case Seq.pull frontier of
            NONE => Seq.empty
          | SOME (st,s') =>
              if ign (st,acc) then dfsi s' acc
              else
                (case Seq.pull (next st) of
                    NONE => let val recdfsi = dfsi s' (st::acc)
                            in if forg (st,acc) then recdfsi else Seq.insertNoEQUAL st recdfsi h end
                  | SOME (st',s'') => let val newFrontier = Seq.insertManyNoEQUAL s'' (Seq.insertNoEQUAL st' s' h) h
                                          val recdfsi = dfsi newFrontier (st::acc)
                                      in if forg (st,acc) then recdfsi else Seq.insertNoEQUAL st recdfsi h end))
    in dfsi (Seq.single state) []
    end

  fun bestFirstAll unfold h ign forg stop state =
    let fun dfsi frontier acc =
          (case Seq.pull frontier of
            NONE => Seq.empty
          | SOME (st,s') =>
              if stop st then frontier
              else 
                if ign (st,acc) then dfsi s' acc
                else 
                  let 
                    val unfolded = unfold st
                    val newFrontier = Seq.insertManyNoEQUAL unfolded s' h
                    val recdfsi = dfsi newFrontier (st::acc)
                  in 
                    if forg (st,acc) then recdfsi 
                    else Seq.insertNoEQUAL st recdfsi h
                  end
          )
    in dfsi (Seq.single state) []
    end

end;
