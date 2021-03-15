import "cspace"

signature ACMT =
sig
  type construction;
  type trail;
  val TES : construction -> trail -> trail list;
  val wellFormed : construction -> bool;
end

structure acmt : ACMT =
struct
  datatype construction = Constructor of CSpace.vertex * construction list | FoundationT of CSpace.vertex ;
  type trail = CSpace.vertex list;

   fun TES _ (FoundationT v) = [[v]]
     | TES tr (Constructor (u, cs)) =
         if null cs orelse List.exists (fn x => x = u) tr
         then [[u]]
         else let fun addToAll S = List.map (fn s => u :: s) S
                  fun TES_REC c = TES (u :: tr) c
                  val tes = maps (addToAll o TES_REC) cs
              in tes
              end

  fun wellFormed acmt =
end
