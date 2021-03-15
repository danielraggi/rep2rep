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
  datatype construction = Constructor of CSpace.crep * construction list | FoundationT of CSpace.trep ;
  datatype UV = U of CSpace.crep | V of CSpace.trep ;
  type trail = UV list;

   fun TES _ (FoundationT v) = [[V v]]
     | TES tr (Constructor (u, cs)) =
         if List.exists (fn x => case x of U x' => x' = u | _ => false) tr
         then [[C u]]
         else let fun addToAll S = List.map (fn s => U u :: s) S
                  fun TES_REC c = TES (U u :: tr) c
                  val tes = maps (addToAll o TES_REC) cs
              in if null tes then [[U u]] else tes
              end

  fun wellFormed acmt =
end
