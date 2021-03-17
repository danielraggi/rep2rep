import "cspace"

signature ACMT =
sig
  type construction;
  type trail;
  val wellFormed : construction -> bool;
  val grounded : construction -> bool;
  val CTS : construction -> trail list;
  val foundationSequence : construction -> construction list;
end

structure acmt : ACMT =
struct
  type uv = {trep : CSpace.vertex, crep : CSpace.vertex}
  datatype construction =
      Construct of uv * construction list
    | Loop of uv
    | FoundationTRep of CSpace.vertex ;
  type trail = construction list;

  fun sameConstruction (FoundationTRep v) (FoundationTRep v') = CSpace.sameVertices v v'
    | sameConstruction (Loop {trep = trep, crep = crep}) (Loop {trep = trep', crep = crep'}) =
        CSpace.sameVertices trep trep' andalso CSpace.sameVertices crep crep'
    | sameConstruction (Construct ({trep = trep, crep = crep}, cs)) (Construct ({trep = trep', crep = crep'}, cs')) =
        CSpace.sameVertices trep trep' andalso CSpace.sameVertices crep crep'
        andalso let fun scs (c::C) (c'::C') = sameConstruction c c' andalso scs C C'
                      | scs [] [] = true
                      | scs _ _ = false
                in scs cs cs' end
    | sameConstruction _ _ = false

   (* the datatype construction itself is not a perfect representation of constructions.
      The following function makes sure that they are well formed, by checking that Loops
      are actually loops and that non-Loops are not forming loops *)
  fun wellFormed c =
    let fun wellFormed' _ (FoundationTRep v) = true
          | wellFormed' tr (Loop {trep, crep}) = List.exists (fn x => x = {trep = trep, crep = crep}) tr
          | wellFormed' tr (Construct ({trep, crep}, cs)) =
            List.all (fn x => not (CSpace.sameVertices (#trep x) trep) andalso not (CSpace.sameVertices (#crep x) crep)) tr
            andalso List.all (wellFormed' ({trep = trep, crep = crep} :: tr)) cs
    in wellFormed' [] c
    end;

  fun grounded (FoundationTRep _) = false
    | grounded (Loop _) = false
    | grounded (Construct (_, cs)) = List.all grounded cs

  fun CTS (FoundationTRep v) = [[FoundationTRep v]]
    | CTS (Loop {trep, crep}) = [[Loop {trep = trep, crep = crep}]]
    | CTS (Construct ({trep, crep}, cs)) =
        if null cs then [[(Construct ({trep = trep, crep = crep}, []))]]
        else
          let fun addToAll S = List.map (fn s => Construct ({trep = trep, crep = crep}, []) :: s) S
              in maps (addToAll o CTS) cs
              end

  fun foundationSequence c = map (hd o rev) (CTS c);

end
