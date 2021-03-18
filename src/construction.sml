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

  fun sameACMT (FoundationTRep v) (FoundationTRep v') = CSpace.sameVertices v v'
    | sameACMT (Loop {trep = trep, crep = crep}) (Loop {trep = trep', crep = crep'}) =
        CSpace.sameVertices trep trep' andalso CSpace.sameVertices crep crep'
    | sameACMT (Construct ({trep = trep, crep = crep}, cs)) (Construct ({trep = trep', crep = crep'}, cs')) =
        CSpace.sameVertices trep trep' andalso CSpace.sameVertices crep crep'
        andalso let fun scs (c::C) (c'::C') = sameACMT c c' andalso scs C C'
                      | scs [] [] = true
                      | scs _ _ = false
                in scs cs cs' end
    | sameACMT _ _ = false
    (* TO DO: implment a sameConstruction function which actually checks that constructions are the same, not only their ACMTs *)

   (* the datatype construction itself is not a perfect representation of constructions.
      The following function makes sure that they are well formed, by checking that Loops
      are actually loops and that non-Loops are not forming loops. Note that evey well formed
      constructions are not cannonical, so there may be two representations of the same construction. *)
  fun wellFormed c =
    let fun wellFormed' _ (FoundationTRep v) = true
          | wellFormed' tr (Loop {trep, crep}) = List.exists (fn x => x = {trep = trep, crep = crep}) tr
          | wellFormed' tr (Construct ({trep, crep}, cs)) =
            List.all (fn x => not (CSpace.sameVertices (#trep x) trep)
                      andalso not (CSpace.sameVertices (#crep x) crep)) tr
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

  fun isGenerator (FoundationTRep v) (FoundationTRep v') = CSpace.sameVertices v v'
    | isGenerator (Loop {trep = trep, crep = crep}) (Loop {trep = trep', crep = crep'}) =
        CSpace.sameVertices trep trep' andalso CSpace.sameVertices crep crep'
    | isGenerator (Construct ({trep = trep, crep = crep}, cs)) (Construct ({trep = trep', crep = crep'}, cs')) =
        CSpace.sameVertices trep trep' andalso CSpace.sameVertices crep crep'
        andalso let fun igs (c::C) (c'::C') = isGenerator c c' andalso igs C C'
                      | igs [] [] = true
                      | igs _ _ = false
                in igs cs cs' end
    | isGenerator (FoundationTRep v) (Construct ({trep, ...}, _)) =
        CSpace.sameVertices v trep
    | isGenerator (FoundationTRep v) (Loop ({trep, ...})) =
        CSpace.sameVertices v trep
    | isGenerator _ _ = false

  exception badTrail
  fun inducedConstruction (FoundationTRep v) [FoundationTRep v'] =
        if CSpace.sameVertices v v'
        then FoundationTRep v'
        else raise badTrail
    | inducedConstruction (Loop {trep = trep, crep = crep}) [Loop {trep = trep', crep = crep'}] =
        if CSpace.sameVertices trep trep' andalso CSpace.sameVertices crep crep'
        then FoundationTRep trep
        else raise badTrail
    | inducedConstruction (Construct ({trep = trep, crep = crep}, cs)) (Construct ({trep = trep', crep = crep'}, [])::tr) =
        if CSpace.sameVertices trep trep' andalso CSpace.sameVertices crep crep'
        then let fun ic (c::C) = (inducedConstruction c tr handle badTrail => ic C)
                   | ic [] = raise badTrail
             in if null tr then Construct ({trep = trep, crep = crep}, cs) else ic cs
             end
        else raise badTrail
    | inducedConstruction (Construct ({trep = trep, crep = crep}, cs)) [FoundationTRep v'] =
        if CSpace.sameVertices trep v'
        then Construct ({trep = trep, crep = crep}, cs)
        else raise badTrail
    | inducedConstruction _ _ = raise badTrail
    (* TO DO: make sure that inducedConstructions of a well formed construction are well formed,
        especially when there are loops *)

  exception Match
  fun split c c' = map (inducedConstruction c) (CTS c')


  fun foundationSequence' c c' = maps foundationSequence (split c c');

end
