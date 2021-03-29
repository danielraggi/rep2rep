import "cspace"

signature ACMT =
sig
  type uv = {trep : CSpace.vertex, crep : CSpace.vertex}
  datatype construction = Construct of uv * construction list
                        | Loop of CSpace.vertex
                        | Source of CSpace.vertex ;
  type trail;

  val wellFormed : construction -> bool;
  val almostWellFormed : construction -> bool;
  val grounded : construction -> bool;

  val CTS : construction -> trail list;
  val foundationSequence : construction -> construction list;
  val isGenerator : construction -> construction -> bool;
  val split : construction -> construction -> construction list;
  val fixInducedConstruction : construction -> construction;
end

structure acmt : ACMT =
struct

  type uv = {trep : CSpace.vertex, crep : CSpace.vertex}
  datatype construction =
      Construct of uv * construction list
    | Loop of CSpace.vertex
    | Source of CSpace.vertex ;
  type trail = construction list;

  (*The following function belongs in lists*)
  fun allZip _ [] [] = true
    | allZip f (h::t) (h'::t') = f h h' andalso allZip f t t'
    | allZip _ _ _ = false

  fun sameACMT (Source v) (Source v') = CSpace.sameVertices v v'
    | sameACMT (Loop v) (Loop v') = CSpace.sameVertices v v'
    | sameACMT (Construct ({trep = v, crep = u}, cs)) (Construct ({trep = v', crep = u'}, cs')) =
        CSpace.sameVertices v v' andalso CSpace.sameVertices u u'
        andalso allZip sameACMT cs cs'
    | sameACMT _ _ = false
    (* TO DO: implment a sameConstruction function which actually checks that constructions are the same, not only their ACMTs *)

  fun constructOf (Source v) = v
    | constructOf (Loop v) = v
    | constructOf (Construct ({trep, ...}, _)) = trep

  fun grounded (Source _) = false
    | grounded (Loop _) = false
    | grounded (Construct (_, cs)) = List.all grounded cs

  fun CTS (Source v) = [[Source v]]
    | CTS (Loop v) = [[Loop v]]
    | CTS (Construct ({trep, crep}, cs)) =
        if null cs then [[(Construct ({trep = trep, crep = crep}, []))]]
        else
          let fun addToAll S = List.map (fn s => Construct ({trep = trep, crep = crep}, []) :: s) S
          in maps (addToAll o CTS) cs
          end

  fun CTS_lossless (Source v) = [[Source v]]
    | CTS_lossless (Loop v) = [[Loop v]]
    | CTS_lossless (Construct ({trep, crep}, cs)) =
        if null cs then [[(Construct ({trep = trep, crep = crep}, []))]]
        else
          let fun addToAll S = List.map (fn s => Construct ({trep = trep, crep = crep}, cs) :: s) S
          in maps (addToAll o CTS_lossless) cs
          end

  exception EmptyInputSequence
  fun pseudoCTS (Source v) = [[Source v]]
    | pseudoCTS (Loop v) = [[Loop v]]
    | pseudoCTS (Construct (uv,cs)) =
        let fun addToFirst (s::S) = (Construct (uv,cs) :: s) :: S | addToFirst [] = raise EmptyInputSequence (*[[(Construct (uv,cs))]]*)
        in maps (addToFirst o pseudoCTS) cs
        end

  fun coherent c =
    let
      fun strongCoh (Source v) (Source v') = CSpace.sameVertices v v'
        | strongCoh (Loop v) (Loop v') = CSpace.sameVertices v v'
        | strongCoh (Construct ({trep = v, crep = u}, q)) (Construct ({trep = v', crep = u'}, q')) =
            CSpace.sameVertices v v' andalso CSpace.sameVertices u u' andalso allZip strongCoh q q'
        | strongCoh (Construct ({trep = v, ...}, _)) (Loop v') = CSpace.sameVertices v v'
        | strongCoh (Loop v') (Construct ({trep = v, ...}, _)) = CSpace.sameVertices v v'
        | strongCoh _ _ = false
      fun weakCoh (c as Construct ({trep = v, ...}, _)) (c' as Construct ({trep = v', ...}, _)) =
            if CSpace.sameVertices v v' then strongCoh c c' else true
            (*else List.all (weakCoh c) q' andalso List.all (weakCoh c') q*)
        (* the following 4 cases just make sure that there's no source somewhere that appears as a non-source somewhere else*)
        | weakCoh (Construct ({trep = v, ...}, _)) (Source v') = not (CSpace.sameVertices v v')
        | weakCoh (Source v') (Construct ({trep = v, ...}, _)) = not (CSpace.sameVertices v v')
        | weakCoh (Loop v) (Source v') = not (CSpace.sameVertices v v')
        | weakCoh (Source v') (Loop v) = not (CSpace.sameVertices v v')
        | weakCoh _ _ = true
      fun compareFromCTS ((x::C)::(h::t)) =
            List.all (weakCoh x) h andalso compareFromCTS (C::(h::t)) andalso compareFromCTS ((x::C)::t)
        | compareFromCTS ([]::(h::t)) = compareFromCTS (h::t)
        | compareFromCTS (_::[]) = true
        | compareFromCTS [] = true
    in compareFromCTS (pseudoCTS c) handle EmptyInputSequence => false
    end

  (* the datatype construction itself is not a perfect representation of constructions.
     The following function makes sure that they are well formed, by checking that Loops
     are actually loops and that non-Loops are not forming loops.*)
  fun wellFormed c =
    let fun correctLoops tr (Source v) = not (List.exists (fn x => #trep x = v) tr)
          | correctLoops tr (Loop v) = List.exists (fn x => #trep x = v) tr
          | correctLoops tr (Construct (uv, cs)) =
              List.all (fn x => not (CSpace.sameVertices (#trep x) (#trep uv))
                      andalso not (CSpace.sameVertices (#crep x) (#crep uv))) tr
              andalso List.all (correctLoops (uv :: tr)) cs
    in correctLoops [] c andalso coherent c
    end;

  (* this function simply ensures that induced constructions in a split are almost
    well formed, in the sense that there may be potential references to loops where
    the loop is not within the induced construction, but otherwise it's fine. *)
  fun almostWellFormed c =
    let fun correctLoops tr (Source v) = not (List.exists (fn x => #trep x = v) tr)
          | correctLoops tr (Loop v) = true
          | correctLoops tr (Construct (uv, cs)) =
              List.all (fn x => not (CSpace.sameVertices (#trep x) (#trep uv))
                        andalso not (CSpace.sameVertices (#crep x) (#crep uv))) tr
              andalso List.all (correctLoops (uv :: tr)) cs
    in correctLoops [] c andalso coherent c
    end;

  fun foundationSequence c = map (hd o rev) (CTS c);

  fun isGenerator (Source v) (Source v') = CSpace.sameVertices v v'
    | isGenerator (Loop v) (Loop v') = CSpace.sameVertices v v'
    | isGenerator (Construct ({trep = v, crep = u}, cs)) (Construct ({trep = v', crep = u'}, cs')) =
        CSpace.sameVertices v v' andalso CSpace.sameVertices u u'
        andalso allZip isGenerator cs cs'
    | isGenerator (Source v) (Construct ({trep, ...}, _)) =
        CSpace.sameVertices v trep
    | isGenerator (Source v) (Loop v') =
        CSpace.sameVertices v v'
    | isGenerator _ _ = false

  exception badTrail
  fun inducedConstruction (Source v) [Source v'] =
        if CSpace.sameVertices v v'
        then Source v
        else raise badTrail
    | inducedConstruction (Loop v) [Loop v'] =
        if CSpace.sameVertices v v'
        then Source v
        else raise badTrail
    | inducedConstruction (Construct ({trep = trep, crep = crep}, cs)) (Construct ({trep = trep', crep = crep'}, [])::tr) =
        if CSpace.sameVertices trep trep' andalso CSpace.sameVertices crep crep'
        then let fun ic (c::C) = (inducedConstruction c tr handle badTrail => ic C)
                   | ic [] = raise badTrail
             in if null tr then Construct ({trep = trep, crep = crep}, cs) else ic cs
             end
        else raise badTrail
    | inducedConstruction (Construct ({trep = trep, crep = crep}, cs)) [Source v'] =
        if CSpace.sameVertices trep v'
        then Construct ({trep = trep, crep = crep}, cs)
        else raise badTrail
    | inducedConstruction _ _ = raise badTrail

  exception Match
  fun split c c' = map (inducedConstruction c) (CTS c')

  fun foundationSequence' c c' = maps foundationSequence (split c c');

  fun fixInducedConstruction c =
    let
      fun fic _ (Source v) = (Source v)
        | fic tr (Loop v) = if List.exists (fn x => #trep x = v) tr then Loop v else Source v
        | fic tr (Construct (uv, cs)) =
            Construct (uv, map (fic (uv::tr)) cs)
    in fic [] c
    end

end
