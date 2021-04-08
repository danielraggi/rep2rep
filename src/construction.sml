import "cspace"

signature ACMT =
sig
  type ut = {token : CSpace.vertex, crep : CSpace.vertex}
  datatype construction = Construct of ut * construction list
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

  type ut = {token : CSpace.vertex, crep : CSpace.vertex}
  datatype construction =
      Construct of ut * construction list
    | Loop of CSpace.vertex
    | Source of CSpace.vertex ;
  type trail = construction list;

  (*The following function belongs in lists*)
  fun allZip _ [] [] = true
    | allZip f (h::t) (h'::t') = f h h' andalso allZip f t t'
    | allZip _ _ _ = false

  fun sameACMT (Source t) (Source t') = CSpace.sameVertices t t'
    | sameACMT (Loop t) (Loop t') = CSpace.sameVertices t t'
    | sameACMT (Construct ({token = t, crep = u}, cs)) (Construct ({token = t', crep = u'}, cs')) =
        CSpace.sameVertices t t' andalso CSpace.sameVertices u u'
        andalso allZip sameACMT cs cs'
    | sameACMT _ _ = false
    (* TO DO: implment a sameConstruction function which actually checks that constructions are the same, not only their ACMTs *)

  fun constructOf (Source t) = t
    | constructOf (Loop t) = t
    | constructOf (Construct ({token, ...}, _)) = token

  fun grounded (Source _) = false
    | grounded (Loop _) = false
    | grounded (Construct (_, cs)) = List.all grounded cs

  fun CTS (Source t) = [[Source t]]
    | CTS (Loop t) = [[Loop t]]
    | CTS (Construct ({token, crep}, cs)) =
        if null cs then [[(Construct ({token, crep}, []))]]
        else
          let fun addToAll S = List.map (fn s => Construct ({token = token, crep = crep}, []) :: s) S
          in maps (addToAll o CTS) cs
          end

  fun CTS_lossless (Source t) = [[Source t]]
    | CTS_lossless (Loop t) = [[Loop t]]
    | CTS_lossless (Construct ({token, crep}, cs)) =
        if null cs then [[(Construct ({token = token, crep = crep}, []))]]
        else
          let fun addToAll S = List.map (fn s => Construct ({token = token, crep = crep}, cs) :: s) S
          in maps (addToAll o CTS_lossless) cs
          end

  exception EmptyInputSequence
  fun pseudoCTS (Source t) = [[Source t]]
    | pseudoCTS (Loop t) = [[Loop t]]
    | pseudoCTS (Construct (ut,cs)) =
        let fun addToFirst (s::S) = (Construct (ut,cs) :: s) :: S | addToFirst [] = raise EmptyInputSequence (*[[(Construct (ut,cs))]]*)
        in maps (addToFirst o pseudoCTS) cs
        end

  fun coherent c =
    let
      fun strongCoh (Source t) (Source t') = CSpace.sameVertices t t'
        | strongCoh (Loop t) (Loop t') = CSpace.sameVertices t t'
        | strongCoh (Construct ({token = t, crep = u}, q)) (Construct ({token = t', crep = u'}, q')) =
            CSpace.sameVertices t t' andalso CSpace.sameVertices u u' andalso allZip strongCoh q q'
        | strongCoh (Construct ({token = t, ...}, _)) (Loop t') = CSpace.sameVertices t t'
        | strongCoh (Loop t') (Construct ({token = t, ...}, _)) = CSpace.sameVertices t t'
        | strongCoh _ _ = false
      fun weakCoh (c as Construct ({token = t, ...}, _)) (c' as Construct ({token = t', ...}, _)) =
            if CSpace.sameVertices t t' then strongCoh c c' else true
            (*else List.all (weakCoh c) q' andalso List.all (weakCoh c') q*)
        (* the following 4 cases just make sure that there's no source somewhere that appears as a non-source somewhere else*)
        | weakCoh (Construct ({token = t, ...}, _)) (Source t') = not (CSpace.sameVertices t t')
        | weakCoh (Source t') (Construct ({token = t, ...}, _)) = not (CSpace.sameVertices t t')
        | weakCoh (Loop t) (Source t') = not (CSpace.sameVertices t t')
        | weakCoh (Source t') (Loop t) = not (CSpace.sameVertices t t')
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
    let fun correctLoops tr (Source t) = not (List.exists (fn x => #token x = t) tr)
          | correctLoops tr (Loop t) = List.exists (fn x => #token x = t) tr
          | correctLoops tr (Construct (ut, cs)) =
              List.all (fn x => not (CSpace.sameVertices (#token x) (#token ut))
                      andalso not (CSpace.sameVertices (#crep x) (#crep ut))) tr
              andalso List.all (correctLoops (ut :: tr)) cs
    in correctLoops [] c andalso coherent c
    end;

  (* this function simply ensures that induced constructions in a split are almost
    well formed, in the sense that there may be potential references to loops where
    the loop is not within the induced construction, but otherwise it's fine. *)
  fun almostWellFormed c =
    let fun correctLoops tr (Source t) = not (List.exists (fn x => #token x = t) tr)
          | correctLoops tr (Loop t) = true
          | correctLoops tr (Construct (ut, cs)) =
              List.all (fn x => not (CSpace.sameVertices (#token x) (#token ut))
                        andalso not (CSpace.sameVertices (#crep x) (#crep ut))) tr
              andalso List.all (correctLoops (ut :: tr)) cs
    in correctLoops [] c andalso coherent c
    end;

  fun foundationSequence c = map (hd o rev) (CTS c);

  fun isGenerator (Source t) (Source t') = CSpace.sameVertices t t'
    | isGenerator (Loop t) (Loop t') = CSpace.sameVertices t t'
    | isGenerator (Construct ({token = t, crep = u}, cs)) (Construct ({token = t', crep = u'}, cs')) =
        CSpace.sameVertices t t' andalso CSpace.sameVertices u u'
        andalso allZip isGenerator cs cs'
    | isGenerator (Source t) (Construct ({token, ...}, _)) =
        CSpace.sameVertices t token
    | isGenerator (Source t) (Loop t') =
        CSpace.sameVertices t t'
    | isGenerator _ _ = false

  exception badTrail
  fun inducedConstruction (Source t) [Source t'] =
        if CSpace.sameVertices t t'
        then Source t
        else raise badTrail
    | inducedConstruction (Loop t) [Loop t'] =
        if CSpace.sameVertices t t'
        then Source t
        else raise badTrail
    | inducedConstruction (Construct ({token = token, crep = crep}, cs)) (Construct ({token = token', crep = crep'}, [])::tr) =
        if CSpace.sameVertices token token' andalso CSpace.sameVertices crep crep'
        then let fun ic (c::C) = (inducedConstruction c tr handle badTrail => ic C)
                   | ic [] = raise badTrail
             in if null tr then Construct ({token = token, crep = crep}, cs) else ic cs
             end
        else raise badTrail
    | inducedConstruction (Construct ({token = token, crep = crep}, cs)) [Source t'] =
        if CSpace.sameVertices token t'
        then Construct ({token = token, crep = crep}, cs)
        else raise badTrail
    | inducedConstruction _ _ = raise badTrail

  exception Match
  fun split c c' = map (inducedConstruction c) (CTS c')

  fun foundationSequence' c c' = maps foundationSequence (split c c');

  fun fixInducedConstruction c =
    let
      fun fic _ (Source t) = (Source t)
        | fic tr (Loop t) = if List.exists (fn x => #token x = t) tr then Loop t else Source t
        | fic tr (Construct (ut, cs)) =
            Construct (ut, map (fic (ut::tr)) cs)
    in fic [] c
    end

end
