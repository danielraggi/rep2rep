import "cspace"

signature CONSTRUCTIONTERM =
sig
  type ut = {token : CSpace.vertex, configurator : CSpace.vertex}
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

structure ConstructionTerm : CONSTRUCTIONTERM =
struct

  type ut = {token : CSpace.vertex, configurator : CSpace.vertex}
  datatype construction =
      Construct of ut * construction list
    | Loop of CSpace.vertex
    | Source of CSpace.vertex ;
  type trail = construction list;

  (*The following function belongs in lists*)
  fun allZip _ [] [] = true
    | allZip f (h::t) (h'::t') = f h h' andalso allZip f t t'
    | allZip _ _ _ = false

  fun sameCT (Source t) (Source t') = CSpace.sameVertices t t'
    | sameCT (Loop t) (Loop t') = CSpace.sameVertices t t'
    | sameCT (Construct ({token = t, configurator = u}, cs)) (Construct ({token = t', configurator = u'}, cs')) =
        CSpace.sameVertices t t' andalso CSpace.sameVertices u u'
        andalso allZip sameCT cs cs'
    | sameCT _ _ = false
    (* TO DO: implment a sameConstruction function which actually checks that constructions are the same, not only their construction terms *)

  fun constructOf (Source t) = t
    | constructOf (Loop t) = t
    | constructOf (Construct ({token, ...}, _)) = token

  fun grounded (Source _) = false
    | grounded (Loop _) = false
    | grounded (Construct (_, cs)) = List.all grounded cs

  fun CTS (Source t) = [[Source t]]
    | CTS (Loop t) = [[Loop t]]
    | CTS (Construct ({token, configurator}, cs)) =
        if null cs then [[(Construct ({token, configurator}, []))]]
        else
          let fun addToAll S = List.map (fn s => Construct ({token = token, configurator = configurator}, []) :: s) S
          in maps (addToAll o CTS) cs
          end

  fun CTS_lossless (Source t) = [[Source t]]
    | CTS_lossless (Loop t) = [[Loop t]]
    | CTS_lossless (Construct ({token, configurator}, cs)) =
        if null cs then [[(Construct ({token = token, configurator = configurator}, []))]]
        else
          let fun addToAll S = List.map (fn s => Construct ({token = token, configurator = configurator}, cs) :: s) S
          in maps (addToAll o CTS_lossless) cs
          end

  exception EmptyInputSequence
  fun pseudoCTS (Source t) = [[Source t]]
    | pseudoCTS (Loop t) = [[Loop t]]
    | pseudoCTS (Construct (ut,cs)) =
        let fun addToFirst (s::S) = (Construct (ut,cs) :: s) :: S | addToFirst [] = raise EmptyInputSequence (*[[(Construct (ut,cs))]]*)
        in maps (addToFirst o pseudoCTS) cs
        end

  (* coherent checks that, if a token appears in two parts of term, there are no
  inconsistencies on which arrows target them, etc. This is very costly because it
  needs to compare every pair of subterms. *)
  fun coherent c =
    let
      fun strongCoh (Source t) (Source t') = CSpace.sameVertices t t'
        | strongCoh (Loop t) (Loop t') = CSpace.sameVertices t t'
        | strongCoh (Construct ({token = t, configurator = u}, q)) (Construct ({token = t', configurator = u'}, q')) =
            CSpace.sameVertices t t' andalso CSpace.sameVertices u u' andalso allZip strongCoh q q'
        | strongCoh (Construct ({token = t, ...}, _)) (Loop t') = CSpace.sameVertices t t'
        | strongCoh (Loop t') (Construct ({token = t, ...}, _)) = CSpace.sameVertices t t'
        | strongCoh _ _ = false
      fun weakCoh (c as Construct ({token = t, ...}, _)) (c' as Construct ({token = t', ...}, _)) =
            not (CSpace.sameVertices t t') orelse strongCoh c c'
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
                      andalso not (CSpace.sameVertices (#configurator x) (#configurator ut))) tr
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
                        andalso not (CSpace.sameVertices (#configurator x) (#configurator ut))) tr
              andalso List.all (correctLoops (ut :: tr)) cs
    in correctLoops [] c andalso coherent c
    end;

  fun foundationSequence c = map (hd o rev) (CTS c);

  fun isGenerator (Source t) (Source t') = CSpace.sameVertices t t'
    | isGenerator (Loop t) (Loop t') = CSpace.sameVertices t t'
    | isGenerator (Construct ({token = t, configurator = u}, cs)) (Construct ({token = t', configurator = u'}, cs')) =
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
    | inducedConstruction (Construct ({token = token, configurator = configurator}, cs)) (Construct ({token = token', configurator = configurator'}, [])::tr) =
        if CSpace.sameVertices token token' andalso CSpace.sameVertices configurator configurator'
        then let fun ic (c::C) = (inducedConstruction c tr handle badTrail => ic C)
                   | ic [] = raise badTrail
             in if null tr then Construct ({token = token, configurator = configurator}, cs) else ic cs
             end
        else raise badTrail
    | inducedConstruction (Construct ({token = token, configurator = configurator}, cs)) [Source t'] =
        if CSpace.sameVertices token t'
        then Construct ({token = token, configurator = configurator}, cs)
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
