import "cspace";

signature CONSTRUCTION =
sig
  type tc = {token : CSpace.token, constructor : CSpace.constructor}
  datatype construction = TCPair of tc * construction list
                        | Loop of CSpace.token
                        | Source of CSpace.token ;
  type trail;

  val same : construction -> construction -> bool;
  val subConstruction : construction -> construction -> bool;
  val constructOf : construction -> CSpace.token;
  val wellFormed : Type.typeSystem -> construction -> bool;
  val almostWellFormed : construction -> bool;
  val grounded : construction -> bool;

  val CTS : construction -> trail list;
  val inducedConstruction : construction -> trail -> construction;
  val foundationSequence : construction -> CSpace.token list;
  val fullTokenSequence : construction -> CSpace.token list;
  val isGenerator : construction -> construction -> bool;
  val split : construction -> construction -> construction list;
  val unsplit : (construction * construction list) -> construction;
  val fixLoops : construction -> construction;
  val attachAtSource : construction -> construction -> construction;

  val renameConstruct : construction -> CSpace.token -> construction;

  val attachConstructionAtToken : construction -> CSpace.token -> construction -> construction list;

  val tokensOfConstruction : construction -> CSpace.token list;

  val toString : construction -> string;

  exception MalformedConstructionTerm
end;

structure Construction : CONSTRUCTION =
struct

  type tc = {token : CSpace.token, constructor : CSpace.constructor}
  datatype construction =
      TCPair of tc * construction list
    | Loop of CSpace.token
    | Source of CSpace.token ;
  datatype vertex = Token of CSpace.token | Constructor of CSpace.constructor
  type trail = vertex list;

  fun isTrivial (Source _) = true
    | isTrivial _ = false

  fun toString (Source t) = CSpace.stringOfToken t
    | toString (Loop t) = CSpace.stringOfToken t
    | toString (TCPair ({token,constructor}, cs)) =
       CSpace.stringOfToken token ^ " <- " ^ CSpace.stringOfConstructor constructor ^ " <-" ^ (String.stringOfList toString cs)

  fun same (Source t) (Source t') = CSpace.sameTokens t t'
    | same (Loop t) (Loop t') = CSpace.sameTokens t t'
    | same (TCPair ({token = t, constructor = u}, cs)) (TCPair ({token = t', constructor = u'}, cs')) =
        CSpace.sameTokens t t' andalso CSpace.sameConstructors u u'
        andalso List.allZip same cs cs'
    | same _ _ = false
    (* TO DO: implment a sameConstruction function which actually checks that constructions are the same, not only their construction terms *)

  fun subConstruction (Source t) (Source t') = CSpace.sameTokens t t'
    | subConstruction (Loop t) (Loop t') = CSpace.sameTokens t t'
    | subConstruction (TCPair ({token = t, constructor = u}, cs)) (TCPair ({token = t', constructor = u'}, cs')) =
        CSpace.sameTokens t t' andalso CSpace.sameConstructors u u'
        andalso List.allZip subConstruction cs cs'
    | subConstruction (Source t) (TCPair ({token = t', ...}, _)) = CSpace.sameTokens t t'
    | subConstruction _ _ = false

  fun constructOf (Source t) = t
    | constructOf (Loop t) = t
    | constructOf (TCPair ({token, ...}, _)) = token

  fun grounded (Source _) = false
    | grounded (Loop _) = false
    | grounded (TCPair (_, cs)) = List.all grounded cs

  fun CTS (Source t) = [[Token t]]
    | CTS (Loop t) = [[Token t]]
    | CTS (TCPair ({token, constructor}, cs)) =
        if null cs then [[Token token, Constructor constructor]]
        else
          let fun addToAll S = List.map (fn s => [Token token, Constructor constructor] @ s) S
          in List.maps (addToAll o CTS) cs
          end

  fun CTS_lossless (Source t) = [[Source t]]
    | CTS_lossless (Loop t) = [[Loop t]]
    | CTS_lossless (TCPair ({token, constructor}, cs)) =
        if null cs then [[(TCPair ({token = token, constructor = constructor}, []))]]
        else
          let fun addToAll S = List.map (fn s => TCPair ({token = token, constructor = constructor}, cs) :: s) S
          in List.maps (addToAll o CTS_lossless) cs
          end

  exception EmptyInputSequence
  fun pseudoCTS (Source t) = [[Source t]]
    | pseudoCTS (Loop t) = [[Loop t]]
    | pseudoCTS (TCPair (tc,cs)) =
        let fun addToFirst (s::S) = (TCPair (tc,cs) :: s) :: S | addToFirst [] = raise EmptyInputSequence (*[[(TCPair (tc,cs))]]*)
        in List.maps (addToFirst o pseudoCTS) cs
        end

  (* coherent checks that, if a token appears in two parts of term, there are no
  inconsistencies on which arrows target them, etc. This is very costly because it
  needs to compare every pair of subterms. *)
  fun coherent c =
    let
      fun strongCoh (Source t) (Source t') = CSpace.sameTokens t t'
        | strongCoh (Loop t) (Loop t') = CSpace.sameTokens t t'
        | strongCoh (TCPair ({token = t, constructor = c}, q)) (TCPair ({token = t', constructor = c'}, q')) =
            CSpace.sameTokens t t' andalso CSpace.sameConstructors c c' andalso List.allZip strongCoh q q'
        | strongCoh (TCPair ({token = t, ...}, _)) (Loop t') = CSpace.sameTokens t t'
        | strongCoh (Loop t') (TCPair ({token = t, ...}, _)) = CSpace.sameTokens t t'
        | strongCoh _ _ = false
      fun weakCoh (c as TCPair ({token = t, ...}, _)) (c' as TCPair ({token = t', ...}, _)) =
            not (CSpace.sameTokens t t') orelse strongCoh c c'
            (*else List.all (weakCoh c) q' andalso List.all (weakCoh c') q*)
        (* the following 4 cases just make sure that there's no source somewhere that appears as a non-source somewhere else*)
        | weakCoh (TCPair ({token = t, ...}, _)) (Source t') = not (CSpace.sameTokens t t')
        | weakCoh (Source t') (TCPair ({token = t, ...}, _)) = not (CSpace.sameTokens t t')
        | weakCoh (Loop t) (Source t') = not (CSpace.sameTokens t t')
        | weakCoh (Source t') (Loop t) = not (CSpace.sameTokens t t')
        | weakCoh _ _ = true
      fun compareFromCTS ((x::C)::(h::t)) =
            List.all (weakCoh x) h andalso compareFromCTS (C::(h::t)) andalso compareFromCTS ((x::C)::t)
        | compareFromCTS ([]::(h::t)) = compareFromCTS (h::t)
        | compareFromCTS (_::[]) = true
        | compareFromCTS [] = true
    in compareFromCTS (pseudoCTS c) handle EmptyInputSequence => false
    end

  fun specialises T [] [] = true
    | specialises T (ty::tys) (ty'::tys') = (#subType T) (ty, ty') andalso specialises T tys tys'
    | specialises _ _ _ = false
  (* the datatype construction itself is not a perfect representation of constructions.
     The following function makes sure that they are well formed, by checking that Loops
     are actually loops and that non-Loops are not forming loops.*)
  fun wellFormed T c =
    let fun correctLoopsAndTypes tr (Source t) = not (List.exists (fn x => #token x = t) tr)
          | correctLoopsAndTypes tr (Loop t) = List.exists (fn x => #token x = t) tr
          | correctLoopsAndTypes tr (TCPair (tc, cs)) =
            let val typesOfInducedConstructs = map (CSpace.typeOfToken o constructOf) cs
                val (typesOfConstructor,ty) = CSpace.spec (#constructor tc)
                val typeOfConstruct = CSpace.typeOfToken (#token tc)
            in (#subType T) (typeOfConstruct, ty)
                andalso specialises T (typesOfInducedConstructs) typesOfConstructor
                andalso List.all (fn x => not (CSpace.sameTokens (#token x) (#token tc))
                                  andalso not (CSpace.sameConstructors (#constructor x) (#constructor tc))) tr
                andalso List.all (correctLoopsAndTypes (tc :: tr)) cs
            end
    in correctLoopsAndTypes [] c andalso coherent c
    end;
  exception MalformedConstructionTerm;

  (* this function simply ensures that induced constructions in a split are almost
    well formed, in the sense that there may be potential references to loops where
    the loop is not within the induced construction, but otherwise it's fine. *)
  fun almostWellFormed c =
    let fun correctLoops tr (Source t) = not (List.exists (fn x => #token x = t) tr)
          | correctLoops _ (Loop _) = true
          | correctLoops tr (TCPair (tc, cs)) =
              List.all (fn x => not (CSpace.sameTokens (#token x) (#token tc))
                        andalso not (CSpace.sameConstructors (#constructor x) (#constructor tc))) tr
              andalso List.all (correctLoops (tc :: tr)) cs
    in correctLoops [] c andalso coherent c
    end;

  fun tokenOfVertex (Token t) = t
    | tokenOfVertex _ = raise MalformedConstructionTerm;

  fun foundationSequence c = map (tokenOfVertex o hd o rev) (CTS c);

  fun removeDuplicates eq [] = []
    | removeDuplicates eq (h::t) = h :: removeDuplicates eq (List.filter (fn x => not(eq x h)) t)
  fun fullTokenSequence ct =
    let fun fvs (Source t) = [t]
          | fvs (Loop t) = []
          | fvs (TCPair ({token,constructor},cs)) =
              token :: List.concat (map fvs cs)
    in removeDuplicates CSpace.sameTokens (fvs ct)
    end

  fun isGenerator (Source t) (Source t') = CSpace.sameTokens t t'
    | isGenerator (Loop t) (Loop t') = CSpace.sameTokens t t'
    | isGenerator (TCPair ({token = t, constructor = c}, cs)) (TCPair ({token = t', constructor = c'}, cs')) =
        CSpace.sameTokens t t' andalso CSpace.sameConstructors c c'
        andalso List.allZip isGenerator cs cs'
    | isGenerator (Source t) (TCPair ({token, ...}, _)) =
        CSpace.sameTokens t token
    | isGenerator (Source t) (Loop t') =
        CSpace.sameTokens t t'
    | isGenerator _ _ = false

  exception badTrail
  fun inducedConstruction (Source t) [Token t'] =
        if CSpace.sameTokens t t'
        then Source t
        else raise badTrail
    | inducedConstruction (Loop t) [Token t'] =
        if CSpace.sameTokens t t'
        then Source t
        else raise badTrail
    | inducedConstruction (TCPair ({token = token, constructor = constructor}, cs)) (Token token'::Constructor constructor'::tr) =
        if CSpace.sameTokens token token' andalso CSpace.sameConstructors constructor constructor'
        then let fun ic (c::C) = (inducedConstruction c tr handle badTrail => ic C)
                   | ic [] = raise badTrail
             in if null tr then TCPair ({token = token, constructor = constructor}, cs) else ic cs
             end
        else raise badTrail
    | inducedConstruction (TCPair ({token = token, constructor = constructor}, cs)) [Token t'] =
        if CSpace.sameTokens token t'
        then TCPair ({token = token, constructor = constructor}, cs)
        else raise badTrail
    | inducedConstruction _ _ = raise badTrail

  exception NotASplit
  fun split c c' = map (inducedConstruction c) (CTS c')

  fun fixLoops c =
    let
      fun fic _ (Source t) = (Source t)
        | fic tr (Loop t) = if List.exists (fn x => #token x = t) tr then Loop t else Source t
        | fic tr (TCPair (tc, cs)) =
            TCPair (tc, map (fic (tc::tr)) cs)
    in fic [] c
    end

  (* The choice of how this function is built may seem strange, but it's made
      so that if the split is not actually a split but something like a pattern split, where
      the induced construction are specialisations, it uses the construct of the
      specialisation instead of the original token *)
  fun unsplit x =
    let fun unsplit' (Source _,[ct]) = ct
          | unsplit' (Loop _, [ct]) = Loop (constructOf ct)
          | unsplit' ((TCPair (tc,cs)), cts) =
              let fun us (c::L) icts = (case List.split(icts, length (foundationSequence c)) of
                                            (cLx,cly) => unsplit' (c, cLx) :: us L cly)
                    | us [] _ = []
              in TCPair (tc, us cs cts)
              end
          | unsplit' _ = raise NotASplit
        val result = fixLoops (unsplit' x)
      (*  val _ = if wellFormed T result then () else print "\n WARNING: " ^ toString result ^ " is malformed" *)
    in result end

  fun isLoop (Loop _) = true
    | isLoop _ = false

  fun attachAtSource ct (Source t) =
        if CSpace.sameTokens (constructOf ct) t then ct else (Source t)
    | attachAtSource ct (TCPair (tc, cs)) =
        if CSpace.sameTokens (constructOf ct) (#token tc)
        then (print "not attachable";(TCPair (tc, cs)))
        else (TCPair (tc, map (attachAtSource ct) cs))
    | attachAtSource _ (Loop t) = (Loop t)


  exception BadConstruction
  fun renameConstruct ct t' =
    let fun rc _ (Source t)  = Source t
          | rc originalConstruct (Loop t) = if CSpace.sameTokens t originalConstruct then Loop t' else Loop t
          | rc originalConstruct (TCPair (tc, cs)) = TCPair (tc, map (rc originalConstruct) cs)
    in case ct of Source _ => Source t'
                | Loop _ => raise BadConstruction
                | TCPair ({token = t,constructor = c}, cs) => TCPair ({token = t',constructor = c}, map (rc t) cs)
    end

  fun attachConstructionAtToken (Source t) t' ct = if CSpace.sameTokens t t' then [ct] else [Source t]
    | attachConstructionAtToken (Loop t) _ _ = [Loop t]
    | attachConstructionAtToken (TCPair (tc, cs)) t ct =
        if CSpace.sameTokens (#token tc) t
        then (if subConstruction ct (TCPair (tc, cs))
              then [TCPair (tc, cs)]
              else if subConstruction (TCPair (tc, cs)) ct
                   then [ct]
                   else [TCPair (tc, cs), ct])
        else
          let val csr = map (fn x => attachConstructionAtToken x t ct) cs
              fun mkNew xs = TCPair (tc, xs)
          in map mkNew (List.listProduct csr)
          end

  fun tokensOfConstruction ct =
    let fun toc (Source t) = [t]
          | toc (Loop _) = []
          | toc (TCPair ({token, ...}, cs)) = token :: List.maps toc cs
    in List.removeRepetition CSpace.sameTokens (toc ct)
    end

end;
