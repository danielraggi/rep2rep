import "core.cspace";
import "util.rpc";

signature CONSTRUCTION =
sig
  type tc = {token : CSpace.token, constructor : CSpace.constructor}
  datatype construction = TCPair of tc * construction list
                        | Source of CSpace.token
                        | Reference of CSpace.token;
  type walk;

  val tc_rpc : tc Rpc.Datatype.t;
  val construction_rpc: construction Rpc.Datatype.t;
  val walk_rpc: walk Rpc.Datatype.t;

  val same : construction -> construction -> bool;
  val subConstruction : construction -> construction -> bool;
  val constructOf : construction -> CSpace.token;
  val wellFormed : (*CSpace.conSpec ->*) Type.typeSystem -> construction -> bool;
  val size : construction -> int;
  (*val almostWellFormed : construction -> bool;*)
(*)
  val CTS : construction -> walk list;
  val inducedConstruction : construction -> walk -> construction;
  val foundationSequence : construction -> CSpace.token list;*)
  val fullTokenSequence : construction -> CSpace.token list;
  val isGenerator : construction -> construction -> bool;
  (*)
  val split : construction -> construction -> construction list;
  val unsplit : (construction * construction list) -> construction;*)
  val fixLoops : construction -> construction;
  val fixReferences : construction -> construction;
  val findAndExpandSubConstruction : construction -> CSpace.token -> construction
  val attachAtSource : construction -> construction -> construction;

  val replaceConstruct : construction -> CSpace.token -> construction;

  val attachConstructionAtToken : construction -> CSpace.token -> construction -> construction list;

  val toString : construction -> string;

  exception MalformedConstructionTerm of string;
end;

structure Construction : CONSTRUCTION =
struct

  type tc = {token : CSpace.token, constructor : CSpace.constructor}
  datatype construction =
      TCPair of tc * construction list
    | Source of CSpace.token
    | Reference of CSpace.token ;
  datatype vertex = Token of CSpace.token | Constructor of CSpace.constructor
  type walk = vertex list;

  val tc_rpc = Rpc.Datatype.convert
                   (Rpc.Datatype.tuple2 (CSpace.token_rpc, CSpace.constructor_rpc))
                   (fn (t, u) => {token = t, constructor = u})
                   (fn {token = t, constructor = u} => (t, u));

  fun construction_rpc_ () = Rpc.Datatype.convert
                                 (Rpc.Datatype.either3
                                      (Rpc.Datatype.tuple2
                                           (tc_rpc,
                                            List.list_rpc
                                                (Rpc.Datatype.recur construction_rpc_)),
                                       CSpace.token_rpc,
                                       CSpace.token_rpc))
                                 (fn (Rpc.Datatype.Either3.FST (tc, cs)) => TCPair (tc, cs)
                                   | (Rpc.Datatype.Either3.SND t) => Source t
                                   | (Rpc.Datatype.Either3.THD t) => Reference t)
                                 (fn (TCPair (tc, cs)) => Rpc.Datatype.Either3.FST (tc, cs)
                                   | (Source t) => Rpc.Datatype.Either3.SND t
                                   | (Reference t) => Rpc.Datatype.Either3.THD t);

  val construction_rpc = construction_rpc_ ();

  val vertex_rpc = Rpc.Datatype.convert
                       (Rpc.Datatype.either2 (CSpace.token_rpc, CSpace.constructor_rpc))
                       (fn (Rpc.Datatype.Either2.FST t) => Token t
                         | (Rpc.Datatype.Either2.SND u) => Constructor u)
                       (fn (Token t) => Rpc.Datatype.Either2.FST t
                         | (Constructor u) => Rpc.Datatype.Either2.SND u);

  val walk_rpc = List.list_rpc vertex_rpc;

  fun isTrivial (Source _) = true
    | isTrivial _ = false

  fun toString (Source t) = CSpace.stringOfToken t
    | toString (Reference t) = CSpace.stringOfToken t
    | toString (TCPair ({token,constructor}, cs)) =
       CSpace.stringOfToken token ^ " <- " ^ CSpace.stringOfConstructor constructor ^ " <-" ^ (String.stringOfList toString cs)

  (* The following assumes well-formed *)
  fun same (Source t) (Source t') = CSpace.sameTokens t t'
    | same (Reference t) (Reference t') = CSpace.sameTokens t t'
    | same (TCPair ({token = t, constructor = u}, cs)) (TCPair ({token = t', constructor = u'}, cs')) =
        CSpace.sameTokens t t' andalso CSpace.sameConstructors u u'
        andalso List.allZip same cs cs'
    | same _ _ = false
    (* TO DO: implment a sameConstruction function which actually checks that constructions are the same, not only their construction terms *)

  fun subConstruction (Source t) (Source t') = CSpace.sameTokens t t'
    | subConstruction (Reference t) (Reference t') = CSpace.sameTokens t t'
    | subConstruction (TCPair ({token = t, constructor = u}, cs)) (TCPair ({token = t', constructor = u'}, cs')) =
        CSpace.sameTokens t t' andalso CSpace.sameConstructors u u'
        andalso List.allZip subConstruction cs cs'
    | subConstruction (Source t) (TCPair ({token = t', ...}, _)) = CSpace.sameTokens t t'
    | subConstruction _ _ = false

  fun constructOf (Source t) = t
    | constructOf (Reference t) = t
    | constructOf (TCPair ({token, ...}, _)) = token

(*
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
    end*)

    exception MalformedConstructionTerm of string;
  fun specialises T [] [] = true
    | specialises T (ty::tys) (ty'::tys') = if (#subType T) (ty, ty') then specialises T tys tys' else false
    | specialises _ _ _ = false

  fun wellFormed T ct =
    let fun wf (Source t) prev = (not (List.exists (fn x => x = t) prev), t::prev)
          | wf (Reference t) prev = (List.exists (fn x => x = t) prev, prev)
          | wf (TCPair ({token,constructor}, cs)) prev =
            let val ty = CSpace.typeOfToken token
                val tys = map (CSpace.typeOfToken o constructOf) cs
              (*  val constructorFromCSpec = valOf (CSpace.findConstructorWithName (CSpace.nameOfConstructor constructor) C)
                val eqConstructors = CSpace.sameConstructors constructorFromCSpec constructor*)
                val (ctys,cty) = CSpace.csig constructor
                val typeChecks = specialises T (ty::tys) (cty::ctys)
                fun wfr [] prev' = (true,prev')
                  | wfr (ct'::L) prev' =
                    (case wf ct' prev' of
                      (WFX,tokenSeqX) => (case wfr L (tokenSeqX @ prev') of
                                              (WFY,tokenSeqY) => (WFX andalso WFY, tokenSeqY)))
                val (WF,uprev) = if typeChecks andalso not (List.exists (fn x => x = token) prev)
                                 then wfr cs (token::prev)
                                 else (false,prev)
            in (WF,uprev)
            end handle Option => (false,[])
    in #1 (wf ct [])
    end

  fun size (Source t) = 1
    | size (Reference t) = 0
    | size (TCPair (_,cs)) = 1 + List.foldl (fn (x,y) => size x + y) 0 cs

  exception BadConstruction
(*)
  (* the datatype construction itself is not a perfect representation of constructions.
     The following function makes sure that they are well formed, by checking that Loops
     are actually loops, that non-Loops are not forming loops, that induced constructions
     are actually induced constructions and that the inputs and outputs
     match the signature of the constructors.*)
  fun wellFormed T c =
    let fun correctLoopsAndTypes wk (Source t) = not (List.exists (fn x => #token x = t) wk)
          | correctLoopsAndTypes wk (Loop t) = List.exists (fn x => #token x = t) wk
          | correctLoopsAndTypes wk (TCPair (tc, cs)) =
            let val typesOfInducedConstructs = map (CSpace.typeOfToken o constructOf) cs
                val (typesOfConstructor,ty) = CSpace.csig (#constructor tc)
                val typeOfConstruct = CSpace.typeOfToken (#token tc)
            in (#subType T) (typeOfConstruct, ty)
                andalso specialises T (typesOfInducedConstructs) typesOfConstructor
                andalso List.all (fn x => not (CSpace.sameTokens (#token x) (#token tc))) wk
                andalso List.all (correctLoopsAndTypes (tc :: wk)) cs
            end
    in correctLoopsAndTypes [] c andalso coherent c
    end;*)

(*)
  (* this function simply ensures that induced constructions in a split are almost
    well formed, in the sense that there may be potential references to loops where
    the loop is not within the induced construction, but otherwise it's fine. *)
  fun almostWellFormed c =
    let fun correctLoops wk (Source t) = not (List.exists (fn x => #token x = t) wk)
          | correctLoops _ (Loop _) = true
          | correctLoops wk (TCPair (tc, cs)) =
              List.all (fn x => not (CSpace.sameTokens (#token x) (#token tc))
                        andalso not (CSpace.sameConstructors (#constructor x) (#constructor tc))) wk
              andalso List.all (correctLoops (tc :: wk)) cs
    in correctLoops [] c andalso coherent c
    end;*)
(*)
  fun tokenOfVertex (Token t) = t
    | tokenOfVertex _ = raise Match;

  fun foundationSequence c = map (tokenOfVertex o hd o rev) (CTS c);*)

  fun removeDuplicates eq [] = []
    | removeDuplicates eq (h::t) = h :: removeDuplicates eq (List.filter (fn x => not(eq x h)) t)

  fun fullTokenSequence ct =
    let fun fvs (Source t) = [t]
          | fvs (Reference t) = []
          | fvs (TCPair ({token,constructor},cs)) =
              token :: List.concat (map fvs cs)
    in fvs ct
    end

  fun isGenerator (Source t) (Source t') = CSpace.sameTokens t t'
    | isGenerator (Reference t) (Reference t') = CSpace.sameTokens t t'
    | isGenerator (TCPair ({token = t, constructor = c}, cs)) (TCPair ({token = t', constructor = c'}, cs')) =
        CSpace.sameTokens t t' andalso CSpace.sameConstructors c c'
        andalso List.allZip isGenerator cs cs'
    | isGenerator (Source t) (TCPair ({token, ...}, _)) =
        CSpace.sameTokens t token
    | isGenerator (Source t) (Reference t') =
        CSpace.sameTokens t t'
    | isGenerator _ _ = false

(*)
  exception badTrail
  fun inducedConstruction (Source t) [Token t'] =
        if CSpace.sameTokens t t'
        then Source t
        else raise badTrail
    | inducedConstruction (Loop t) [Token t'] =
        if CSpace.sameTokens t t'
        then Source t
        else raise badTrail
    | inducedConstruction (TCPair ({token = token, constructor = constructor}, cs)) (Token token'::Constructor constructor'::wk) =
        if CSpace.sameTokens token token' andalso CSpace.sameConstructors constructor constructor'
        then let fun ic (c::C) = (inducedConstruction c wk handle badTrail => ic C)
                   | ic [] = raise badTrail
             in if null wk then TCPair ({token = token, constructor = constructor}, cs) else ic cs
             end
        else raise badTrail
    | inducedConstruction (TCPair ({token = token, constructor = constructor}, cs)) [Token t'] =
        if CSpace.sameTokens token t'
        then TCPair ({token = token, constructor = constructor}, cs)
        else raise badTrail
    | inducedConstruction _ _ = raise badTrail

  exception NotASplit
  fun split c c' = map (inducedConstruction c) (CTS c')
*)
  fun fixLoops c =
    let
      fun fic _ (Source t) = (Source t)
        | fic wk (Reference t) = if List.exists (fn x => #token x = t) wk then Reference t else Source t
        | fic wk (TCPair (tc, cs)) =
            TCPair (tc, map (fic (tc::wk)) cs)
    in fic [] c
    end

  fun fixReferences ct =
    let fun fix (Source t) prev = if List.exists (fn x => x = t) prev then (Reference t,prev) else (Source t, t::prev)
          | fix (Reference t) prev = if List.exists (fn x => x = t) prev then (Reference t,prev) else (Source t, t::prev)
          | fix (TCPair (tc, cs)) prev =
            let fun fixr [] prev' = ([],prev')
                  | fixr (ct'::L) prev' =
                    (case fix ct' prev' of
                      (fixedct',tokenSeqX) => (case fixr L (tokenSeqX @ prev') of
                                                (fixedctL',tokenSeqY) => (fixedct'::fixedctL', tokenSeqY)))
                val (fixedcs,uprev) = fixr cs (#token tc :: prev)
            in (TCPair (tc, fixedcs),uprev)
            end
    in #1 (fix ct [])
    end

  fun findFirstSOME (SOME x :: _) = SOME x
    | findFirstSOME (NONE :: L) = findFirstSOME L
    | findFirstSOME [] = NONE

  fun findSubConstructionWithConstruct (Source t') t =
        if CSpace.sameTokens t' t then SOME (Source t') else NONE
    | findSubConstructionWithConstruct (Reference _) _ = NONE
    | findSubConstructionWithConstruct (TCPair (tc, cs)) t =
        if CSpace.sameTokens (#token tc) t
        then SOME (TCPair (tc, cs))
        else findFirstSOME (map (fn x => findSubConstructionWithConstruct x t) cs)

  fun takeGeneratorUntil L (Source t) = if List.exists (fn x => x = t) L then Reference t else (Source t)
    | takeGeneratorUntil _ (Reference t) = Reference t
    | takeGeneratorUntil L (TCPair (tc, cs)) =
        if List.exists (fn x => x = #token tc) L
        then Reference (#token tc)
        else TCPair (tc, map (takeGeneratorUntil L) cs)
  fun findAndExpandSubConstruction ct t =
    let val smallConstruction = valOf (findSubConstructionWithConstruct ct t)
        val tokensOfSmallConstruction = fullTokenSequence smallConstruction
        fun expandReferencesUntil (Source t') = Source t'
          | expandReferencesUntil (Reference t') = takeGeneratorUntil tokensOfSmallConstruction (valOf (findSubConstructionWithConstruct ct t'))
          | expandReferencesUntil (TCPair (tc,cs)) = TCPair (tc, map expandReferencesUntil cs)
    in expandReferencesUntil smallConstruction
    end handle Option => (print "what?";raise BadConstruction)

(*)
  (* The choice of how this function is built may seem strange, but it's made
      so that if the split is not actually a split but something like a pattern split, where
      the induced construction are specialisations, it uses the construct of the
      specialisation instead of the original token *)
  fun unsplit x =
    let fun unsplit' (Source _,[ct]) = ct
          | unsplit' (Reference _, [ct]) = Reference (constructOf ct)
          | unsplit' ((TCPair (tc,cs)), cts) =
              let fun us (c::L) icts = (case List.split(icts, length (foundationSequence c)) of
                                            (cLx,cly) => unsplit' (c, cLx) :: us L cly)
                    | us [] _ = []
              in TCPair (tc, us cs cts)
              end
          | unsplit' _ = raise NotASplit
        val result = fixLoops (unsplit' x)
      (*  val _ = if wellFormed T result then () else print "\n WARNING: " ^ toString result ^ " is malformed" *)
    in result end*)

  fun isReference (Reference _) = true
    | isReference _ = false

  fun attachAtSource ct (Source t) =
        if CSpace.sameTokens (constructOf ct) t then ct else Source t
    | attachAtSource ct (TCPair (tc, cs)) =
        if CSpace.sameTokens (constructOf ct) (#token tc)
        then (print "not attachable";(TCPair (tc, cs)))
        else TCPair (tc, map (attachAtSource ct) cs)
    | attachAtSource _ (Reference t) = Reference t


  fun replaceConstruct ct t' =
    let fun rc _ (Source t) = Source t
          | rc originalConstruct (Reference t) = if CSpace.sameTokens t originalConstruct then Reference t' else Reference t
          | rc originalConstruct (TCPair (tc, cs)) = TCPair (tc, map (rc originalConstruct) cs)
    in case ct of Source _ => Source t'
                | Reference _ => raise BadConstruction
                | TCPair ({token = t,constructor = c}, cs) => TCPair ({token = t',constructor = c}, map (rc t) cs)
    end

  fun attachConstructionAtToken (Source t) t' ct = if CSpace.sameTokens t t' then [ct] else [Source t]
    | attachConstructionAtToken (Reference t) _ _ = [Reference t]
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

end;
