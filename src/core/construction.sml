import "core.cspace";
import "util.result";
import "util.diagnostic";
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
  val isTrivial : construction -> bool;

  val isGenerator : construction -> construction -> bool;
  val subConstruction : construction -> construction -> bool;
  val constructOf : construction -> CSpace.token;
  val childrenOf : construction -> construction list;
  val wellFormed : CSpace.conSpecData -> construction -> bool;
  val typeCheck : CSpace.conSpecData -> construction -> (unit, Diagnostic.t list) Result.t;
  val size : construction -> int;

  val leavesOfConstruction : construction -> CSpace.token list;
  val tokensOfConstruction : construction -> CSpace.token FiniteSet.set;

  val fixReferences : construction -> construction;
  val largestSubConstructionWithConstruct : construction -> CSpace.token -> construction
  val attachAtSource : construction -> construction -> construction;

  val replaceConstruct : construction -> CSpace.token -> construction;

  val attachConstructionAtToken : construction -> CSpace.token -> construction -> construction list;

  val minus : construction -> construction -> construction list;
  val foundationalSubConstructions : construction -> construction Seq.seq;

  val toString : construction -> string;

  exception MalformedConstructionTerm of string;

  structure R : sig
                val toString : Rpc.endpoint
                val typeCheck: (string -> CSpace.conSpecData option) -> Rpc.endpoint
            end;
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
                   "Construction.tc"
                   (Rpc.Datatype.tuple2 (CSpace.token_rpc, CSpace.constructor_rpc))
                   (fn (t, u) => {token = t, constructor = u})
                   (fn {token = t, constructor = u} => (t, u));

  fun construction_rpc_ () = Rpc.Datatype.convert
                                 "Construction.construction"
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
                       "Construction.vertex"
                       (Rpc.Datatype.either2 (CSpace.token_rpc, CSpace.constructor_rpc))
                       (fn (Rpc.Datatype.Either2.FST t) => Token t
                         | (Rpc.Datatype.Either2.SND u) => Constructor u)
                       (fn (Token t) => Rpc.Datatype.Either2.FST t
                         | (Constructor u) => Rpc.Datatype.Either2.SND u);

  val walk_rpc = Rpc.Datatype.alias
                     "Construction.walk"
                     (List.list_rpc vertex_rpc);

  fun toString (Source t) = CSpace.stringOfToken t
    | toString (Reference t) = CSpace.stringOfToken t
    | toString (TCPair ({token,constructor}, cs)) =
       CSpace.stringOfToken token ^ " <- " ^ CSpace.nameOfConstructor constructor ^ (String.stringOfList toString cs)

  fun sameTCPairs {token = t, constructor = c} {token = t', constructor = c'} =
    CSpace.sameTokens t t' andalso CSpace.sameConstructors c c'

  (* The following assumes well-formed *)
  fun same (Source t) (Source t') = CSpace.sameTokens t t'
    | same (Reference t) (Reference t') = CSpace.sameTokens t t'
    | same (TCPair (tc, cs)) (TCPair (tc', cs')) = sameTCPairs tc tc' andalso List.allZip same cs cs'
    | same _ _ = false

  fun isTrivial (TCPair _) = false
    | isTrivial _ = true

  (* The following assumes well-formed *)
  fun similar (Source t) (Source t') = CSpace.tokensHaveSameType t t'
    | similar (Reference t) (Reference t') = CSpace.tokensHaveSameType t t'
    | similar (TCPair ({token = t, constructor = c}, cs)) (TCPair ({token = t', constructor = c'}, cs')) =
        CSpace.tokensHaveSameType t t' andalso CSpace.sameConstructors c c'
        andalso List.allZip similar cs cs'
    | similar _ _ = false

  fun constructOf (Source t) = t
    | constructOf (Reference t) = t
    | constructOf (TCPair ({token, ...}, _)) = token

  fun leavesOfConstruction (Source t) = [t]
    | leavesOfConstruction (Reference t) = []
    | leavesOfConstruction (TCPair ({token, ...}, cs)) = List.concat (map leavesOfConstruction cs)

  exception MalformedConstructionTerm of string;

  fun specialises T [] [] = true
    | specialises T (ty::tys) (ty'::tys') = if (#subType T) (ty, ty') then specialises T tys tys' else false
    | specialises _ _ _ = false

  fun wellFormed CSD ct =
    let val T = #typeSystem (#typeSystemData CSD)
        fun wf (Source t) prev = (not (List.exists (fn x => x = t) prev) andalso
                                    Set.elementOf (CSpace.typeOfToken t) (#Ty T),
                                  t::prev)
          | wf (Reference t) prev = (List.exists (fn x => x = t) prev, prev)
          | wf (TCPair ({token,constructor}, [])) prev =
            if String.isPrefix "?" (CSpace.nameOfConstructor constructor)
            then (true,token::prev)
            else (false,token::prev)
          | wf (TCPair ({token,constructor}, cs)) prev =
            let val ty = CSpace.typeOfToken token
                val tys = map (CSpace.typeOfToken o constructOf) cs
              (*  val constructorFromCSpec = valOf (CSpace.findConstructorWithName (CSpace.nameOfConstructor constructor) C)
                val eqConstructors = CSpace.sameConstructors constructorFromCSpec constructor*)
                val (ctys,cty) = CSpace.csig constructor
                fun wfr [] prev' = (true,prev')
                  | wfr (ct'::L) prev' =
                    (case wf ct' prev' of
                      (WFX,tokenSeqX) => (case wfr L tokenSeqX of
                                              (WFY,tokenSeqY) => (WFX andalso WFY, tokenSeqY)))
                val (WF,uprev) = if Set.elementOf (CSpace.typeOfToken token) (#Ty T) andalso
                                    FiniteSet.exists (CSpace.sameConstructors constructor) (#constructors CSD) andalso
                                    specialises T (ty::tys) (cty::ctys) andalso
                                    not (List.exists (CSpace.sameTokens token) prev)
                                 then wfr cs (token::prev)
                                 else (false,prev)
            in (WF,uprev)
            end handle Option => (false,[])
    in #1 (wf ct [])
    end;

  fun typeCheck space ct =
      let val typeSystem = #typeSystem (#typeSystemData space);
          val types = #Ty typeSystem;
          val subType = #subType typeSystem;
          fun check (Source t) seen =
              let val notAlreadySeen =
                      if (not (List.exists (fn x => x = t) seen))
                      then Result.ok ()
                      else Result.error [
                              Diagnostic.create
                                  Diagnostic.ERROR
                                  "'Source' token has been encountered directly twice."
                                  [CSpace.nameOfToken t]];
                  val knownType =
                      if Set.elementOf (CSpace.typeOfToken t) types
                      then Result.ok ()
                      else Result.error [
                              Diagnostic.create
                                  Diagnostic.ERROR
                                  ("Token has unknown type "
                                   ^ (Type.nameOfType (CSpace.typeOfToken t))
                                   ^ ".")
                                  [CSpace.nameOfToken t]];
                  val both = Result.allUnit List.concat [notAlreadySeen, knownType];
              in (both, t::seen) end
            | check (Reference t) seen =
              let val alreadySeen =
                      if List.exists (fn x => x = t) seen
                      then Result.ok ()
                      else Result.error [
                              Diagnostic.create
                                  Diagnostic.ERROR
                                  "'Reference' token has never been seen before."
                                  [CSpace.nameOfToken t]];
              in (alreadySeen, seen) end
            | check (TCPair ({token, constructor}, cs)) seen =
              let val ty = CSpace.typeOfToken token;
                  val inToks = map constructOf cs;
                  val tys = map CSpace.typeOfToken inToks;
                  val (ctys, cty) = CSpace.csig constructor;
                  val rightLength =
                      let val l = List.length tys;
                          val lc = List.length ctys;
                      in if l = lc
                         then Result.ok ()
                         else Result.error [
                                 Diagnostic.create
                                     Diagnostic.ERROR
                                     ("Constructor needs "
                                      ^ (Int.toString lc)
                                      ^ " input tokens; only given "
                                      ^ (Int.toString l) ^ ".")
                                     (List.map CSpace.nameOfToken inToks)]
                      end;
                  fun rightType tok (conTyp, realTyp) verb =
                      if subType (realTyp, conTyp)
                      then Result.ok ()
                      else Result.error [
                              Diagnostic.create
                                  Diagnostic.ERROR
                                  ("Token has incorrect type; constructor "
                                   ^ verb
                                   ^ " "
                                   ^ (Type.nameOfType conTyp)
                                   ^ ", but token has type "
                                   ^ (Type.nameOfType realTyp)
                                   ^ ".")
                                  [CSpace.nameOfToken tok]];
                  val rightOutTy = rightType token (cty, ty) "produces";
                  val rightInTys = Result.allUnit
                                       List.concat
                                       (ListPair.map
                                            (fn (tok, tys) => rightType tok tys "requires")
                                            (inToks, (ListPair.zip (ctys, tys))));
                  val (recs, seen') =
                      List.foldl
                          (fn (c, (rs, seen)) => let val (r, seen') = check c seen;
                                                 in (r::rs, seen') end)
                          ([], token::seen)
                          cs;
                  val recursiveCheck = Result.allUnit List.concat recs;
                  val allChecks =
                      Result.allUnit List.concat
                                     [rightLength,
                                      rightOutTy,
                                      rightInTys,
                                      recursiveCheck];
              in (allChecks, seen') end;
      in #1 (check ct []) end;

  fun size (Source t) = 1
    | size (Reference t) = 0
    | size (TCPair (_,cs)) = 1 + List.foldl (fn (x,y) => size x + y) 0 cs

  exception BadConstruction

  fun removeDuplicates eq [] = []
    | removeDuplicates eq (h::t) = h :: removeDuplicates eq (List.filter (fn x => not(eq x h)) t)

  (* assumes well-formed, otherwise will contain repetition *)
  fun tokensOfConstruction ct =
    let fun fvs (Source t) = [t]
          | fvs (Reference _) = []
          | fvs (TCPair ({token,constructor},cs)) =
              token :: List.concat (map fvs cs)
    in FiniteSet.ofListQuick (fvs ct)
    end

  fun isGenerator (Source t) (Source t') = CSpace.sameTokens t t'
    | isGenerator (Reference t) (Reference t') = CSpace.sameTokens t t'
    | isGenerator (TCPair ({token = t, constructor = c}, cs)) (TCPair ({token = t', constructor = c'}, cs')) =
        CSpace.sameTokens t t' andalso CSpace.sameConstructors c c'
        andalso List.allZip isGenerator cs cs'
    | isGenerator (Source t) (TCPair ({token, ...}, _)) =
        CSpace.sameTokens t token
    | isGenerator _ _ = false

  fun fixReferences ct =
    let fun fix (Source t) prev =
              if List.exists (CSpace.sameTokens t) prev
              then (Reference t,prev)
              else (Source t, t::prev)
          | fix (Reference t) prev =
              if List.exists (CSpace.sameTokens t) prev
              then (Reference t,prev)
              else (Source t, t::prev)
          | fix (TCPair (tc, cs)) prev =
              let fun fixr [] prev' = ([],prev')
                    | fixr (ct'::L) prev' =
                      (case fix ct' prev' of (fixedct',tokenSeqX) =>
                        (case fixr L tokenSeqX of (fixedctL',tokenSeqY) =>
                          (fixedct'::fixedctL', tokenSeqY)))
                  val _ = if List.exists (CSpace.sameTokens (#token tc)) prev
                          then (raise MalformedConstructionTerm (toString ct))
                          else ()
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

  exception TokenNotPresent of (string * string)
  fun takeGeneratorUntil L (Source t) =
        if List.exists (fn x => CSpace.sameTokens x t) L
        then Reference t
        else Source t
    | takeGeneratorUntil _ (Reference t) = Reference t
    | takeGeneratorUntil L (TCPair (tc, cs)) =
        if List.exists (fn x => CSpace.sameTokens x (#token tc)) L
        then Reference (#token tc)
        else TCPair (tc, map (takeGeneratorUntil L) cs)
  fun largestSubConstructionWithConstruct ct t =
    let val smallConstruction = valOf (findSubConstructionWithConstruct ct t)
        val tokensOfSmallConstruction = tokensOfConstruction smallConstruction
        fun expandReferencesUntil (Source t') = Source t'
          | expandReferencesUntil (Reference t') = takeGeneratorUntil tokensOfSmallConstruction (valOf (findSubConstructionWithConstruct ct t'))
          | expandReferencesUntil (TCPair (tc,cs)) = TCPair (tc, map expandReferencesUntil cs)
    in fixReferences (expandReferencesUntil smallConstruction)
    end handle Option => raise TokenNotPresent (toString ct,CSpace.stringOfToken t)

  fun subConstruction ct ct' =
    isGenerator ct (largestSubConstructionWithConstruct ct' (constructOf ct))
    handle TokenNotPresent _ => false

  fun childrenOf (Source t) = []
    | childrenOf (Reference t) = []
    | childrenOf (TCPair (tc,cts)) = cts

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
        then (if isGenerator ct (TCPair (tc, cs))
              then [TCPair (tc, cs)]
              else if isGenerator (TCPair (tc, cs)) ct
                   then [ct]
                   else [TCPair (tc, cs), ct])
        else
          let val csr = map (fn x => attachConstructionAtToken x t ct) cs
              fun mkNew xs = TCPair (tc, xs)
          in map mkNew (List.listProduct csr)
          end

  exception NotGenerator;
  fun minusGenerator (TCPair (tc,cts)) (TCPair (tc',cts')) =
        let fun minusL [] [] = []
              | minusL (x::L) (x'::L') = minusGenerator x x' @ minusL L L'
              | minusL _ _ = raise NotGenerator
        in if tc = tc'
           then minusL cts cts'
           else raise NotGenerator
        end
    | minusGenerator (Reference t) (Reference t') =
        if CSpace.sameTokens t t'
        then []
        else raise NotGenerator
    | minusGenerator ct (Source t') =
        if CSpace.sameTokens (constructOf ct) t'
        then childrenOf ct
        else raise NotGenerator
    | minusGenerator _ _ = raise NotGenerator;

  fun minusTCPair ct tc' =
    let fun minusTC' (TCPair (tc,cts)) =
            if sameTCPairs tc tc'
            then (Source (#token tc), List.filter (fn x => not (isTrivial x)) cts)
            else (case map minusTC' cts of R =>
                  (TCPair (tc, map #1 R), List.concat (map #2 R)))
          | minusTC' (Source t) = (Source t,[])
          | minusTC' (Reference t) = (Source t,[])
        val (c,L) = minusTC' ct
    in if not (isTrivial c) orelse null L then [c] @ L else L
    end

  fun minusTCPairs ct (tc::L) =
        List.maps (fn x => minusTCPair x tc) (minusTCPairs ct L)
      (*)  List.maps (fn x => minusTCPairs x L) (minusTCPair ct tc)*)
    | minusTCPairs ct [] = [ct]

  fun collectTCPairs (TCPair (tc,cts)) = tc :: List.maps collectTCPairs cts
    | collectTCPairs _ = []

  fun minus ct ct' = minusTCPairs ct (collectTCPairs ct')

  fun foundationalSubConstructions (Source t) = Seq.single (Source t)
    | foundationalSubConstructions (Reference t) = Seq.single (Reference t)
    | foundationalSubConstructions (TCPair (tc,cs)) =
        Seq.cons (TCPair (tc,cs)) (Seq.maps foundationalSubConstructions (Seq.of_list cs))


  structure R = struct
  fun url s = "core.construction." ^ s;

  val toString = Rpc.provide (url "toString",
                              construction_rpc,
                              String.string_rpc)
                             toString;

  val typeCheck =
   fn getSpace =>
      Rpc.provide (url "typeCheck",
                   Rpc.Datatype.tuple2 (String.string_rpc, construction_rpc),
                   Result.t_rpc (unit_rpc, List.list_rpc Diagnostic.t_rpc))
                  (fn (space, construction) =>
                      case Option.map (fn s => typeCheck s construction) (getSpace space) of
                          NONE => Result.error [
                                     Diagnostic.create
                                         Diagnostic.ERROR
                                         ("Unknown Construction Space " ^ space)
                                         []]
                        | SOME r => r);
  end;

end;
