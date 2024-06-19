import "core.sequent";
import "transfer.search";

signature STATE =
sig 

  include SEQUENT

  type state = {sequent : sequent, discharged : mgraph, tokenNamesUsed : string list, score : real}
  type schemaData = {name: string, conSpecNames : string list, schema : sequent, strength : real}
  val stringOfSchemaData : schemaData -> string;
  val applyBackwardToState : mTypeSystem -> (int -> bool) -> schemaData -> state -> state Seq.seq
  val applyBackwardAllToState : mTypeSystem -> (int -> bool) -> schemaData Seq.seq -> state -> state Seq.seq

  val makeInstantiationOfTypeVars : MSpace.mTypeSystem -> Type.typ list -> Type.typ Seq.seq -> (Type.typ -> Type.typ option) Seq.seq;
  val applyTransferSchemas : MSpace.mTypeSystem -> schemaData Seq.seq -> state -> state Seq.seq
  val score : state -> real;

  val transfer : int option * int option * int option
                  -> bool
                  -> bool
                  -> bool
                  -> mTypeSystem
                  -> schemaData Seq.seq
                  -> state
                  -> state Seq.seq

  val initState : CSpace.conSpecData -> (* Source Constructor Specification *)
                  CSpace.conSpecData -> (* Target Constructor Specification *)
                  CSpace.conSpecData -> (* Inter-space Constructor Specification *)
                  Graph.graph -> (* The construction to transform *)
                  Graph.graph -> (* The goal to satisfy *)
                  state
end

structure State : STATE =
struct

  open Sequent
  type state = {sequent : sequent, discharged : mgraph, tokenNamesUsed : string list, score : real}
  type schemaData = {name: string, conSpecNames : string list, schema : sequent, strength : real}

  fun stringOfSchemaData {name,conSpecNames,schema = (A,C),strength} =
    let val s = name ^ ":" ^ List.toString (fn x => x) conSpecNames ^ " \n" ^ MGraph.toString A ^ "\n" ^ MGraph.toString C
    in s
    end

  fun wellFormedSchema conSpecNames (A,C) = 
    MGraph.wellFormed conSpecNames A andalso MGraph.wellFormed conSpecNames C

  fun applyBackwardToState T I {schema = (A,C), strength,...} state =
    let
      val (A',C') = #sequent state
      val discharged = #discharged state
      val tokenNamesUsed = #tokenNamesUsed state
      val newscore = #score state + strength
      val deltas = findDeltasForBackwardApp T I tokenNamesUsed (A,C) (A',C')
      fun makeResult (f,gf,D) = 
        let
          val freshlyDischarged = MGraph.image f C 
          val dischargedUpdated = MGraph.imageWeak gf discharged
          val discharged = MGraph.join freshlyDischarged dischargedUpdated
          val newTokenNamesUsed = Graph.insertStrings (MGraph.tokenNamesOfGraphQuick D) (MGraph.tokenNamesOfGraphQuick discharged)
        in
          {sequent = (A',D), discharged = discharged, tokenNamesUsed = newTokenNamesUsed, score = newscore} 
        end
    in
      Seq.map makeResult deltas 
    end 

  fun applyBackwardAllToState T I SC st =
      Seq.maps (fn sc => applyBackwardToState T I sc st) SC 


  exception Fail

  fun findTINForToken _ [] = NONE
    | findTINForToken t (tin::g) = if CSpace.sameTokens t (#token tin) then SOME tin else findTINForToken t g
  fun assessTokenHierarchy tks (g:Graph.graph) t = 
    1 + (List.max (fn (x,y) => Int.compare (x,y)) (map (assessTokenHierarchy (t::tks) g) (List.filter (fn x => not (List.exists (fn y => CSpace.sameTokens x y) tks)) (List.flatmap #inputTokens (#inputs (valOf (findTINForToken t g)))))))  handle Empty => 1 | Option => 0
  fun assignTokenHierarchy [] _ = []
    | assignTokenHierarchy (tin::g:Graph.graph) g' =
    {h = assessTokenHierarchy [] g' (#token tin), tin = tin} :: assignTokenHierarchy g g'

  fun orderByHierarchy (g:Graph.graph) = map #tin (List.mergesort (fn (x,y) => Int.compare(#h y,#h x)) (assignTokenHierarchy g g))


  fun makeInstantiationOfTypeVars _ [] _ = Seq.single (fn _ => NONE)
    | makeInstantiationOfTypeVars T (tyVar::tyVars) tys =
    let val tys' = Seq.filter (fn ty => (Type.parentOfDanglyType ty = Type.parentOfDanglyType tyVar) handle badType => false) tys
    in Seq.maps (fn f => (Seq.map (fn ty => (fn x => if Type.equal tyVar x then SOME ty else f x)) tys')) (makeInstantiationOfTypeVars T tyVars tys)
    end

  fun makeTokenMapForInstantiationOfTypeVars f = (fn t => case f (CSpace.typeOfToken t) of SOME ty => SOME (CSpace.makeToken (CSpace.nameOfToken t) ty) | NONE => SOME t, fn _ => NONE)

  fun schemasOfVarSchema T tys {schema = (A,C), strength, name, conSpecNames} =
    let
      fun getTyVars [] = []
        | getTyVars ([]::mg) = getTyVars mg
        | getTyVars ((tin::g)::mg) = 
            (case (CSpace.typeOfToken (#token tin),getTyVars (g::mg)) of 
                (ty,tyVars) => if Type.isTypeVar ty andalso not(List.exists (fn x => Type.equal x ty) tyVars) then ty :: tyVars 
                               else tyVars)
      val tyVars = getTyVars (A @ C)
      val tokenMaps = Seq.map makeTokenMapForInstantiationOfTypeVars (makeInstantiationOfTypeVars T tyVars tys)
      fun updateSchemaForMap f = {schema = (MGraph.image f A, MGraph.image f C), strength = strength, name = name, conSpecNames = conSpecNames}
    in Seq.map (updateSchemaForMap o makeTokenMapForInstantiationOfTypeVars) (makeInstantiationOfTypeVars T tyVars tys)
      (*if null tyVars then [{schema = (A,C), strength = strength}] else R*)
    end

  fun typesInSequent ([],[]) = Seq.empty
    | typesInSequent ([],([]::C)) = typesInSequent ([],C)
    | typesInSequent ([],((tin::g)::C)) = 
      (case (CSpace.typeOfToken (#token tin), typesInSequent ([],(g::C))) of 
        (ty,tys) => if not(Seq.exists (fn x => Type.equal x ty) tys) then Seq.cons ty tys else tys)
    | typesInSequent (([]::A),C) = typesInSequent (A,C)
    | typesInSequent (((tin::g)::A),C) = 
      (case (CSpace.typeOfToken (#token tin), typesInSequent (g::A,C)) of 
        (ty,tys) => if not(Seq.exists (fn x => Type.equal x ty) tys) then Seq.cons ty tys else tys)

  fun applyTransferSchemas T SC st =
    let
      val tys = typesInSequent (#sequent st)
      val SC' = Seq.maps (schemasOfVarSchema T tys) SC
    in
      applyBackwardAllToState T (fn i => i = 1) SC' st 
    end
  
  fun score st =
    let val (_,C) = #sequent st
    in 10.0 * #score st / (1.0 + Real.fromInt (MGraph.size C))
    end

  fun compare (st1,st2) = 
    let 
      val (A1,C1) = #sequent st1
      val (A2,C2) = #sequent st2
      val cnq1 = List.last C1
      val cnq2 = List.last C2
      val anc1 = List.last A1
      val anc2 = List.last A2
    in
      case (Graph.contained cnq1 anc1, Graph.contained cnq2 anc2) of
          (true,false) => LESS
        | (false,true) => GREATER
        | _ => (if MGraph.equal C1 C2 andalso MGraph.equal A1 A2 then 
                  EQUAL
                else
                  case Real.compare (score st2, score st1) of 
                    EQUAL => LESS
                  | ord => ord)
    end

  fun ignore maxNumGoals maxNumResults maxCompSize unistructured (st,L) =
    let
      val (_,C') = #sequent st
    in 
      (Graph.numberOfConstructors (List.last C') > maxNumGoals orelse 
      length L > maxNumResults orelse
      Graph.size (List.nth(C',1)) > maxCompSize) 
    end

  fun transfer (goalLimit,compositionLimit,searchLimit) eager iterative unistructured T SC state =
    let
      val maxNumGoals = case goalLimit of SOME x => x | NONE => 20
      val maxCompSize = case compositionLimit of SOME x => x | NONE => 100
      val maxNumResults = case searchLimit of SOME x => x | NONE => 500
      val ignT = ignore maxNumGoals maxNumResults maxCompSize unistructured
      val stop = if eager then (fn x => case #sequent x of (A',C') => MGraph.contained C' A') else (fn _ => false)
    in
      Search.bestFirstAll (applyTransferSchemas T SC) compare ignT (fn _ => false) stop state 
    end
  
  fun initState sCSD tCSD iCSD graph goal =
    let val tTS = #typeSystem (#typeSystemData tCSD)
        val targetTokens = FiniteSet.filter
                               (fn x => Set.elementOf (CSpace.typeOfToken x) (#Ty tTS) andalso
                                        not (FiniteSet.elementOf x (Graph.tokensOfGraphQuick graph)))
                               (Graph.tokensOfGraphQuick goal);
        val sequent = ([graph, Graph.empty, Graph.empty], [Graph.empty, Graph.makeFromTokens targetTokens, goal])
    in {sequent = sequent, discharged = [Graph.empty,Graph.empty,Graph.empty], tokenNamesUsed = [], score = 0.0}
    end

end