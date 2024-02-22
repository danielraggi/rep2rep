import "core.pattern";
import "core.sequent";
(*import "core.interCSpace";*)
import "transfer.search";
(* scaffolding uses old constructions as a medium between parsing and schema-application-to-sequents. 
    Meant as a temporary structure until the parsers are updated. *)

signature SCAFFOLDING =
sig 

  val graphOfOldConstruction : Pattern.construction -> Graph.graph
  val oldConstructionsOfGraph : CSpace.conSpecData -> Graph.graph -> Pattern.construction list
  val makeInstantiationOfTypeVars : MSpace.mTypeSystem -> Type.typ list -> Type.typ Seq.seq -> (Type.typ -> Type.typ option) Seq.seq;
  (*val schemaOfOldTransferSchema : InterCSpace.tSchemaData -> Sequent.schemaData*)
  val applyTransferSchemas : MSpace.mTypeSystem -> Sequent.schemaData Seq.seq -> Sequent.state -> Sequent.state Seq.seq
  val adaptSchema : string list -> Sequent.schemaData -> Sequent.schemaData
  val transfer : int option * int option * int option
                  -> bool
                  -> bool
                  -> bool
                  -> Sequent.mTypeSystem
                  -> Sequent.schemaData Seq.seq
                  -> Sequent.state
                  -> Sequent.state Seq.seq
  val initState : CSpace.conSpecData -> (* Source Constructor Specification *)
                  CSpace.conSpecData -> (* Target Constructor Specification *)
                  CSpace.conSpecData -> (* Inter-space Constructor Specification *)
                  Graph.graph -> (* The construction to transform *)
                  Graph.graph -> (* The goal to satisfy *)
                  Sequent.state
end

structure Scaffolding : SCAFFOLDING =
struct

  exception Fail

  fun graphOfOldConstruction ct =
    let
      fun gooc (Pattern.Source t) = [{token = t, inputs = []}]
        | gooc (Pattern.Reference t) = [{token = t, inputs = []}]
        | gooc (Pattern.TCPair (tc,ch)) = {token = #token tc, inputs = [{constructor = CSpace.nameOfConstructor (#constructor tc), inputTokens = map Pattern.constructOf ch}]} :: List.flatmap gooc ch
    in Graph.factorise (gooc ct)
    end

  fun unzip [] = ([],[])
    | unzip ((x,y)::L) = case unzip L of (Lx,Ly) => (x::Lx,y::Ly)



fun findTINForToken _ [] = NONE
  | findTINForToken t (tin::g) = if CSpace.sameTokens t (#token tin) then SOME tin else findTINForToken t g
fun assessTokenHierarchy (g:Graph.graph) t = 
  1 + (List.max (fn (x,y) => Int.compare (x,y)) (map (assessTokenHierarchy g) (List.filter (fn x => not (CSpace.sameTokens x t)) (List.flatmap #inputTokens (#inputs (valOf (findTINForToken t g)))))))  handle Empty => 1 | Option => 0
fun assignTokenHierarchy _ [] _ = []
  | assignTokenHierarchy tks (tin::g:Graph.graph) g' =
  {h = assessTokenHierarchy g' (#token tin), tin = tin} :: assignTokenHierarchy ((#token tin) :: tks) g g'

fun orderByHierarchy (g:Graph.graph) = map #tin (List.mergesort (fn (x,y) => Int.compare(#h y,#h x)) (assignTokenHierarchy [] g g))




  fun oldConstructionsOfGraph CS g =
    let
      fun getConstructor cn = case CSpace.findConstructorWithName cn CS of SOME c => c | NONE => (print ("constructor " ^cn ^ " not found"); raise Option)
      fun tokensMatchConstructs [] [] = true
        | tokensMatchConstructs (tk::tks) (ct::cts) = CSpace.sameTokens tk (Pattern.constructOf ct) andalso tokensMatchConstructs tks cts
        | tokensMatchConstructs _ _ = false
      fun attachDownwards {token,inputs = []} (Pattern.Source t) = (CSpace.sameTokens token t, Pattern.Source t)
        | attachDownwards {token,inputs = [{constructor,inputTokens}]} (Pattern.Source t) = 
            if CSpace.sameTokens token t then 
              (true, Pattern.TCPair ({token = token, constructor = getConstructor constructor}, map Pattern.Source inputTokens))
            else 
              (false, Pattern.Source t)
        | attachDownwards {token,inputs = []} (Pattern.TCPair (tc,ch)) = (CSpace.sameTokens token (#token tc), Pattern.TCPair (tc,ch))
        | attachDownwards (tin as {token,inputs = [{constructor,inputTokens}]}) (Pattern.TCPair (tc,ch)) = 
            if CSpace.sameTokens token (#token tc) andalso constructor = CSpace.nameOfConstructor (#constructor tc) andalso tokensMatchConstructs inputTokens ch then
              (true,Pattern.TCPair (tc,ch))
            else
              (case unzip (map (attachDownwards tin) ch) of (X,CH) =>
                (List.exists (fn x => x) X, Pattern.TCPair (tc,CH)))
        | attachDownwards {token,inputs = []} (Pattern.Reference t) = (CSpace.sameTokens token t,Pattern.Reference t)
        | attachDownwards tin (Pattern.Reference t) = (false,Pattern.Reference t)
        | attachDownwards _ _ = (print "can't attach downwards";raise Match)

      fun makeFromTokenListAndAttach [] ct = (false, [])
        | makeFromTokenListAndAttach (tk::tks) ct = 
            if CSpace.sameTokens tk (Pattern.constructOf ct) then 
              (true,ct :: map Pattern.Source tks)
            else 
              let val (x,cts) = makeFromTokenListAndAttach tks ct 
              in (x, Pattern.Source tk :: cts) 
              end
      fun attach (tin as {token,inputs = []}) ct = attachDownwards tin ct
        | attach (tin as {token,inputs = [{constructor,inputTokens}]}) ct = 
          let val (x,ch) = makeFromTokenListAndAttach inputTokens ct 
          in if x then (x,Pattern.TCPair ({token = token, constructor = getConstructor constructor}, ch)) else attachDownwards tin ct
          end
        | attach _ _ = raise Fail
      fun ocotinSingle ({token,inputs = []}) = Pattern.Source token
        | ocotinSingle ({token,inputs = [{constructor,inputTokens}]}) = Pattern.TCPair ({token = token, constructor = getConstructor constructor}, map Pattern.Source inputTokens)
        | ocotinSingle _ = raise Fail
      fun ocotin tin [] = [ocotinSingle tin]
        | ocotin tin (ct::cts) = 
          let val (x,ct') = attach tin ct 
          in if x then (ct'::cts) else ct :: ocotin tin cts
          end
      fun ocog [] cts = cts
        | ocog (tin::g') cts = ocog g' (ocotin tin cts)
    in ocog (orderByHierarchy (Graph.expand g)) []
    end

(*
  fun schemaOfOldTransferSchema tSchemaData =
    let
      val tschema = #tSchema tSchemaData
      val s = graphOfOldConstruction (#source tschema)
      val t = graphOfOldConstruction (#target tschema)
      val a = Graph.factorise (List.flatmap graphOfOldConstruction (#antecedent tschema))
      val c = graphOfOldConstruction (#consequent tschema)
    in 
      {schema = ([s,t,a],[Graph.empty,Graph.empty,c]), strength = #strength tSchemaData}
    end*)

  fun makeInstantiationOfTypeVars _ [] _ = Seq.single (fn _ => NONE)
    | makeInstantiationOfTypeVars T (tyVar::tyVars) tys =
    let val tys' = Seq.filter (fn ty => (*#subType (List.last T)*) ((Type.parentOfDanglyType ty)=(Type.parentOfDanglyType tyVar)) handle badType => false) tys
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

  fun adaptSchema CSN {schema = (A,C), strength, name, conSpecNames} =
    let
      val empty = Graph.empty
      fun whichItem _ _ [] = NONE
        | whichItem i s (x::xs) = if s = x then SOME i else whichItem (i+1) s xs
      fun makeFun _ [] = (fn _ => NONE)
        | makeFun i (x::xs) = (fn j => if i = j then whichItem 0 x conSpecNames else makeFun (i+1) xs j)
      val f = makeFun 0 CSN
      fun makeNewSchema _ [] = ([],[])
        | makeNewSchema i (_::xs) = 
          let val (A',C') = makeNewSchema (i+1) xs 
          in case f i of 
                SOME j => (List.nth(A,j) :: A', List.nth(C,j) :: C')
              | NONE => (empty :: A', empty :: C')
          end
      val x = makeNewSchema 0 CSN;
    in {schema = makeNewSchema 0 CSN, strength = strength, name = name, conSpecNames = CSN}
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
      Sequent.applyBackwardAllToState T (fn i => i = 1) SC' st 
    end
  
  fun compare (st1,st2) = 
    let 
      val (A1,C1) = #sequent st1
      val (A2,C2) = #sequent st2
      val cnq1 = List.last C1
      val cnq2 = List.last C2
      val anc1 = List.last A1
      val anc2 = List.last A2
      fun score st = #score st / Real.fromInt (MGraph.size (#2 (#sequent st)))
    in
      case (Graph.contained cnq1 anc1, Graph.contained cnq2 anc2) of
          (true,false) => LESS
        | (false,true) => GREATER
        | _ => Real.compare (score st2, score st1)
    end

  fun ignore maxNumGoals maxNumResults maxCompSize unistructured (st,L) =
    let
      val (A',C') = #sequent st
    in 
      (Graph.numberOfConstructors (List.last C') > maxNumGoals orelse 
      length L > maxNumResults orelse
      Graph.size (List.nth(C',1)) > maxCompSize) 
    end

  fun transfer (goalLimit,compositionLimit,searchLimit) eager iterative unistructured T SC state =
    let
      val maxNumGoals = case goalLimit of SOME x => x | NONE => 20
      val maxCompSize = case compositionLimit of SOME x => x | NONE => 500
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