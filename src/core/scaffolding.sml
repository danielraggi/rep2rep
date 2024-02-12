import "core.sequent";
import "core.interCSpace";
import "transfer.search";

signature SCAFFOLDING =
sig 
  val graphOfOldConstruction : Pattern.construction -> Graph.graph
  val oldConstructionsOfGraph : CSpace.conSpecData -> Graph.graph -> Pattern.construction list
  val makeInstantiationOfTypeVars : MSpace.mTypeSystem -> Type.typ list -> Type.typ list -> (Type.typ -> Type.typ option) list;
  val schemaOfOldTransferSchema : InterCSpace.tSchemaData -> Sequent.schemaData
  val applyTransferSchemas : MSpace.mTypeSystem -> Sequent.schemaData Seq.seq -> Sequent.state -> Sequent.state Seq.seq
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
                  Construction.construction -> (* The construction to transform *)
                  Construction.construction -> (* The goal to satisfy *)
                  Sequent.state
end

structure Scaffolding : SCAFFOLDING =
struct

  fun graphOfOldConstruction ct =
    let
      fun gooc (Pattern.Source t) = [{token = t, inputs = []}]
        | gooc (Pattern.Reference t) = [{token = t, inputs = []}]
        | gooc (Pattern.TCPair (tc,ch)) = {token = #token tc, inputs = [{constructor = CSpace.nameOfConstructor (#constructor tc), inputTokens = map Pattern.constructOf ch}]} :: List.flatmap gooc ch
    in Graph.factorise (gooc ct)
    end

  fun unzip [] = ([],[])
    | unzip ((x,y)::L) = case unzip L of (Lx,Ly) => (x::Lx,y::Ly)

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
      fun ocotinSingle ({token,inputs = []}) = Pattern.Source token
        | ocotinSingle ({token,inputs = [{constructor,inputTokens}]}) = Pattern.TCPair ({token = token, constructor = getConstructor constructor}, map Pattern.Source inputTokens)
      fun ocotin tin [] = [ocotinSingle tin]
        | ocotin tin (ct::cts) = 
          let val (x,ct') = attach tin ct 
          in if x then (ct'::cts) else ct :: ocotin tin cts
          end
      fun ocog [] cts = cts
        | ocog (tin::g') cts = ocog g' (ocotin tin cts)
    in ocog (Graph.expand g) []
    end

  fun schemaOfOldTransferSchema tSchemaData =
    let
      val tschema = #tSchema tSchemaData
      val s = graphOfOldConstruction (#source tschema)
      val t = graphOfOldConstruction (#target tschema)
      val a = Graph.factorise (List.flatmap graphOfOldConstruction (#antecedent tschema))
      val c = graphOfOldConstruction (#consequent tschema)
    in 
      {schema = ([s,t,a],[Graph.empty,Graph.empty,c]), strength = #strength tSchemaData}
    end

  fun makeInstantiationOfTypeVars _ [] _ = [(fn _ => NONE)]
    | makeInstantiationOfTypeVars T (tyVar::tyVars) tys =
    let val tys' = List.filter (fn ty => (*#subType (List.last T)*) ((Type.parentOfDanglyType ty)=(Type.parentOfDanglyType tyVar)) handle badType => false) tys
    in List.flatmap (fn f => (List.map (fn ty => (fn x => if Type.equal tyVar x then SOME ty else f x)) tys')) (makeInstantiationOfTypeVars T tyVars tys)
    end

  fun makeTokenMapForInstantiationOfTypeVars f = (fn t => case f (CSpace.typeOfToken t) of SOME ty => SOME (CSpace.makeToken (CSpace.nameOfToken t) ty) | NONE => SOME t, fn _ => NONE)

  fun schemasOfVarSchema T tys {schema = (A,C), strength} =
    let
      fun getTyVars [] = []
        | getTyVars ([]::mg) = getTyVars mg
        | getTyVars ((tin::g)::mg) = 
            (case (CSpace.typeOfToken (#token tin),getTyVars (g::mg)) of 
                (ty,tyVars) => if Type.isTypeVar ty andalso not(List.exists (fn x => Type.equal x ty) tyVars) then ty :: tyVars 
                               else tyVars)
      val tyVars = getTyVars (A @ C)
      val tokenMaps = List.map makeTokenMapForInstantiationOfTypeVars (makeInstantiationOfTypeVars T tyVars tys)
      val R = List.map (fn f => {schema = (MGraph.image f A, MGraph.image f C), strength = strength}) tokenMaps
    in Seq.of_list R
      (*if null tyVars then [{schema = (A,C), strength = strength}] else Seq.of_list R*)
    end

  fun typesInSequent ([],[]) = []
    | typesInSequent ([],([]::C)) = typesInSequent ([],C)
    | typesInSequent ([],((tin::g)::C)) = (case (CSpace.typeOfToken (#token tin), typesInSequent ([],(g::C))) of (ty,tys) => if not(List.exists (fn x => Type.equal x ty) tys) then ty :: tys else tys)
    | typesInSequent (([]::A),C) = typesInSequent (A,C)
    | typesInSequent (((tin::g)::A),C) = (case (CSpace.typeOfToken (#token tin), typesInSequent (g::A,C)) of (ty,tys) => if not(List.exists (fn x => Type.equal x ty) tys) then ty :: tys else tys)
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
    in
      case (Graph.contained (List.last C1) (List.last A1), Graph.contained (List.last C2) (List.last A2)) of
          (true,false) => LESS
        | (false,true) => GREATER
        | _ => Real.compare (#score st2, #score st1)
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
      val maxCompSize = case compositionLimit of SOME x => x | NONE => 1000
      val maxNumResults = case searchLimit of SOME x => x | NONE => 10000
      val ignT = ignore maxNumGoals maxNumResults maxCompSize unistructured
      val stop = if eager then (fn x => case #sequent x of (A',C') => MGraph.contained C' A') else (fn _ => false)
    in
      Search.bestFirstAll (applyTransferSchemas T SC) compare ignT (fn _ => false) stop state 
    end
  
  fun initState sCSD tCSD iCSD ct goal =
    let val tTS = #typeSystem (#typeSystemData tCSD)
        val targetTokens = FiniteSet.filter
                               (fn x => Set.elementOf (CSpace.typeOfToken x) (#Ty tTS) andalso
                                        not (FiniteSet.elementOf x (Construction.tokensOfConstruction ct)))
                               (Construction.leavesOfConstruction goal);
        val sequent = ([graphOfOldConstruction ct, Graph.empty, Graph.empty], [Graph.empty, Graph.makeFromTokens targetTokens, graphOfOldConstruction goal])
    in {sequent = sequent, discharged = [Graph.empty,Graph.empty,Graph.empty], tokenNamesUsed = [], score = 0.0}
    end

end