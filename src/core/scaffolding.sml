import "core.sequent";
import "core.interCSpace";
import "transfer.search";

signature SCAFFOLDING =
sig 
  val graphOfOldConstruction : Pattern.construction -> Graph.graph
  val oldConstructionsOfGraph : CSpace.conSpecData -> Graph.graph -> Pattern.construction list
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

  fun applyTransferSchemas T SC st = 
    Sequent.applyBackwardAllToState T (fn i => i = 1) SC st 

  
  fun compare (st1,st2) = 
    let 
      val (A1,C1) = #sequent st1
      val (A2,C2) = #sequent st2
    in
      case (MGraph.contained C1 A1, MGraph.contained C2 A2) of
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
      val maxNumGoals = case goalLimit of SOME x => x | NONE => 5
      val maxCompSize = case compositionLimit of SOME x => x | NONE => 100
      val maxNumResults = case searchLimit of SOME x => x | NONE => 100
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