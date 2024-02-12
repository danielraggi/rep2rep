import "core.graph";

signature MSPACE =
sig
  type mTypeSystem
  type mgraph
  type map
end

structure MSpace : MSPACE =
struct
  type mTypeSystem = MGraph.mTypeSystem
  type mgraph = MGraph.mgraph
  type map = MGraph.map
end

signature SEQUENT =
sig
  include MSPACE
  type sequent = mgraph * mgraph

  (* 
    findDeltasForBackwardApp takes a pair of sequents <a1,...,an ||- c1,...,cn> and 
    <a1',...,an' ||- c1',...,cn'> and finds refinement maps of <a1,...,an ||- c1,...,cn>. 
    For each refinement map, r, it returns a pair (r,(d1,...,dn)) where (d1,...,dn) is a
    multi-space graph of deltas such that <a1' \cup d1, ..., an' \cup dn ||- c1'',...,cn''>
    is a refinement of <a1,...,an ||- c1,...,cn> and (c1'',...,cn'') is a specialisation of 
    (c1',...,cn'). Importantly, this means that <a1',...,an' ||- d1,...,dn> is an 
    application of <a1,...,an ||- c1,...,cn> to <a1',...,an' ||- c1',...,cn'>.
  *)
  val findDeltasForBackwardApp : mTypeSystem -> (int -> bool) -> string list -> sequent -> sequent -> (map * map * mgraph) Seq.seq

  val applyBackwardFree : mTypeSystem -> sequent -> sequent -> sequent Seq.seq
  val applyBackwardRestricted : mTypeSystem -> sequent -> sequent -> sequent Seq.seq
  val applyBackwardTargetting : mTypeSystem -> (int -> bool) -> sequent -> sequent -> sequent Seq.seq

  (* 
    findDeltasForForwardApp takes a pair of sequents <a1,...,an ||- c1,...,cn> and 
    <a1',...,an' ||- c1',...,cn'> and finds refinement maps of <a1,...,an ||- c1,...,cn>. 
    For each refinement map, r, it returns a pair (r,(d1,...,dn)) where (d1,...,dn) is a
    multi-space graph of deltas such that <a1',...,an' ||- d1,...,dn> is a refinement of
    <a1,...,an ||- c1,...,cn>. Importantly, this means that 
    <a1' \cup d1, ..., an' \cup dn ||- c1',...,cn'> is an application of 
    <a1,...,an ||- c1,...,cn> to <a1',...,an' ||- c1',...,cn'>.
  
  val findDeltasForForwardApp : mTypeSystem -> sequent -> sequent -> (map * mgraph) Seq.seq

  val applyForward : mTypeSystem -> sequent -> sequent -> sequent Seq.seq
*)

  type state = {sequent : sequent, discharged : mgraph, tokenNamesUsed : string list, score : real}
  type schemaData = {schema : sequent, strength : real}
  val applyBackwardToState : mTypeSystem -> (int -> bool) -> schemaData -> state -> state Seq.seq
  val applyBackwardAllToState : mTypeSystem -> (int -> bool) -> schemaData Seq.seq -> state -> state Seq.seq
end


structure Sequent : SEQUENT =
struct
  open MSpace
  type sequent = mgraph * mgraph

  open TokenMap
  infix 6 oo

  (* 
    The assumption for findDeltasForBackwardApp is that (A,C) is a schema and (A',C') is a sequent.
    It aims to find a d such that (A,C) can be refined into (A' \cup d, C'') where C'' is a specialisation of C'.
    findDeltasForBackwardApp returns (f,gf,d) where f is the refinement map of (A,C) to (A' \cup d, C''), and gf maps C' to C''.
    That's slightly stronger than the Transfer paper's version of backward application, but still ensures that
    if (A',d) is a schema then (A',C') is a schema.
    The first thing is to check that C can be embedded in C' (a more complete version would find loosenings rather than embeddings, 
    but practically this may add too many useless cases).
    If so, then we proceed to find d such that A can be reified into A' \cup d.
    There are infinitely many, so we restrict it to find 'minimal' ones.
    The idea is: for each subgraph, sA, of A, find a reification of sA into A'.
    Then take the complement of sA in A and create a copy, d, disjoint from A', of it so that A reifies into A' cup d.
    I is a list of integers that indicates the dimensions on which we DO NOT want non-trivial deltas, i.e., where (#i sA) = (#i A).
    
  *)
  fun findDeltasForBackwardApp T I tns (A,C) (A',C') =
    let
      val consequentEmbeddings = 
        MGraph.findEmbeddingsUpTo T (MGraph.tokensOfGraphQuick A,[]) emptyMap C C'

      val tokensOfAC = Graph.insertStrings (MGraph.tokenNamesOfGraphQuick A) (MGraph.tokenNamesOfGraphQuick C)
      val tokensOfAC' = Graph.insertStrings (Graph.insertStrings (MGraph.tokenNamesOfGraphQuick A') (MGraph.tokenNamesOfGraphQuick C')) tns

      fun findDeltasPerConsequentEmbedding consequentEmbedding = 
        let 
          val extendedInverseConsequentEmbedding = #1 (extendDomain (invertMap consequentEmbedding) (MGraph.tokensOfGraphQuick C') tokensOfAC)
          val extendedC = MGraph.image extendedInverseConsequentEmbedding C'  (* extension of C that mimics the structure of C' *)
          val restrictedConsequentEmbedding = restrictDomain (invertMap extendedInverseConsequentEmbedding) (MGraph.tokensOfGraphQuick A)
          (* restricting the domain of consequentEmbedding *)
          val (extendedConsequentEmbedding,newTokensUsed') = extendDomain restrictedConsequentEmbedding (MGraph.tokensOfGraphQuick extendedC) tokensOfAC'
          val consequentDelta = MGraph.image extendedConsequentEmbedding (MGraph.remove C extendedC) 
          val goalMap = extendedConsequentEmbedding oo extendedInverseConsequentEmbedding

          val subgraphsOfA = MGraph.subgraphsRestricted I A
          (*val _ = print (MGraph.toString (#1(valOf(Seq.pull subgraphsOfA))) ^ "\n")
          val _ = print (Int.toString (length (Seq.list_of subgraphsOfA)) ^ "\n")*)
          fun findPerSubgraphOfA subgraphOfA = 
            let 
              val antecedentReifications = MGraph.findReifications T extendedConsequentEmbedding subgraphOfA (MGraph.imageWeak goalMap A') 
              fun findPerReificationOfSubgraphOfA f' = 
                let 
                  val complementOfSubgraphOfA = MGraph.remove subgraphOfA A
                  val extendedMap = #1 (extendDomain f' (MGraph.tokensOfGraphQuick complementOfSubgraphOfA) (tokensOfAC' @ newTokensUsed')) (* extend domain of f' : subgraphOfA -> A' from subgraphOfA to A avoiding clashing with A' union C' *)
                  val antecedentDelta = MGraph.image extendedMap complementOfSubgraphOfA 
                in 
                  (extendedMap, goalMap, MGraph.join consequentDelta antecedentDelta) 
                end 
            in 
              Seq.map findPerReificationOfSubgraphOfA antecedentReifications
            end
        in 
          Seq.maps findPerSubgraphOfA subgraphsOfA
        end
    in
      Seq.maps findDeltasPerConsequentEmbedding consequentEmbeddings 
    end

  fun applyBackwardFree T (A,C) (A',C') = Seq.map (fn x => (A', #3 x)) (findDeltasForBackwardApp T (fn _ => false) [] (A,C) (A',C'))

  fun metaSpaceSelector M i = i < length M
  fun applyBackwardRestricted T (A,C) (A',C') = Seq.map (fn x => (A', #3 x)) (findDeltasForBackwardApp T (metaSpaceSelector C') [] (A,C) (A',C'))

  fun applyBackwardTargetting T I (A,C) (A',C') = Seq.map (fn x => (A', #3 x)) (findDeltasForBackwardApp T I [] (A,C) (A',C'))

  type state = {sequent : sequent, discharged : mgraph, tokenNamesUsed : string list, score : real}
  type schemaData = {schema : sequent, strength : real}

  fun applyBackwardToState T I {schema = (A,C), strength} state =
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


end