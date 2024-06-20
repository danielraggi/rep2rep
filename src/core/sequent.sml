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
  val findDeltasForBackwardApp : mTypeSystem -> (int -> bool) -> string list -> sequent -> sequent -> (sequent * map * map * mgraph) Seq.seq

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

end


structure Sequent : SEQUENT =
struct
  open MSpace
  type sequent = mgraph * mgraph

  open TokenMap
  infix 6 oo

  (* Given consequentEmbedding: C -> C', we adapt (A,C) and (A',C') so that (A,C) is directly applicable to (A',C').
     Everything done is valid, i.e., (updatedA,updatedB) is still a schema, and the validity of (updatedA',updatedC') implies the validity of (A',C'). *)
  fun specialiseSchemaForConsequentEmbedding T consequentEmbedding (A,C) (A',C') =
    let 
      fun ssfce (f,f') _ [] = (f,f')
        | ssfce (f,f') (T'::TT') ([]::G) = ssfce (f,f') TT' G
        | ssfce (f,f') (T'::TT') ((tin::g)::G) = 
          let
            val t = #token tin 
            val t' = valOf (applyMap consequentEmbedding t)
            val (newTok,newTok') = case Type.min (#subType T') (CSpace.typeOfToken t,CSpace.typeOfToken t') of 
                            SOME mt => (CSpace.makeToken (CSpace.nameOfToken t) mt,CSpace.makeToken (CSpace.nameOfToken t') mt)
                          | NONE => raise Fail "min type"
          in ssfce (addPair (newTok,newTok') f, addPair (t',newTok') f') (T'::TT') (g::G)
          end
        | ssfce _ _ _ = raise Match
      val (newConsequentEmbedding,goalMap) = ssfce (emptyMap,emptyMap) T C
      val updatedC = MGraph.image ((invertMap newConsequentEmbedding) oo goalMap oo consequentEmbedding) C
      val updatedA = MGraph.imageWeak ((invertMap newConsequentEmbedding) oo goalMap oo consequentEmbedding) A
      val updatedC' = MGraph.imageWeak goalMap C'
      val updatedA' = MGraph.imageWeakTypeGeneralising T goalMap A'
    in
      ((updatedA,updatedC),(updatedA',updatedC'),newConsequentEmbedding,goalMap)
    end 

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
      val tokensOfA = MGraph.tokensOfGraphQuick A
      val consequentEmbeddings = 
        MGraph.findEmbeddingsUpTo T (tokensOfA,[]) emptyMap C C'

      fun findDeltasPerConsequentEmbedding consequentEmbedding = 
        let 
          val ((updatedA,updatedC),(updatedA',updatedC'),newConsequentEmbedding,goalMap) = specialiseSchemaForConsequentEmbedding T consequentEmbedding (A,C) (A',C')
          val tokensOfAC' = Graph.insertStrings (Graph.insertStrings (MGraph.tokenNamesOfGraphQuick updatedA') (MGraph.tokenNamesOfGraphQuick updatedC')) tns
          
          val consequentDelta = MGraph.remove (MGraph.image newConsequentEmbedding updatedC) updatedC' 
          val subgraphsOfA = MGraph.subgraphsRestricted I updatedA
          fun findPerSubgraphOfA subgraphOfA = 
            let 
              val antecedentReifications = MGraph.findReifications T newConsequentEmbedding subgraphOfA updatedA'
              val complementOfSubgraphOfA = MGraph.remove subgraphOfA updatedA
              fun findPerReificationOfSubgraphOfA f' = 
                let 
                  val (extendedMap,_) = extendDomain f' (MGraph.tokensOfGraphQuick complementOfSubgraphOfA) (tokensOfAC') (* extend domain of f' : subgraphOfA -> A' from subgraphOfA to A avoiding clashing with A' union C' *)
                  val antecedentDelta = MGraph.image extendedMap complementOfSubgraphOfA
                in 
                  ((updatedA,updatedC), extendedMap, goalMap, MGraph.join consequentDelta antecedentDelta) 
                end
            in 
              Seq.map findPerReificationOfSubgraphOfA antecedentReifications
            end
        in 
          Seq.maps findPerSubgraphOfA subgraphsOfA
        end handle Fail "type generalising" => Seq.empty | Fail "min type" => Seq.empty
    in
      Seq.maps findDeltasPerConsequentEmbedding consequentEmbeddings 
    end 

  fun applyBackwardFree T (A,C) (A',C') = Seq.map (fn x => (A', #4 x)) (findDeltasForBackwardApp T (fn _ => false) [] (A,C) (A',C'))

  fun metaSpaceSelector M i = i < length M
  fun applyBackwardRestricted T (A,C) (A',C') = Seq.map (fn x => (A', #4 x)) (findDeltasForBackwardApp T (metaSpaceSelector C') [] (A,C) (A',C'))

  fun applyBackwardTargetting T I (A,C) (A',C') = Seq.map (fn x => (A', #4 x)) (findDeltasForBackwardApp T I [] (A,C) (A',C'))

end