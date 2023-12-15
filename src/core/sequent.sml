import "core.graph";
import "transfer.search";

signature SEQUENT =
sig
  type mgraph
  type map
  type sequent = mgraph * mgraph

  (* 
    findDeltasForBackwardApp takes a pair of sequents <a1,...,an ||- c1,...,cn> and 
    <a1',...,an' ||- c1',...,cn'> and finds refinement maps of <a1,...,an ||- c1,...,cn>. 
    For each refinement map, r, it returns a pair (r,(d1,...,dn)) where (d1,...,dn) is a
    multi-space graph of deltas such that <a1' \cup d1, ..., an' \cup dn ||- c1',...,cn'>
    is a refinement of <a1,...,an ||- c1,...,cn>. Importantly, this means that 
    <a1',...,an' ||- d1,...,dn> is an application of <a1,...,an ||- c1,...,cn> to
    <a1',...,an' ||- c1',...,cn'>.
  *)
  val findDeltasForBackwardApp : Type.typeSystem -> (int -> bool) -> sequent -> sequent -> (map * mgraph) Seq.seq

  val applyBackwardFree : Type.typeSystem -> sequent -> sequent -> sequent Seq.seq
  val applyBackwardRestricted : Type.typeSystem -> sequent -> sequent -> sequent Seq.seq
  val applyBackwardTargetting : Type.typeSystem -> (int -> bool) -> sequent -> sequent -> sequent Seq.seq

  (* 
    findDeltasForForwardApp takes a pair of sequents <a1,...,an ||- c1,...,cn> and 
    <a1',...,an' ||- c1',...,cn'> and finds refinement maps of <a1,...,an ||- c1,...,cn>. 
    For each refinement map, r, it returns a pair (r,(d1,...,dn)) where (d1,...,dn) is a
    multi-space graph of deltas such that <a1',...,an' ||- d1,...,dn> is a refinement of
    <a1,...,an ||- c1,...,cn>. Importantly, this means that 
    <a1' \cup d1, ..., an' \cup dn ||- c1',...,cn'> is an application of 
    <a1,...,an ||- c1,...,cn> to <a1',...,an' ||- c1',...,cn'>.
  
  val findDeltasForForwardApp : Type.typeSystem -> sequent -> sequent -> (map * mgraph) Seq.seq

  val applyForward : Type.typeSystem -> sequent -> sequent -> sequent Seq.seq
*)
  type state = {sequent : sequent, discharged : mgraph}
  val applyBackwardToState : Type.typeSystem -> (int -> bool) -> sequent -> state -> state Seq.seq
end


structure Sequent : SEQUENT =
struct
  type mgraph = MGraph.mgraph
  type map = MGraph.map
  type sequent = mgraph * mgraph

  fun chooseMinType T f t = 
    valOf (Type.min (#subType T) (CSpace.typeOfToken t, CSpace.typeOfToken (valOf (Graph.applyInvMap f t))))

  fun specialiseTypeOfToken T f t = CSpace.makeToken (CSpace.nameOfToken t) (chooseMinType T f t)

  (* 
    The assumption for findDeltasForBackwardApp is that (A,C) is a schema and (A',C') is a sequent.
    It aims to find a d such that (A,C) can be refined into (A' \cup d, C'). 
    The first thing is to check that C can be embedded in C'.
    If so, then we proceed to find d such that A can be reified into A' \cup d.
    There are infinitely many, so we restrict it to find 'minimal' ones.
    The idea is: for each subgraph, sA, of A, find a reification of sA into A'.
    Then take the complement of sA in A and create a copy, d, disjoint from A', of it so that A reifies into A' cup d.
    I is a list of integers that indicates the dimensions on which we DO NOT want non-trivial deltas, i.e., where (#i sA) = (#i A)
  *)
  fun findDeltasForBackwardApp T I (A,C) (A',C') =
    let
      val consequentMaps = MGraph.findEmbeddingsUpTo T (MGraph.tokensOfGraphQuick A,[]) (fn _ => NONE,fn _ => NONE) C C'
      fun findDeltasPerConsequentMap f = 
        let 
          val consequentEmbedding = MGraph.image f C
          val consequentDelta' = MGraph.remove consequentEmbedding C'
          val tokensThatMayBeSpecialisedInConsequentDelta = 
            List.filter (fn t => not (MGraph.tokenInGraphQuick t A')) (MGraph.tokensOfGraphQuick consequentDelta')
          val sequentUpdateMap = 
            List.foldl (fn (t,f') => Graph.updatePair (t,specialiseTypeOfToken T f t) f') (fn t => SOME t, fn t => SOME t) tokensThatMayBeSpecialisedInConsequentDelta
          val consequentDelta = MGraph.image sequentUpdateMap consequentDelta'
          val newF =
            (fn t => case Graph.applyMap f t of 
                        SOME t' => (case Graph.applyMap sequentUpdateMap t' of SOME t'' => SOME t'' | NONE => SOME t')
                      | NONE => NONE,
             fn t => case Graph.applyInvMap f t of 
                        SOME t' => (case Graph.applyInvMap sequentUpdateMap t' of SOME t'' => SOME t'' | NONE => SOME t')
                      | NONE => NONE)
            
          fun findPerSubgraph sA = 
            let 
              fun findPerReificationOfsA f' = 
                let 
                  val tokenNamesToAvoid = List.map CSpace.nameOfToken (MGraph.tokensOfGraphQuick A' @ MGraph.tokensOfGraphQuick C')
                  val complementOfsA = MGraph.remove sA A
                  val extendedMap = #1 (MGraph.extendMap f' (MGraph.tokensOfGraphQuick complementOfsA) tokenNamesToAvoid) (* extend domain of f' : sA -> A' from sA to A avoiding clashing with A' union C' *)
                  val antecedentDelta = MGraph.image extendedMap complementOfsA
                in 
                  (extendedMap, MGraph.join consequentDelta antecedentDelta)
                end
            in 
              Seq.map findPerReificationOfsA (MGraph.findReifications T newF sA A')
            end
        in 
          Seq.maps findPerSubgraph (MGraph.subgraphsRestricted I A)
        end
    in
      Seq.maps findDeltasPerConsequentMap consequentMaps 
    end

  fun applyBackwardFree T (A,C) (A',C') = Seq.map (fn x => (A', #2 x)) (findDeltasForBackwardApp T (fn _ => false) (A,C) (A',C'))

  fun applyBackwardRestricted T (A,C) (A',C') = Seq.map (fn x => (A', #2 x)) (findDeltasForBackwardApp T (fn i => i < length C') (A,C) (A',C'))

  fun applyBackwardTargetting T I (A,C) (A',C') = Seq.map (fn x => (A', #2 x)) (findDeltasForBackwardApp T I (A,C) (A',C'))

  type state = {sequent : sequent, discharged : mgraph}

  fun applyBackwardToState T I (A,C) st =
    let
      val (A',C') = #sequent st
      val deltas = findDeltasForBackwardApp T I (A,C) (A',C')
      fun makeResult (f,D) = 
        let
          val newDischarged = MGraph.image f C
        in
          {sequent = (A',D), discharged = MGraph.join newDischarged (#discharged st)}
        end
    in
      Seq.map makeResult deltas
    end

end