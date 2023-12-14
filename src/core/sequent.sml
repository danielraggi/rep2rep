import "core.graph";

signature SEQUENT =
sig
  type mgraph
  type map
  type sequent = mgraph * mgraph

  (* 
    refineForBackwardApp takes a pair of sequents <a1,...,an ||- c1,...,cn> and 
    <a1',...,an' ||- c1',...,cn'> and finds refinement maps of <a1,...,an ||- c1,...,cn>. 
    For each refinement map, r, it returns a pair (r,(d1,...,dn)) where (d1,...,dn) is a
    multi-space graph of deltas such that <a1' \cup d1, ..., an' \cup dn ||- c1',...,cn'>
    is a refinement of <a1,...,an ||- c1,...,cn>. Importantly, this means that 
    <a1',...,an' ||- d1,...,dn> is an application of <a1,...,an ||- c1,...,cn> to
    <a1',...,an' ||- c1',...,cn'>.
  *)
  val refineForBackwardApp : Type.typeSystem -> sequent -> sequent -> (map * mgraph) Seq.seq

  val applyBackward : Type.typeSystem -> sequent -> sequent -> sequent Seq.seq

  (* 
    refineForForwardApp takes a pair of sequents <a1,...,an ||- c1,...,cn> and 
    <a1',...,an' ||- c1',...,cn'> and finds refinement maps of <a1,...,an ||- c1,...,cn>. 
    For each refinement map, r, it returns a pair (r,(d1,...,dn)) where (d1,...,dn) is a
    multi-space graph of deltas such that <a1',...,an' ||- d1,...,dn> is a refinement of
    <a1,...,an ||- c1,...,cn>. Importantly, this means that 
    <a1' \cup d1, ..., an' \cup dn ||- c1',...,cn'> is an application of 
    <a1,...,an ||- c1,...,cn> to <a1',...,an' ||- c1',...,cn'>.
  
  val refineForForwardApp : Type.typeSystem -> sequent -> sequent -> (map * mgraph) Seq.seq

  val applyForward : Type.typeSystem -> sequent -> sequent -> sequent Seq.seq
*)
end


structure Sequent : SEQUENT =
struct
  type mgraph = MGraph.mgraph
  type map = MGraph.map
  type sequent = mgraph * mgraph


  (* 
    findDeltasForReification finds values d such that g can be reified into g' \cup d.
    There are infinitely many, so here we only find minimal ones.
    The idea is: for every subgraph, s, of g, find a reification of s into g'.
    Then take the complement of s in g and create a copy, d, of it so that g reifies into g' cup d. 
  *)
  fun refineForBackwardApp T (A,C) (A',C') =
    let
      val consequentMaps = MGraph.findEmbeddingsUpTo T (MGraph.tokensOfGraph A,[]) (fn _ => NONE,fn _ => NONE) C C'
      fun findDeltasForReification f = 
        let 
          val consequentEmbedding = MGraph.image f C
          val consequentDelta = MGraph.remove consequentEmbedding C'
          fun findPerSubgraph sA = 
            let fun mapWithDelta f' = 
                  let 
                    val tokenIDS = List.map CSpace.nameOfToken (MGraph.tokensOfGraph A' @ MGraph.tokensOfGraph C')
                    val extendedMap = #1 (MGraph.extendMap f' A tokenIDS) (* extend domain of f' : sA -> A' from sA to A avoiding clashing with A' union C' *)
                    val antecedentDelta = MGraph.image extendedMap (MGraph.remove sA A) 
                  in (f', MGraph.join consequentDelta antecedentDelta)
                  end
            in Seq.map mapWithDelta (MGraph.findReifications T f sA A')
            end
        in 
          Seq.maps findPerSubgraph (MGraph.subgraphs A)
        end
    in
      Seq.maps findDeltasForReification consequentMaps 
    end

  fun applyBackward T (A,C) (A',C') = Seq.map (fn x => (A', #2 x)) (refineForBackwardApp T (A,C) (A',C'))

    
end