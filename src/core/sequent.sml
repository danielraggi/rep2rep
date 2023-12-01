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
  val refineForBackwardApp : sequent -> sequent -> (map * mgraph) Seq.seq

  val applyBackward : sequent -> sequent -> sequent Seq.seq

  (* 
    refineForForwardApp takes a pair of sequents <a1,...,an ||- c1,...,cn> and 
    <a1',...,an' ||- c1',...,cn'> and finds refinement maps of <a1,...,an ||- c1,...,cn>. 
    For each refinement map, r, it returns a pair (r,(d1,...,dn)) where (d1,...,dn) is a
    multi-space graph of deltas such that <a1',...,an' ||- d1,...,dn> is a refinement of
    <a1,...,an ||- c1,...,cn>. Importantly, this means that 
    <a1' \cup d1, ..., an' \cup dn ||- c1',...,cn'> is an application of 
    <a1,...,an ||- c1,...,cn> to <a1',...,an' ||- c1',...,cn'>.
  *)
  val refineForForwardApp : sequent -> sequent -> (map * mgraph) Seq.seq

  val applyForward : sequent -> sequent -> sequent Seq.seq

end
