import "pattern"
import "relation"

signature CORRESPONDENCE =
sig
  type corr = Pattern.T * Pattern.T * Relation.T * Relation.T
  type composition
  type set
  val rightMatching : corr -> SGraph.T -> SGraph.vertex -> SGraph.T set
  val leftMatching : corr -> SGraph.T -> SGraph.vertex -> SGraph.T set
end

structure Correspondence : CORRESPONDENCE =
struct
  type corr
  type composition
  type set
  fun rightmatching
  fun leftmatching
end
