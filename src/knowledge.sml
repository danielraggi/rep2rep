import "correspondence"

signature KNOWLEDGE =
sig
  type base = CSpace.T * Correspondence.set * Relation.set
  val make : CSpace.T -> Correspondence.set -> Relation.set -> base
end

structure Knowledge : KNOWLEDGE =
struct
  type base
  fun make cspace corrs rels = (cspace,corrs,rels)
end
