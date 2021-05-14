import "correspondence"
import "composition"

signature KNOWLEDGE =
sig
  type base

  (* CSpace knowledge *)


  (* Relational knowledge *)
  val relationshipsOf : base -> Relation.relationship FiniteSet.set;
  val related : base -> Relation.T -> CSpace.token list -> CSpace.token list -> bool;
  val subRelation : base -> Relation.T -> Relation.T -> bool;

  (* Correspondence knowledge *)
  val correspondencesOf : base -> Correspondence.corr FiniteSet.set;

  (* Building a knowledge base *)
  val addCorrespondences : base -> Correspondence.corr list -> base;
  val addRelationships : base -> Relation.relationship list -> base;

  val make : Relation.relationship list -> Correspondence.corr list -> base;

end

structure Knowledge : KNOWLEDGE =
struct
  type base = {relationships : Relation.relationship FiniteSet.set,
               subRelation : Relation.T * Relation.T -> bool,
               correspondences : Correspondence.corr FiniteSet.set};

  (* Relational knowledge *)
  fun relationshipsOf KB = #relationships KB;
  fun subRelation KB R1 R2 = (#subRelation KB) (R1,R2);

  fun related KB R a b =
    let fun sat (X,Y,R') = allZip CSpace.sameTokens a X andalso allZip CSpace.sameTokens b Y andalso subRelation KB R' R
    in Relation.same R Relation.alwaysTrue orelse Option.isSome (FiniteSet.find sat (relationshipsOf KB))
    end;

  (* Correspondence knowledge *)
  fun correspondencesOf KB = #correspondences KB;

  (* Building a knowledge base *)
  fun addCorrespondences KB corrs =
    {relationships= #relationships KB,
      subRelation = #subRelation KB,
      correspondences = FiniteSet.union (#correspondences KB) (FiniteSet.ofList corrs)}

  fun addRelationships KB rels =
    {relationships= FiniteSet.union (#relationships KB) rels,
      subRelation = #subRelation KB,
      correspondences = #correspondences KB}

  (* for now, the subRelation function is simply reflexive *)
  fun make rels corrs =
    let fun subrel (R1,R2) = if Relation.same R1 R2 then true else false
    in {relationships= FiniteSet.ofList rels,
        subRelation = subrel,
        correspondences = FiniteSet.ofList corrs}
    end

end
