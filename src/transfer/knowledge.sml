import "core.correspondence";
import "core.composition";

signature KNOWLEDGE =
sig
  type base

  (* CSpace knowledge *)


  (* Relational knowledge *)
(*)  val relationshipsOf : base -> Relation.relationship FiniteSet.set;*)
  (*val related : base -> Relation.T -> CSpace.token list -> CSpace.token list -> bool;*)
  val subRelation : base -> Relation.T -> Relation.T -> bool;

  (* Correspondence knowledge *)
  val correspondencesOf : base -> Correspondence.corr Seq.seq;

  (* Building a knowledge base *)
  val addCorrespondence : base -> Correspondence.corr -> base;
  val addCorrespondences : base -> Correspondence.corr Seq.seq -> base;
  (*val addRelationships : base -> Relation.relationship list -> base;*)
  val findCorrespondenceWithName : base -> string -> Correspondence.corr option;

  val make : (*Relation.relationship list ->*) Correspondence.corr Seq.seq -> base;
  val join : base -> base -> base;
  val empty : base;
end;

structure Knowledge : KNOWLEDGE =
struct
  type base = {(*relationships : Relation.relationship FiniteSet.set,*)
               subRelation : Relation.T * Relation.T -> bool,
               correspondences : Correspondence.corr Seq.seq};

  (* Relational knowledge *)
  (*fun relationshipsOf KB = #relationships KB;*)
  fun subRelation KB R1 R2 = (#subRelation KB) (R1,R2);
(*)
  fun related KB R a b =
    let fun sat (X,Y,R') = List.allZip CSpace.sameTokens a X andalso List.allZip CSpace.sameTokens b Y andalso subRelation KB R' R
    in Relation.same R Relation.alwaysTrue orelse Option.isSome (FiniteSet.find sat (relationshipsOf KB))
    end;*)

  (* Correspondence knowledge *)
  fun correspondencesOf KB = #correspondences KB;

  fun addCorrespondence KB corr =
    {(*relationships= #relationships KB,*)
      subRelation = #subRelation KB,
      correspondences = Seq.cons corr (#correspondences KB)}

  (* Building a knowledge base *)
  fun addCorrespondences KB corrs =
    {(*relationships= #relationships KB,*)
      subRelation = #subRelation KB,
      correspondences = Seq.append (#correspondences KB) corrs}
(*)
  fun addRelationships KB rels =
    {relationships= FiniteSet.union (#relationships KB) rels,
      subRelation = #subRelation KB,
      correspondences = #correspondences KB}*)

  fun findCorrespondenceWithName KB name =
    Seq.findFirst (fn x => Correspondence.nameOf x = name) (#correspondences KB)

  (* for now, the subRelation function is simply reflexive *)
  fun make corrs =
    let fun subrel (R1,R2) = Relation.same R1 R2
    in {(*relationships= FiniteSet.ofList rels,*)
        subRelation = subrel,
        correspondences = corrs}
    end


  fun subRelUnion subR1 subR2 (x,y) = subR1(x,y) orelse subR2(x,y)
  (*)  if (subR1(x,y) orelse subR2(x,y)) = (subR1(y,x) orelse subR2(y,x))
    then raise incompatibleSubRelationFuns
    else subR1(x,y) orelse subR2(x,y)*)

  fun join k1 k2 =
    {subRelation = subRelUnion (#subRelation k1) (#subRelation k2),
     correspondences = Seq.append (#correspondences k1) (#correspondences k2)}

  val empty = make (Seq.empty)
end;
