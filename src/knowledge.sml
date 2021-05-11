import "correspondence"

signature KNOWLEDGE =
sig
  type base

  (* CSpace knowledge *)


  (* Relational knowledge *)
  val relationsOf : base -> Relation.relationship Set.T;
  val related : base -> Relation.T -> 'a -> 'b -> bool;
  val subRelation : base -> Relation.T -> Relation.T -> bool;

  (* Correspondence knowledge *)
  val correspondencesOf : base -> Correspondence.corr Set.T;

  (* Building a knowledge base *)
  val addCorrespondences : base -> Correspondence.corr list -> base;
  val addRelationships : base -> Relation.relationship list -> base;

  val make : Relation.relationship list -> Correspondence.corr list -> CSpace.T -> base;

end

structure Knowledge : KNOWLEDGE =
struct
  type base = {relationships : Relation.relationship Set.T,
               subRelation : Relation.T * Relation.T -> bool,
               correspondences : Correspondence.corr Set.T,
               cspace : CSpace.T};

  (* CSpace knowledge *)
  (* nothing for now*)

  (* Relational knowledge *)
  fun relationshipsOf KB = #relationships KB;
  fun subRelation KB R1 R2 = (#subRelation KB) (R1,R2);

  fun related KB R a b =
  let val alwaysTrue = Relation.alwaysTrue (Relation.leftTypeOf R) (Relation.rightTypeOf R)
      fun sat (x,y,R') = SGraph.sameV x a andalso SGraph.sameV y b andalso subRelation KB (R', R)
  in Relation.same R alwaysTrue orelse Option.isSome (Set.find sat (relationshipsOf KB))
  end;

  (* Correspondence knowledge *)
  fun correspondencesOf KB = #correspondences KB;

  (* Building a knowledge base *)
  fun addCorrespondences KB corrs =
    {relationships= #relationships KB,
      subRelation = #subRelation KB,
      correspondences = List.foldl Set.insert (#correspondences KB) corrs,
      cspace = #cspace KB}

  fun addRelationships KB rels =
    {relationships= List.foldl Set.insert (#relationships KB) rels,
      subRelation = #subRelation KB,
      correspondences = #correspondences KB,
      cspace = #cspace KB}

  (* for now, the subRelation function is simply reflexive *)
  fun make rels corrs cs =
  let fun subrel (R1,R2) = if Relation.same (R1,R2) then true else false
  in {relationships= Set.fromList rels,
      subRelation = subrel,
      correspondences = Set.fromList corrs,
      cspace = cs}
  end

end
