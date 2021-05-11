import "knowledge"

signature STATE =
sig
  type T;
  val constructionOf : T -> Construction.construction;
  val goalsOf : T -> Relation.relationship list;
  val patternDecompOf : T -> Decomposition.decomposition;
  val knowledgeOf : T -> Knowledge.base;
  val make : {typeSystem : Type.typeSystem,
              construction : Construction.construction,
              goals : Relation.relationship list,
              decomposition : Decomposition.decomposition,
              knowledge : Knowledge.base} -> T;
  val updatePatternDecomp : T -> Decomposition.decomposition -> T
  val updateGoals : T -> Relation.relationship list -> T
  val replaceGoal : T -> Relation.relationship -> Relation.relationship list -> T
  val removeGoal : T -> Relation.relationship -> T

end

structure State : STATE =
struct
  type T = {typeSystem : Type.typeSystem,
            construction : Construction.construction,
            goals : Relation.relationship list,
            decomposition : Decomposition.decomposition,
            knowledge : Knowledge.base};

  fun typeSystemOf {typeSystem,...} = typeSystem;
  fun constructionOf {construction,...} = construction;
  fun goalsOf {goals,...} = goals;
  fun patternDecompOf {decomposition,...} = decomposition;
  fun knowledgeOf {knowledge,...} = knowledge;

  fun make st = st

  fun updatePatternDecomp st d =
           {typeSystem = #typeSystem st,
            construction = #construction st,
            goals = #goals st,
            decomposition = d,
            knowledge = #knowledge st}

  fun updateGoals st gs =
           {typeSystem = #typeSystem st,
            construction = #construction st,
            goals = gs,
            decomposition = #decomposition st,
            knowledge = #knowledge st}

  fun replaceGoal st g gs =
    let fun r [] = [] | r (x::xs) => if Relation.sameRelationship x g then g @ r xs else x :: r xs
        val newGoals = r (#goals st)
    in updateGoals st newGoals
    end

  fun removeGoal st g =
    let fun r [] = [] | r (x::xs) => if Relation.sameRelationship x g then r xs else x :: r xs
        val newGoals = r (#goals st)
    in updateGoals st newGoals
    end

end
