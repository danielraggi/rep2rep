import "knowledge"

signature STATE =
sig
  type T;
  val typeSystemOf : T -> TypeSystem.typeSystem;
  val constructionOf : T -> Construction.construction;
  val goalsOf : T -> Relation.relationship list;
  val patternCompOf : T -> Composition.composition;
  val knowledgeOf : T -> Knowledge.base;
  val make : {typeSystem : TypeSystem.typeSystem,
              construction : Construction.construction,
              goals : Relation.relationship list,
              composition : Composition.composition,
              knowledge : Knowledge.base} -> T;
  val updatePatternComp : T -> Composition.composition -> T
  val updateGoals : T -> Relation.relationship list -> T
  val replaceGoal : T -> Relation.relationship -> Relation.relationship list -> T
  val removeGoal : T -> Relation.relationship -> T

end

structure State : STATE =
struct
  type T = {typeSystem : TypeSystem.typeSystem,
            construction : Construction.construction,
            goals : Relation.relationship list,
            composition : Composition.composition,
            knowledge : Knowledge.base};

  fun typeSystemOf {typeSystem,...} = typeSystem;
  fun constructionOf {construction,...} = construction;
  fun goalsOf {goals,...} = goals;
  fun patternCompOf {composition,...} = composition;
  fun knowledgeOf {knowledge,...} = knowledge;

  fun make st = st

  fun updatePatternComp st d =
           {typeSystem = #typeSystem st,
            construction = #construction st,
            goals = #goals st,
            composition = d,
            knowledge = #knowledge st}

  fun updateGoals st gs =
           {typeSystem = #typeSystem st,
            construction = #construction st,
            goals = gs,
            composition = #composition st,
            knowledge = #knowledge st}

  fun replaceGoal st g gs =
    let fun r [] = [] | r (x::xs) = if Relation.sameRelationship x g then gs @ r xs else x :: r xs
        val newGoals = r (#goals st)
    in updateGoals st newGoals
    end

  fun removeGoal st g =
    let fun r [] = [] | r (x::xs) = if Relation.sameRelationship x g then r xs else x :: r xs
        val newGoals = r (#goals st)
    in updateGoals st newGoals
    end

end
