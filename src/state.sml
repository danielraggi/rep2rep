import "knowledge";

signature STATE =
sig
  type T;
  val sourceTypeSystemOf : T -> Type.typeSystem;
  val targetTypeSystemOf : T -> Type.typeSystem;
  val constructionOf : T -> Construction.construction;
  val originalGoalOf : T -> Relation.relationship;
  val goalsOf : T -> Relation.relationship list;
  val patternCompOf : T -> Composition.composition;
  val knowledgeOf : T -> Knowledge.base;
  val make : {sourceTypeSystem : Type.typeSystem,
              targetTypeSystem : Type.typeSystem,
              construction : Construction.construction,
              originalGoal : Relation.relationship,
              goals : Relation.relationship list,
              composition : Composition.composition,
              knowledge : Knowledge.base} -> T;
  val updatePatternComp : T -> Composition.composition -> T
  val updateGoals : T -> Relation.relationship list -> T
  val replaceGoal : T -> Relation.relationship -> Relation.relationship list -> T
  val removeGoal : T -> Relation.relationship -> T
  val applyPartialMorphismToCompAndGoals : (CSpace.token -> CSpace.token option) -> T -> T;

end;

structure State : STATE =
struct
  type T = {sourceTypeSystem : Type.typeSystem,
            targetTypeSystem : Type.typeSystem,
            construction : Construction.construction,
            originalGoal : Relation.relationship,
            goals : Relation.relationship list,
            composition : Composition.composition,
            knowledge : Knowledge.base};

  fun sourceTypeSystemOf {sourceTypeSystem,...} = sourceTypeSystem;
  fun targetTypeSystemOf {targetTypeSystem,...} = targetTypeSystem;
  fun constructionOf {construction,...} = construction;
  fun originalGoalOf {originalGoal,...} = originalGoal;
  fun goalsOf {goals,...} = goals;
  fun patternCompOf {composition,...} = composition;
  fun knowledgeOf {knowledge,...} = knowledge;

  fun make st = st

  fun updatePatternComp st d =
           {sourceTypeSystem = #sourceTypeSystem st,
            targetTypeSystem = #targetTypeSystem st,
            construction = #construction st,
            originalGoal = #originalGoal st,
            goals = #goals st,
            composition = d,
            knowledge = #knowledge st}

  fun updateGoals st gs =
           {sourceTypeSystem = #sourceTypeSystem st,
            targetTypeSystem = #targetTypeSystem st,
            construction = #construction st,
            originalGoal = #originalGoal st,
            goals = gs,
            composition = #composition st,
            knowledge = #knowledge st}

  fun replaceGoal st g gs =
    let fun r [] = []
          | r (x::xs) = if Relation.sameRelationship x g
                        then gs @ r xs
                        else x :: r xs
        val newGoals = r (#goals st)
    in updateGoals st newGoals
    end

  fun removeGoal st g = replaceGoal st g []

  fun applyPartialMorphismToCompAndGoals f st =
    let fun applyPartialF t = (case f t of SOME t' => t' | NONE => t)
        fun applyToRelationship (ss,ts,R) = (map applyPartialF ss, map applyPartialF ts, R)
    in {sourceTypeSystem = #sourceTypeSystem st,
        targetTypeSystem = #targetTypeSystem st,
        construction = #construction st,
        originalGoal = applyToRelationship (#originalGoal st),
        goals = map applyToRelationship (#goals st),
        composition = Composition.applyPartialMorphismToComposition f (#composition st),
        knowledge = #knowledge st}
    end

end;
