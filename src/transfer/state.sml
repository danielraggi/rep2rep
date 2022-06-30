import "transfer.knowledge";
import "transfer.transfer_proof";

signature STATE =
sig
  type T;
  val sourceTypeSystemOf : T -> Type.typeSystemData;
  val sourceConSpecDataOf : T -> CSpace.conSpecData;
  val targetTypeSystemOf : T -> Type.typeSystemData;
  val targetConSpecDataOf : T -> CSpace.conSpecData;
  val interTypeSystemOf : T -> Type.typeSystemData;
  val interConSpecDataOf : T -> CSpace.conSpecData;

  val constructionOf : T -> Construction.construction;
  val originalGoalOf : T -> Pattern.construction;
  val goalsOf : T -> Pattern.construction list;
  val patternCompsOf : T -> Composition.composition list;
  val knowledgeOf : T -> Knowledge.base;
  val transferProofOf : T -> TransferProof.tproof;
  val make : {sourceConSpecData : CSpace.conSpecData,
              targetConSpecData : CSpace.conSpecData,
              interConSpecData : CSpace.conSpecData,
              transferProof : TransferProof.tproof,
              construction : Construction.construction,
              originalGoal : Pattern.construction,
              goals : Pattern.construction list,
              compositions : Composition.composition list,
              knowledge : Knowledge.base} -> T;
  val updatePatternComps : T -> Composition.composition list -> T
  val updateGoals : T -> Pattern.construction list -> T
  val updateTransferProof : T -> TransferProof.tproof -> T
  val replaceGoal : T -> Pattern.construction -> Pattern.construction list -> T
  val removeGoal : T -> Pattern.construction -> T
  val applyPartialMorphismToCompAndGoals : (CSpace.token -> CSpace.token option) -> T -> T;

  val tokensInUse : T -> CSpace.token FiniteSet.set
end;

structure State : STATE =
struct
  type T = {sourceConSpecData : CSpace.conSpecData,
            targetConSpecData : CSpace.conSpecData,
            interConSpecData : CSpace.conSpecData,
            transferProof : TransferProof.tproof,
            construction : Construction.construction,
            originalGoal : Pattern.construction,
            goals : Pattern.construction list,
            compositions : Composition.composition list,
            knowledge : Knowledge.base};

  fun sourceTypeSystemOf {sourceConSpecData,...} = #typeSystemData sourceConSpecData;
  fun sourceConSpecDataOf {sourceConSpecData,...} = sourceConSpecData;

  fun targetTypeSystemOf {targetConSpecData,...} = #typeSystemData targetConSpecData;
  fun targetConSpecDataOf {targetConSpecData,...} = targetConSpecData;

  fun interTypeSystemOf {interConSpecData,...} = #typeSystemData interConSpecData;
  fun interConSpecDataOf {interConSpecData,...} = interConSpecData;

  fun constructionOf {construction,...} = construction;
  fun originalGoalOf {originalGoal,...} = originalGoal;
  fun goalsOf {goals,...} = goals;
  fun patternCompsOf {compositions,...} = compositions;
  fun knowledgeOf {knowledge,...} = knowledge;
  fun transferProofOf {transferProof,...} = transferProof;

  fun make st = st

  fun updatePatternComps st L =
         {sourceConSpecData = #sourceConSpecData st,
          targetConSpecData = #targetConSpecData st,
          interConSpecData = #interConSpecData st,
          transferProof = #transferProof st,
          construction = #construction st,
          originalGoal = #originalGoal st,
          goals = #goals st,
          compositions = L,
          knowledge = #knowledge st}

  fun updateGoals st gs =
           {sourceConSpecData = #sourceConSpecData st,
            targetConSpecData = #targetConSpecData st,
            interConSpecData = #interConSpecData st,
            transferProof = #transferProof st,
            construction = #construction st,
            originalGoal = #originalGoal st,
            goals = gs,
            compositions = #compositions st,
            knowledge = #knowledge st}

  fun updateTransferProof st tp =
           {sourceConSpecData = #sourceConSpecData st,
            targetConSpecData = #targetConSpecData st,
            interConSpecData = #interConSpecData st,
            transferProof = tp,
            construction = #construction st,
            originalGoal = #originalGoal st,
            goals = #goals st,
            compositions = #compositions st,
            knowledge = #knowledge st}

(*)
  fun replaceGoal st g gs =
    let fun r [] = []
          | r (x::xs) = if Relation.sameRelationship x g
                        then gs @ r xs
                        else x :: r xs
        val newGoals = r (#goals st)
    in updateGoals st newGoals
    end*)

  fun replaceGoal st g gs =
    let fun r [] = []
          | r (x::xs) = if Construction.subConstruction x g
                        then Construction.minus x g @ gs @ r xs
                        else x :: r xs
        val newGoals = r (#goals st)
    in updateGoals st newGoals
    end

  fun removeGoal st g = replaceGoal st g []

  fun applyPartialMorphismToCompAndGoals f st =
    let fun applyPartialF t = (case f t of SOME t' => t' | NONE => t)
        fun applyToRelationship (ss,ts,R) = (map applyPartialF ss, map applyPartialF ts, R)
    in {sourceConSpecData = #sourceConSpecData st,
        targetConSpecData = #targetConSpecData st,
        interConSpecData = #interConSpecData st,
        transferProof = TransferProof.applyPartialMorphism f (#transferProof st),
        construction = #construction st,
        originalGoal = Pattern.applyPartialMorphism f (#originalGoal st),
        goals = map (Pattern.applyPartialMorphism f) (#goals st),
        compositions = map (Composition.applyPartialMorphismToComposition f) (#compositions st),
        knowledge = #knowledge st}
    end

  fun tokensInUse {construction,goals,compositions,...} =
    FiniteSet.union
      (foldl (fn (x,y) => FiniteSet.union (Pattern.tokensOfConstruction x) y) FiniteSet.empty goals)
      (FiniteSet.union (Construction.tokensOfConstruction construction)
                       (Composition.tokensOfCompositions compositions))
end;
