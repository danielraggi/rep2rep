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
              originalGoal : Pattern.pattern,
              goals : Pattern.pattern list,
              compositions : Composition.composition list,
              knowledge : Knowledge.base} -> T;
  val updatePatternComps : Composition.composition list -> T -> T
  val updateGoals : Pattern.construction list -> T -> T
  val updateTransferProof : TransferProof.tproof -> T -> T
  val replaceGoal : Pattern.construction -> Pattern.construction list -> T -> T
  val removeGoal : Pattern.construction -> T -> T
  val insertGoals : Pattern.pattern list -> T -> T
  val applyPartialMorphismToProof : (CSpace.token -> CSpace.token option) -> T -> T;

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

  fun updatePatternComps L st =
         {sourceConSpecData = #sourceConSpecData st,
          targetConSpecData = #targetConSpecData st,
          interConSpecData = #interConSpecData st,
          transferProof = #transferProof st,
          construction = #construction st,
          originalGoal = #originalGoal st,
          goals = #goals st,
          compositions = L,
          knowledge = #knowledge st}

  fun updateGoals gs st =
           {sourceConSpecData = #sourceConSpecData st,
            targetConSpecData = #targetConSpecData st,
            interConSpecData = #interConSpecData st,
            transferProof = #transferProof st,
            construction = #construction st,
            originalGoal = #originalGoal st,
            goals = gs,
            compositions = #compositions st,
            knowledge = #knowledge st}

  fun updateTransferProof tp st =
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

  fun replaceGoal g gs st =
    let fun r [] = []
          | r (x::xs) = if Construction.same x g
                        then gs @ r xs
                        else x :: r xs
        (*fun r [] = []
          | r (x::xs) = if Construction.subConstruction x g
                        then Construction.minus x g @ gs @ r xs
                        else x :: r xs*)
        val newGoals = r (#goals st)
    in updateGoals newGoals st
    end

  fun removeGoal g st = replaceGoal g [] st
  fun insertGoals gs st = updateGoals (gs @ #goals st) st

  fun applyPartialMorphismToProof f st =
    {sourceConSpecData = #sourceConSpecData st,
     targetConSpecData = #targetConSpecData st,
     interConSpecData = #interConSpecData st,
     transferProof = TransferProof.applyPartialMorphism f (#transferProof st) ,
     construction = #construction st,
     originalGoal = Pattern.applyPartialMorphism f (#originalGoal st),
     goals = map (Pattern.applyPartialMorphism f) (#goals st),
     compositions = #compositions st,
     knowledge = #knowledge st}

  fun tokensInUse {construction,goals,compositions,...} =
    FiniteSet.union
      (foldl (fn (x,y) => FiniteSet.union (Pattern.tokensOfConstruction x) y) FiniteSet.empty goals)
      (FiniteSet.union (Construction.tokensOfConstruction construction)
                       (Composition.tokensOfCompositions compositions))
end;
