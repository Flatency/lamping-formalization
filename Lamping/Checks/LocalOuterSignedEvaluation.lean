import Lamping.Lamping.LocalOuterSignedEvaluation
import Lamping.Checks.UniformOldOuterImageAlignment

namespace Lamping.Checks.LocalOuterSignedEvaluationChecks
open Lambda Lambda.Labelled AG
open SingleUnsafeCopyFunctionAppInputsChecks
open ExpandedArgumentHistoryOriginsChecks.CrossPrefix
open UniformOldOuterImageAlignmentChecks.CrossPrefix

/-- A real earlier OLD prefix from a noninitial SOURCE, using the complete
SOURCE atom images. The output is lexical, not physical-path reflection. -/
theorem actual_early_cross_prefix_signed_evaluation :
    INIT original ∧History [[.arg,.fn,.body],[]] original source ∧
      earlyLocal.label.sourceWord
        (fun n=>(initialRelabelling source 0 n).edgeWord)
        (Label.atom 6).edgeWord (EdgeWord.reverse (Label.atom 6).edgeWord)=
        copiedArgument.label.edgeWord := by
  obtain ⟨node,atGlobal,equation⟩ :=
    event.beforeOld.local_outer_signed_evaluation preHistory localBefore selected
      (by rfl : localMiddle.subterm earlyHead=some earlyLocal)
  have nodeEq : node=copiedArgument :=
    Option.some.inj (atGlobal.symm.trans (by rfl : middle.subterm earlyHead=some copiedArgument))
  exact ⟨initial,prefixHistory,by rw [nodeEq] at equation;exact equation⟩

/-- The later actual prefix uses the SAME SOURCE basis, another actual
lookup, and its own paired schedule. No local coordinate injection is used. -/
theorem actual_late_cross_prefix_signed_evaluation :
    INIT original ∧History [[.arg,.fn,.body],[]] original source ∧
      lateLocal.label.sourceWord
        (fun n=>(initialRelabelling source 0 n).edgeWord)
        (Label.atom 6).edgeWord (EdgeWord.reverse (Label.atom 6).edgeWord)=
        copiedArgument.label.edgeWord := by
  obtain ⟨node,atGlobal,equation⟩ :=
    event.final_old.local_outer_signed_evaluation event.final_history localFull selected
      (by rfl : localTarget.subterm leftHead=some lateLocal)
  have nodeEq : node=copiedArgument := Option.some.inj (atGlobal.symm.trans leftLookup)
  exact ⟨initial,prefixHistory,by rw [nodeEq] at equation;exact equation⟩

#print axioms actual_early_cross_prefix_signed_evaluation
#print axioms actual_late_cross_prefix_signed_evaluation
end Lamping.Checks.LocalOuterSignedEvaluationChecks
