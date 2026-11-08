import Lamping.Lamping.FanBodyVariableAuxiliary
import Lamping.Checks.FanCopiedBodyBinding
set_option maxHeartbeats 4000000
namespace Lamping.Checks.FanBodyVariableAuxiliaryConsumer
open AG Graph Lambda Lambda.Labelled
open FanBodyBindingIdentityReachable FanCopiedBodyBindingChecks
/-- Literal CURRENT syntax domain; no physical profile or wanted finish. -/
theorem actual_body_syntax : ∃parent stamp,bodyPosition.val=parent++[.body] ∧
    current.subterm parent=some (.lam stamp (.var functionBody.label 0)) :=
  ⟨[.fn],functionTerm.label,rfl,rfl⟩
/-- Direct NEW natural top on the actual identity two-event carrier.
SOURCEJoint remains an honest condition; both endpoint isos are real selfpairs. -/
theorem direct_natural_endpoint
    (source : OccurrenceFragmentSelection current sourceNet (.inl ()))
    (target : OccurrenceFragmentSelection current targetNet (.inl ()))
    (sourceJoint : JointRepresentation currentClosed source) :
    (target bodyPosition).fragment.segments=(target bodyPosition).fragment.segments := by
  obtain ⟨principal⟩ := outerFan.site.actionPrincipal_exists
  obtain ⟨_inputs,oldT⟩ := source_inputs_transparency
  exact outerFan.site.fan_body_variable_endpoint_equality actual_source_matches actual_target_matches
    sourceFlow rfl oldT principal currentClosed source target sourceJoint bodyPosition bodyPosition
    (show current.subterm bodyPosition.val=some (.var functionBody.label 0) from rfl)
    (show current.subterm bodyPosition.val=some (.var functionBody.label 0) from rfl)
    actual_body_syntax actual_body_syntax rfl actual_successful_endpoints.2.2.1 actual_successful_endpoints.2.2.2
/-- Direct restricted D017 top: difference is hypothetical, never claimed
inhabited for the real same-occurrence positive example. -/
theorem direct_restricted_auxiliary
    (source : OccurrenceFragmentSelection current sourceNet (.inl ()))
    (target : OccurrenceFragmentSelection current targetNet (.inl ()))
    (sourceJoint : JointRepresentation currentClosed source)
    (different : (target bodyPosition).fragment.segments≠(target bodyPosition).fragment.segments) :
    ¬(SuccessfulEndpointIso current currentClosed (SyntaxIncidence.source current bodyPosition)
        (SyntaxIncidence.source current bodyPosition) ∧
      SuccessfulEndpointIso current currentClosed (SyntaxIncidence.target current currentClosed bodyPosition)
        (SyntaxIncidence.target current currentClosed bodyPosition)) := by
  obtain ⟨principal⟩ := outerFan.site.actionPrincipal_exists
  obtain ⟨_inputs,oldT⟩ := source_inputs_transparency
  exact outerFan.site.fan_body_variable_auxiliary_separation actual_source_matches actual_target_matches
    sourceFlow rfl oldT principal currentClosed source target sourceJoint bodyPosition bodyPosition
    (show current.subterm bodyPosition.val=some (.var functionBody.label 0) from rfl)
    (show current.subterm bodyPosition.val=some (.var functionBody.label 0) from rfl)
    actual_body_syntax actual_body_syntax rfl different
/-- Four independent legal choices: each natural call uses ONE consistent
source/target selection; cross-choice equality and IH transport are explicit. -/
theorem direct_four_choices
    (sourceFirst sourceSecond : OccurrenceFragmentSelection current sourceNet (.inl ()))
    (targetFirst targetSecond : OccurrenceFragmentSelection current targetNet (.inl ()))
    (sourceJoint : JointRepresentation currentClosed sourceFirst) :
    (targetFirst bodyPosition).fragment.segments=(targetSecond bodyPosition).fragment.segments := by
  have first := direct_natural_endpoint sourceFirst targetFirst sourceJoint
  have secondJoint : JointRepresentation currentClosed sourceSecond :=
    (JointRepresentation.choice_independent actual_source_matches currentClosed sourceFirst sourceSecond).mp sourceJoint
  have second := direct_natural_endpoint sourceSecond targetSecond secondJoint
  have choices := (targetFirst bodyPosition).segments_unique actual_target_matches (targetSecond bodyPosition)
  exact first.trans (choices.trans second)
#print axioms actual_body_syntax
#print axioms direct_natural_endpoint
#print axioms direct_restricted_auxiliary
#print axioms direct_four_choices
#print axioms FanCopiedBodyBindingChecks.source_inputs_transparency
#print axioms FanCopiedBodyBindingChecks.actual_original_history_trace
#print axioms FanCopiedBodyBindingChecks.actual_successful_endpoints
#print axioms FanCopiedBodyBindingChecks.actual_nonempty_four_choices
#print axioms FanCopiedBodyBindingChecks.actual_binding_finish
#print axioms FanBodyBindingIdentityReachable.lambdaFinish
#print axioms FanCopiedBodyBindingChecks.actual_direct_cut
#print axioms FanBodyBindingIdentityReachable.actualHistory
end Lamping.Checks.FanBodyVariableAuxiliaryConsumer