import Lamping.Lamping.FanLambdaAuxiliaryPreservation
import Lamping.Checks.FanCopiedBodyBinding
set_option maxHeartbeats 4000000
namespace Lamping.Checks.FanLambdaAuxiliaryPreservationConsumer
open AG Graph Lambda Lambda.Labelled
open FanBodyBindingIdentityReachable FanCopiedBodyBindingChecks

/-- Direct full natural Aux top on the genuine original INIT/root-beta/fanlambda
identity carrier. SOURCEJoint is an honest premise, not a claimed fixture fact. -/
theorem direct_actual_auxiliary
    (source : OccurrenceFragmentSelection current sourceNet (.inl ()))
    (target : OccurrenceFragmentSelection current targetNet (.inl ()))
    (sourceJoint : JointRepresentation currentClosed source) :
    AuxiliarySeparation currentClosed target := by
  obtain ⟨principal⟩ := outerFan.site.actionPrincipal_exists
  obtain ⟨_inputs,oldT⟩ := source_inputs_transparency
  exact outerFan.site.fan_lambda_auxiliary_separation_preserve actual_source_matches actual_target_matches
    sourceFlow rfl oldT principal currentClosed source target sourceJoint

/-- Direct NEW Joint preservation; it assumes SOURCEJoint and proves no
unconditional history invariant or different endpoint isomorphism. -/
theorem direct_actual_joint
    (source : OccurrenceFragmentSelection current sourceNet (.inl ()))
    (target : OccurrenceFragmentSelection current targetNet (.inl ()))
    (sourceJoint : JointRepresentation currentClosed source) :
    JointRepresentation currentClosed target := by
  obtain ⟨principal⟩ := outerFan.site.actionPrincipal_exists
  obtain ⟨_inputs,oldT⟩ := source_inputs_transparency
  exact outerFan.site.fan_lambda_joint_representation_preserve actual_source_matches actual_target_matches
    sourceFlow rfl oldT principal currentClosed source target sourceJoint

/-- Four arbitrary legal choices use ONE consistent pair per call. The
SOURCE IH and cross-target property comparison are transported explicitly. -/
theorem direct_four_choices
    (sourceFirst sourceSecond : OccurrenceFragmentSelection current sourceNet (.inl ()))
    (targetFirst targetSecond : OccurrenceFragmentSelection current targetNet (.inl ()))
    (sourceJoint : JointRepresentation currentClosed sourceFirst) :
    AuxiliarySeparation currentClosed targetFirst ∧JointRepresentation currentClosed targetFirst ∧
      AuxiliarySeparation currentClosed targetSecond ∧JointRepresentation currentClosed targetSecond ∧
      (JointRepresentation currentClosed targetFirst ↔JointRepresentation currentClosed targetSecond) := by
  have secondSource : JointRepresentation currentClosed sourceSecond :=
    (JointRepresentation.choice_independent actual_source_matches currentClosed sourceFirst sourceSecond).mp sourceJoint
  exact ⟨direct_actual_auxiliary sourceFirst targetFirst sourceJoint,
    direct_actual_joint sourceFirst targetFirst sourceJoint,
    direct_actual_auxiliary sourceSecond targetSecond secondSource,
    direct_actual_joint sourceSecond targetSecond secondSource,
    JointRepresentation.choice_independent actual_target_matches currentClosed targetFirst targetSecond⟩

#print axioms direct_actual_auxiliary
#print axioms direct_actual_joint
#print axioms direct_four_choices
#print axioms FanCopiedBodyBindingChecks.source_inputs_transparency
#print axioms FanCopiedBodyBindingChecks.actual_original_history_trace
#print axioms FanCopiedBodyBindingChecks.actual_successful_endpoints
#print axioms FanCopiedBodyBindingChecks.actual_nonempty_four_choices
#print axioms FanCopiedBodyBindingChecks.actual_binding_finish
#print axioms FanBodyBindingIdentityReachable.lambdaFinish
#print axioms FanCopiedBodyBindingChecks.actual_direct_cut
#print axioms FanBodyBindingIdentityReachable.actualHistory
end Lamping.Checks.FanLambdaAuxiliaryPreservationConsumer
