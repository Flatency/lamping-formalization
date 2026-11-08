import Lamping.Lamping.FanAppJointPreservation
import Lamping.Checks.FanAppAuxiliaryPreservation
set_option maxHeartbeats 4000000
namespace Lamping.Checks.FanAppJointPreservationConsumer
open AG Graph Lambda Lambda.Labelled
open FanAppAuxiliaryArgumentReachable
/-- Direct combined top on the accepted original five-event KC carrier.
SOURCEJoint is an explicit conditional IH, not an instance constructed here. -/
theorem direct_natural_joint
    (source : OccurrenceFragmentSelection Syntax.current fanApp.site.net (.inl ()))
    (target : OccurrenceFragmentSelection Syntax.current fanApp.site.reduce (.inl ()))
    (sourceJoint : JointRepresentation Syntax.targetClosed source) :
    JointRepresentation Syntax.targetClosed target := by
  obtain ⟨principal⟩ := fanApp.site.actionPrincipal_exists
  exact fanApp.site.fan_app_joint_representation_preserve actual_source_matches actual_target_matches
    (fanApp.sourceIso.flowBalance Domain.fourthFlow) rfl
    FanAppAuxiliaryPreservationConsumer.actual_source_inputs principal Syntax.targetClosed
    source target sourceJoint
/-- Both clauses come from the one actual combined invocation with SAME selections. -/
theorem direct_joint_clauses
    (source : OccurrenceFragmentSelection Syntax.current fanApp.site.net (.inl ()))
    (target : OccurrenceFragmentSelection Syntax.current fanApp.site.reduce (.inl ()))
    (sourceJoint : JointRepresentation Syntax.targetClosed source) :
    ChainRepresentationInvariant Syntax.targetClosed target ∧
      AuxiliarySeparation Syntax.targetClosed target :=
  direct_natural_joint source target sourceJoint
/-- The actual selector spaces are inhabited independently of the conditional IH. -/
theorem actual_nonempty_selections :
    Nonempty (OccurrenceFragmentSelection Syntax.current fanApp.site.net (.inl ())) ∧
    Nonempty (OccurrenceFragmentSelection Syntax.current fanApp.site.reduce (.inl ())) :=
  Domain.actual_selections_nonempty
#print axioms direct_natural_joint
#print axioms direct_joint_clauses
#print axioms actual_nonempty_selections
#print axioms FanAppAuxiliaryArgumentReachable.actual_five_step_trace
#print axioms FanAppAuxiliaryArgumentReachable.actual_source_matches
#print axioms FanAppAuxiliaryArgumentReachable.actual_target_matches
#print axioms Syntax.initial
#print axioms Syntax.actualHistory
#print axioms Syntax.two_actual_successful_endpoints
#print axioms Domain.actual_selected_argument_domain
#print axioms Domain.actual_argument_kept_copied_cut
end Lamping.Checks.FanAppJointPreservationConsumer