import Lamping.Lambda.TargetHistoryPreimages
import Lamping.Checks.HistoryEndpointAvailability
namespace Lamping.Checks.TargetHistoryPreimagesChecks
open Lambda Lambda.Labelled AG
open HistoryEndpointAvailabilityChecks

theorem actual_two_step_target :
    BetaVertexHistoryPreimage labels (some currentTo) (some oldTo) := by
  obtain ⟨vertex,spec,ancestry⟩ := trace.target_history toSpec
  have equal := SyntaxIncidence.Target.unique spec oldToSpec
  exact equal ▸ ancestry

theorem actual_unique_target {vertex : SyntaxIncidence.Vertex NodeLabelSuffixOriginsChecks.source}
    (other : BetaVertexHistoryPreimage labels (some currentTo) vertex) : vertex=some oldTo :=
  other.unique actual_two_step_target

theorem boundary_not_proper :
    ¬BetaVertexHistoryPreimage labels none (some oldTo) := by intro trace;cases trace

#print axioms BetaVertexHistoryPreimage.unique
#print axioms BetaNodeHistoryPreimage.target_history
#print axioms actual_two_step_target
#print axioms actual_unique_target
#print axioms boundary_not_proper
end Lamping.Checks.TargetHistoryPreimagesChecks
