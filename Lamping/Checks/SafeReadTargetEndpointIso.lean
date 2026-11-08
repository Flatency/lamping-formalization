import Lamping.Lamping.SafeReadTargetEndpointIso
import Lamping.Checks.AuxiliaryEndpointAvailability
namespace Lamping.Checks.SafeReadTargetEndpointIsoChecks
open Lambda Lambda.Labelled AG
open NodeLabelSuffixOriginsChecks AuxiliaryEndpointAvailabilityChecks

abbrev F : List Path := [[.arg]]
abbrev markedTarget : Marked := .app [[]] (.lam (.var 0))
  (.app [[.arg,.arg]] (.lam (.var 0)) (.lam (.var 0)))
def old : Marked.RelativeOldHistory F [[.arg]] (Marked.mark F source.erase)
    markedTarget :=
  .cons (.appR (.redRoot _ _ _)) (by decide) (.nil _)

theorem selected (p : Path) (member : p∈F) : source.degreeAt p=some (.atom 4) := by
  have equal := List.mem_singleton.mp member
  subst p;rfl

theorem targetClosed : Closed target.erase := actualStep.betaAt.beta.scoped closed

def leftTrace : BetaNodeHistoryPreimage actualHistory [.arg] [.arg,.arg] :=
  .one (step:=actualStep) redex_lookup actualOrigin (.nil _ _)

def rightOrigin : BetaNodePreimage (.var (.atom 5) 0) argumentTerm [.arg]
    [.arg,.fn] [.arg,.arg,.fn] :=
  .copied (q:=[]) (relative:=[.fn]) (by rfl) (by rfl)
def rightTrace : BetaNodeHistoryPreimage actualHistory [.arg,.fn] [.arg,.arg,.fn] :=
  .one (step:=actualStep) redex_lookup rightOrigin (.nil _ _)

def currentLambda : SyntaxIncidence.ProperPosition target :=
  ⟨[.arg,.fn],Or.inr ⟨.atom 7,.var (.atom 8) 0,rfl⟩⟩
def rightChain : EndpointChain target (some currentLambda) [[.arg,.fn]] := by
  change PrerequisiteChain target ([.arg]++[.fn]) [[.arg]++[.fn]]
  exact .redex_lam (by rfl)

theorem readSafe (edge : Path) (member : edge∈[[.arg,.fn]]) (node : LTerm)
    (lookup : target.subterm edge=some node) :
    node.label.OuterBarsSafe (fun payload=>payload≠Label.atom 4) := by
  have equal := List.mem_singleton.mp member
  subst edge
  have equal : node=.lam (.atom 7) (.var (.atom 8) 0) := Option.some.inj lookup.symm
  subst node;trivial

-- ONE canonical INIT, its actual nonroot beta, a marked incoming APP, and
-- two different actual TARGET vertices with the SAME nonempty safe READ list.
theorem actual_marked_incoming_safe_read_target_iso :
    ∃left right,SyntaxIncidence.Target source [.arg,.arg] left ∧
      SyntaxIncidence.Target source [.arg,.arg,.fn] right ∧
      BetaVertexHistoryPreimage actualHistory (some currentInner) left ∧
      BetaVertexHistoryPreimage actualHistory (some currentLambda) right ∧
      SuccessfulEndpointIso source closed left right :=
  safe_read_old_target_endpoint_iso old closed targetClosed
    (DegreeAligned.initial source F) selected leftTrace rightTrace
    current_target_endpoint (Or.inl rfl)
    actual_target_endpoint_chain rightChain ⟨ChainIncidenceIso.refl _⟩ readSafe readSafe

theorem actual_distinct_targets : currentInner.val≠currentLambda.val := by decide
theorem marked_incoming_is_not_read_safety :
    ¬currentArgument.label.OuterBarsSafe (fun x=>x≠Label.atom 4) := actual_marked

#print axioms safe_read_old_target_endpoint_iso
#print axioms initial
#print axioms actualHistory
#print axioms old
#print axioms actual_marked_incoming_safe_read_target_iso
#print axioms actual_distinct_targets
#print axioms marked_incoming_is_not_read_safety
end Lamping.Checks.SafeReadTargetEndpointIsoChecks
