import Lamping.Lamping.CancellationJointRepresentation
import Lamping.Lamping.JointRepresentationTransport
import Lamping.Lamping.RootCancellationMatching
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {B : Type} [FiniteNames B]

/-- Transport through the actual site and BOTH boundary-fixing carrier
isomorphisms. Both matches are explicit semantic hypotheses at this layer. -/
theorem GraphStep.cancellation_joint_representation {s : Schema} {g h : ActualNet B}
    (step : GraphStep s g h) (cancel : IsCancellation s)
    {boundary : B → Bool} (flow : FlowBalance g.net boundary) (root : B)
    (positive : boundary root=true) {current : LTerm} (closed : Closed current.erase)
    (sourceMatches : Matches g.net root current.erase)
    (targetMatches : Matches h.net root current.erase)
    (source : OccurrenceFragmentSelection current g.net root)
    (target : OccurrenceFragmentSelection current h.net root) :
    JointRepresentation closed target ↔JointRepresentation closed source := by
  cases step with
  | atSite kept site sourceIso targetIso =>
    have localSourceMatches := sourceIso.matches sourceMatches
    have localTargetMatches := targetIso.symm.matches targetMatches
    obtain ⟨localSource⟩ := localSourceMatches.occurrence_fragment_selection closed
    obtain ⟨localTarget⟩ := localTargetMatches.occurrence_fragment_selection closed
    exact (targetIso.joint_representation localTargetMatches closed localTarget target).trans
      ((site.cancellation_joint_representation cancel (sourceIso.flowBalance flow) root positive closed
        localSourceMatches localTargetMatches localSource localTarget).trans
        (sourceIso.joint_representation sourceMatches closed source localSource))

/-- Cancellation-only actual traces, including zero-step carrier renaming.
Every intermediate match and structural input is derived from the actual
step by P06; no target Matches or intermediate REP is supplied. -/
theorem GraphTrace.cancellation_joint_representation {g h : ActualNet B} {schemas : List Schema}
    (trace : GraphTrace g h schemas) (cancellations : ∀ s∈schemas,IsCancellation s)
    {boundary : B → Bool} {heights : B → Int} (flow : FlowBalance g.net boundary)
    (root : B) (positive : boundary root=true) (balance : IndexedLevelBalance g.net heights)
    (rootDepth : heights root=0) (inputs : RootInputs g.net root) (transparent : Transparency g.net root)
    {current : LTerm} (closed : Closed current.erase) (matching : Matches g.net root current.erase)
    (source : OccurrenceFragmentSelection current g.net root)
    (target : OccurrenceFragmentSelection current h.net root) :
    JointRepresentation closed target ↔JointRepresentation closed source := by
  induction trace with
  | iso same => exact same.joint_representation matching closed source target
  | @cons g middle final s ss step tail ih =>
    have cancel := cancellations s List.mem_cons_self
    have nextMatches := step.cancellation_matches_rootInputs cancel flow positive inputs balance rootDepth transparent matching
    have nextInputs := step.cancellation_rootInputs cancel flow positive inputs
    obtain ⟨nextFlow⟩ := step.flowBalance flow
    obtain ⟨nextBalance⟩ := step.indexed_balance balance
    have nextT := step.transparency_indexed flow positive balance rootDepth transparent
    obtain ⟨middleSelection⟩ := nextMatches.occurrence_fragment_selection closed
    have first := step.cancellation_joint_representation cancel flow root positive closed matching nextMatches source middleSelection
    have remaining := ih (fun schema member=>cancellations schema (List.mem_cons_of_mem _ member))
      nextFlow nextBalance nextInputs nextT nextMatches middleSelection target
    exact remaining.trans first
end
end Lamping.AG
