import Lamping.Lamping.CancellationRepresentationTrace
import Lamping.Lamping.InitialJointRepresentation
import Lamping.Lamping.InitialFullIndependence
import Lamping.Lamping.InitialTransparency
namespace Lamping.Checks.CancellationRepresentationTrace
open AG Graph Lambda Lambda.Labelled

/-- All structural and semantic source hypotheses are constructed from closed
initial syntax. The caller supplies only the actual cancellation-only trace. -/
theorem all_closed_initial_cancellation_traces (term : Term) (closed : Closed term)
    (target : ActualNet (Boundary term)) (schemas : List Schema)
    (trace : GraphTrace (ActualNet.initial term) target schemas)
    (cancellations : ∀ s∈schemas,IsCancellation s) :
    ∃ selection : OccurrenceFragmentSelection (initLabels term) target.net (.inl ()),
      JointRepresentation (show Closed (initLabels term).erase from by
        simpa only [erase_initLabels] using closed) selection := by
  have labelledClosed : Closed (initLabels term).erase := by
    simpa only [erase_initLabels] using closed
  have matching : Matches (ActualNet.initial term).net (.inl ()) (initLabels term).erase := by
    simpa only [erase_initLabels] using encode_closed_matches term closed 0
  obtain ⟨flow⟩ := encode_flowBalance term 0
  obtain ⟨balance⟩ := encode_indexed_balance term 0
  have inputs := (encode_closed_independence term closed 0).rootInputs
  have transparent := encode_closed_transparency term closed 0
  have nextMatches := trace.cancellation_matches_rootInputs cancellations flow rfl
    inputs balance rfl transparent matching
  have initialSupply : ∃ source : OccurrenceFragmentSelection (initLabels term)
      (ActualNet.initial term).net (.inl ()),JointRepresentation labelledClosed source := by
    let property (t : Term) : Prop := ∃ selection : OccurrenceFragmentSelection (initLabels term)
        (encode 0 t).net (.inl ()),JointRepresentation labelledClosed selection
    have atErased : property (initLabels term).erase :=
      encode_initial_joint_realization (initLabels term) labelledClosed (init_is_INIT term) 0
    exact Eq.mp (congrArg property (erase_initLabels term)) atErased
  obtain ⟨source,initial⟩ := initialSupply
  obtain ⟨selection⟩ := nextMatches.occurrence_fragment_selection labelledClosed
  refine ⟨selection,?_⟩
  exact (trace.cancellation_joint_representation cancellations flow (.inl ()) rfl balance rfl
    inputs transparent labelledClosed matching source selection).mpr initial

#print axioms GraphStep.cancellation_joint_representation
#print axioms GraphTrace.cancellation_joint_representation
#print axioms all_closed_initial_cancellation_traces
end Lamping.Checks.CancellationRepresentationTrace
