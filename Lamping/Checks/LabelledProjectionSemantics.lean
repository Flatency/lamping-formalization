import Lamping.Lamping.LabelledProjectionSemantics
import Lamping.Checks.Phase6Projection

namespace Lamping.Checks.LabelledProjectionSemantics
open AG Graph Lambda Lambda.Labelled Phase6Projection SoundnessBetaAncestor

/-- Starting from the aligned raw events, reconstruct the actual trace,
original labels, root inputs and fixed-target Matches. Previously returned
semantic witnesses are discarded. Repeated source labels are retained. -/
theorem actual_projection_recovers_semantics :
    ∃ (target : LTerm) (raw : ParallelHistory repeatedSource.erase target.erase),
      LabelledGraphProjection (ActualNet.initial identityApp)
        (ActualNet.ofNet actualBetaSite.reduce) (.inl ()) [.beta 0] repeatedSource target raw ∧
      GraphTrace (ActualNet.initial identityApp) (ActualNet.ofNet actualBetaSite.reduce) [.beta 0] ∧
      History raw.derivation.paths repeatedSource target ∧
      RootInputs actualBetaSite.reduce (.inl ()) ∧ Matches actualBetaSite.reduce (.inl ()) target.erase := by
  obtain ⟨target,raw,aligned,_labels,_inputs,_matching⟩ := actual_existing_labels_trace
  have closed : Closed identityApp := ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
  obtain ⟨flow⟩ := encode_flowBalance identityApp 0
  obtain ⟨balance⟩ := encode_indexed_balance identityApp 0
  have final := aligned.target_matches flow rfl balance rfl
    (encode_closed_independence identityApp closed 0).rootInputs
    (encode_closed_transparency identityApp closed 0) (encode_closed_matches identityApp closed 0) closed
  exact ⟨target,raw,aligned,aligned.graph_trace,aligned.label_history,final⟩

/-- Zero actual events preserve the still-present redex. Reconstructing
projection semantics does not assert normalization or strategy termination. -/
theorem zero_projection_keeps_redex :
    ∃ raw : ParallelHistory repeatedSource.erase repeatedSource.erase,
      History raw.derivation.paths repeatedSource repeatedSource ∧ IsRedex repeatedSource.erase := by
  obtain ⟨raw,aligned,_labels,redex⟩ := actual_zero_trace_retains_labels
  exact ⟨raw,aligned.label_history,redex⟩

#print axioms LabelledGraphProjection.graph_trace
#print axioms LabelledGraphProjection.label_history
#print axioms LabelledGraphProjection.target_matches
#print axioms actual_projection_recovers_semantics
#print axioms zero_projection_keeps_redex
end Lamping.Checks.LabelledProjectionSemantics
