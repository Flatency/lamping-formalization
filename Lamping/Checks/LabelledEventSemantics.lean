import Lamping.Lamping.LabelledEventSemantics
import Lamping.Checks.Phase6Projection

namespace Lamping.Checks.LabelledEventSemantics
open AG Graph Lambda Lambda.Labelled Phase6Projection SoundnessBetaAncestor

/-- The event alone supplies its actual step and labelled schedule. Source
semantics are constructed from the closed encoding; the event's separately
constructed target Matches witness is deliberately not used. -/
theorem actual_event_recovers_semantics :
    ∃ (target : LTerm) (raw : ParallelHistory repeatedSource.erase target.erase),
      LabelledGraphEvent (.beta 0) (ActualNet.initial identityApp)
        (ActualNet.ofNet actualBetaSite.reduce) (.inl ()) repeatedSource target raw ∧
      GraphStep (.beta 0) (ActualNet.initial identityApp) (ActualNet.ofNet actualBetaSite.reduce) ∧
      History raw.derivation.paths repeatedSource target ∧ Matches actualBetaSite.reduce (.inl ()) target.erase := by
  obtain ⟨target,raw,event,_labels,_matching⟩ := actual_existing_labels_event
  have closed : Closed identityApp := ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
  obtain ⟨flow⟩ := encode_flowBalance identityApp 0
  obtain ⟨balance⟩ := encode_indexed_balance identityApp 0
  exact ⟨target,raw,event,event.graph_step,event.label_history,
    event.target_matches flow rfl balance rfl
      (encode_closed_independence identityApp closed 0).rootInputs
      (encode_closed_transparency identityApp closed 0) (encode_closed_matches identityApp closed 0) closed⟩

#print axioms LabelledGraphEvent.graph_step
#print axioms LabelledGraphEvent.label_history
#print axioms LabelledGraphEvent.target_matches
#print axioms actual_event_recovers_semantics
end Lamping.Checks.LabelledEventSemantics
