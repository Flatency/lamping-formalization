import Lamping.Lamping.LabelledBetaEventAuxiliary
import Lamping.Lamping.InitialJointRepresentation
import Lamping.Checks.Phase6Projection

namespace Lamping.Checks.LabelledBetaEventAuxiliary
open AG Graph Lambda Lambda.Labelled SoundnessBetaAncestor

/-- A genuine beta from the closed encoding supplies every source premise.
The actual event supplies target matching and local development internally. -/
theorem actual_closed_event_auxiliary :
    ∃ (target : LTerm) (raw : ParallelHistory (initLabels identityApp).erase target.erase),
    ∃ event : LabelledGraphEvent (.beta 0) (ActualNet.initial identityApp)
      (ActualNet.ofNet actualBetaSite.reduce) (.inl ()) (initLabels identityApp) target raw,
    ∃ selection : OccurrenceFragmentSelection target actualBetaSite.reduce (.inl ()),
      AuxiliarySeparation
        (event.label_history.closed
          (show Closed (initLabels identityApp).erase from
            ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩)) selection := by
  let original := initLabels identityApp
  have closed : Closed original.erase := ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
  obtain ⟨flow⟩ := encode_flowBalance identityApp 0
  obtain ⟨balance⟩ := encode_indexed_balance identityApp 0
  have inputs := (encode_closed_independence identityApp closed 0).rootInputs
  have transparent := encode_closed_transparency identityApp closed 0
  have matching := encode_closed_matches identityApp closed 0
  obtain ⟨sourceSelection,joint⟩ := encode_initial_joint_realization original closed (init_is_INIT _) 0
  obtain ⟨target,raw,event,_labels,_matching⟩ :=
    ActualTraceSoundness.actual_beta_from_encoding.labelled_event
      (source:=original) flow rfl balance rfl inputs transparent matching closed
  have targetMatching := event.target_matches flow rfl balance rfl inputs transparent matching closed
  obtain ⟨targetSelection⟩ := targetMatching.occurrence_fragment_selection (event.label_history.closed closed)
  exact ⟨target,raw,event,targetSelection,
    event.beta_auxiliary_preserve (init_is_INIT _) (.nil _) (.nil _) (.nil _) closed
      flow rfl balance rfl inputs transparent matching sourceSelection targetSelection joint⟩

#print axioms actual_closed_event_auxiliary
end Lamping.Checks.LabelledBetaEventAuxiliary
