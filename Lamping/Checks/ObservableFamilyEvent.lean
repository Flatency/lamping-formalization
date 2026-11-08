import Lamping.Lamping.ObservableFamilyEvent
import Lamping.Lamping.InitialJointRepresentation
import Lamping.Checks.Phase6Projection

namespace Lamping.Checks.ObservableFamilyEvent
open AG Graph Lambda Lambda.Labelled SoundnessBetaAncestor

private abbrev original := initLabels identityApp
private theorem closed : Closed original.erase :=
  ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩

/-- A real beta from the closed encoding constructs source REP, event,
global INIT and labelled history internally. The actual raw OLD schedule
is retained modulo deletion of empty selections and extends the complete
initial prefix. This is a single-event consumer, not full trace REP. -/
theorem actual_event_extends_complete_initial_prefix :
    ∃ (target : LTerm) (raw observed : ParallelHistory original.erase target.erase),
      LabelledGraphEvent (.beta 0) (ActualNet.initial identityApp)
        (ActualNet.ofNet actualBetaSite.reduce) (.inl ()) original target raw ∧
      ParallelHistory.Observable observed ∧ raw.derivation=observed.derivation ∧
      PermEq raw observed ∧ History observed.derivation.paths original target ∧
      CompleteDerivation ((ParallelHistory.nil original.erase).append observed) ∧
      Matches actualBetaSite.reduce (.inl ()) target.erase := by
  obtain ⟨flow⟩ := encode_flowBalance identityApp 0
  obtain ⟨balance⟩ := encode_indexed_balance identityApp 0
  have inputs := (encode_closed_independence identityApp closed 0).rootInputs
  have transparent := encode_closed_transparency identityApp closed 0
  have matching := encode_closed_matches identityApp closed 0
  obtain ⟨selection,joint⟩ := encode_initial_joint_realization original closed (init_is_INIT _) 0
  obtain ⟨target,raw,event,_labels,_targetMatches⟩ :=
    ActualTraceSoundness.actual_beta_from_encoding.labelled_event
      (source:=original) flow rfl balance rfl inputs transparent matching closed
  obtain ⟨observed,observable,same,permutation,complete⟩ :=
    event.observable_complete_extension (init_is_INIT _) closed (.nil _) (.nil _) (.nil _)
      matching selection joint.1
  exact ⟨target,raw,observed,event,observable,same,permutation,same ▸ event.label_history,
    complete,event.target_matches flow rfl balance rfl inputs transparent matching closed⟩

#print axioms LabelledGraphEvent.observable_complete_extension
#print axioms actual_event_extends_complete_initial_prefix
end Lamping.Checks.ObservableFamilyEvent
