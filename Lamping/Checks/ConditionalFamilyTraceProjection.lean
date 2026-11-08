import Lamping.Lamping.ConditionalFamilyTraceProjection
import Lamping.Lamping.InitialJointRepresentation
import Lamping.Checks.Phase6Projection

namespace Lamping.Checks.ConditionalFamilyTraceProjection
open AG Graph Lambda Lambda.Labelled SoundnessBetaAncestor

private abbrev original := initLabels identityApp
private theorem closed : Closed original.erase :=
  ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩

/-- The concrete one-beta projection supplies its only event-source REP
from the actual closed initial encoding. This exercises conditional trace
assembly; it does not establish REP for arbitrary later action/beta sources. -/
theorem actual_single_beta_complete_projection :
    ∃ (target : LTerm) (raw observed : ParallelHistory original.erase target.erase),
    ∃ aligned : LabelledGraphProjection (ActualNet.initial identityApp)
      (ActualNet.ofNet actualBetaSite.reduce) (.inl ()) [.beta 0] original target raw,
      aligned.SourceChainREP ∧ParallelHistory.Observable observed ∧
      raw.derivation=observed.derivation ∧PermEq raw observed ∧
      History observed.derivation.paths original target ∧CompleteDerivation observed ∧
      RootInputs actualBetaSite.reduce (.inl ()) ∧Matches actualBetaSite.reduce (.inl ()) target.erase := by
  obtain ⟨flow⟩ := encode_flowBalance identityApp 0
  obtain ⟨balance⟩ := encode_indexed_balance identityApp 0
  have inputs := (encode_closed_independence identityApp closed 0).rootInputs
  have transparent := encode_closed_transparency identityApp closed 0
  have matching := encode_closed_matches identityApp closed 0
  obtain ⟨selection,joint⟩ := encode_initial_joint_realization original closed (init_is_INIT _) 0
  obtain ⟨target,first,event,_labels,_next⟩ :=
    ActualTraceSoundness.actual_beta_from_encoding.labelled_event
      (source:=original) flow rfl balance rfl inputs transparent matching closed
  let tail : LabelledGraphProjection (ActualNet.ofNet actualBetaSite.reduce)
      (ActualNet.ofNet actualBetaSite.reduce) (.inl ()) [] target target (.nil target.erase) :=
    .iso (.refl _)
  let aligned := LabelledGraphProjection.cons event tail
  have represented : aligned.SourceChainREP :=
    .cons (event:=event) (tail:=tail) closed selection joint.1 (.iso (.refl _))
  obtain ⟨observed,observable,same,permutation,labels,complete,final⟩ :=
    aligned.conditional_complete_projection represented (init_is_INIT _) (.nil _) (.nil _) (.nil _)
      flow rfl balance rfl inputs transparent matching closed
  exact ⟨target,_,observed,aligned,represented,observable,same,permutation,labels,complete,final⟩

/-- A zero-event alignment needs no source selector or REP certificate.
Its still-reducible term is retained, with a complete empty history. -/
theorem zero_events_need_no_source_rep :
    ∃ aligned : LabelledGraphProjection (ActualNet.initial identityApp) (ActualNet.initial identityApp)
      (.inl ()) [] original original (.nil original.erase),
      aligned.SourceChainREP ∧CompleteDerivation (ParallelHistory.nil original.erase) ∧
      IsRedex original.erase :=
  ⟨.iso (.refl _),.iso (.refl _),.nil _,True.intro⟩

#print axioms LabelledGraphProjection.family_steps_of_source_rep
#print axioms LabelledGraphProjection.conditional_complete_projection
#print axioms actual_single_beta_complete_projection
#print axioms zero_events_need_no_source_rep
end Lamping.Checks.ConditionalFamilyTraceProjection
