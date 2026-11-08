import Lamping.Lamping.BetaLabelledProjection
import Lamping.Lamping.LabelledGraphEvents
import Lamping.Lamping.LabelledTraceProjection
import Lamping.Checks.InsertionCoherence
import Lamping.Checks.UnpairedSourceProfiles

namespace Lamping.Checks.Phase6Projection
open AG Graph Lambda Lambda.Labelled SoundnessBetaAncestor

def repeatedSource : LTerm := .app (.atom 9)
  (.lam (.atom 9) (.var (.atom 9) 0)) (.lam (.atom 9) (.var (.atom 9) 0))

theorem repeated_source_not_init : ¬INIT repeatedSource := by
  simp [INIT,repeatedSource,LTerm.labels]

/-- A real observable beta consumes the old fiber while retaining an existing
non-INIT labelling. The source labels are not silently replaced by initLabels. -/
theorem actual_existing_labels_project :
    ∃ ps marked target,
      Marked.CompleteOldDevelopment (actualBetaSite.betaSyntaxFiber (.inl ()) repeatedSource.erase)
        repeatedSource.erase ps marked ∧
      History ps repeatedSource target ∧ target.erase=marked.erase ∧
      Matches actualBetaSite.reduce (.inl ()) target.erase := by
  have closed : Closed identityApp := ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
  obtain ⟨balance⟩ := encode_indexed_balance identityApp 0
  exact actualBetaSite.beta_labelled_projection closed
    (betaEncodingIso.matches (encode_closed_matches identityApp closed 0))
    (betaEncodingIso.rootInputs (encode_closed_independence identityApp closed 0).rootInputs)
    actualFlow rfl (betaEncodingIso.indexed_balance balance) rfl
    (betaEncodingIso.transparency (encode_closed_transparency identityApp closed 0))

/-- An actual beta in a root-invisible component also has a labelled
projection; this conclusion does not manufacture a nonempty family event. -/
theorem actual_empty_fiber_projects :
    ∃ ps marked target,
      Marked.CompleteOldDevelopment
        (UnpairedSourceProfiles.Model.site.betaSyntaxFiber () UnpairedRootProof.identity)
        UnpairedRootProof.identity ps marked ∧
      History ps (initLabels UnpairedRootProof.identity) target ∧
      target.erase=marked.erase ∧ Matches UnpairedSourceProfiles.Model.site.reduce () target.erase := by
  open UnpairedSourceProfiles.Model in
    exact site.beta_labelled_projection (source:=initLabels UnpairedRootProof.identity)
      (by change 0<1; decide)
      UnpairedRootProof.root_matches UnpairedRootProof.root_inputs flow rfl indexed rfl
      UnpairedRootProof.root_transparency

#print axioms PathSite.beta_labelled_projection
#print axioms actual_existing_labels_project
#print axioms actual_empty_fiber_projects
#print axioms repeated_source_not_init

/-- The actual step, including its noncanonical source carrier, constructs
the raw event; an INIT proof of repeatedSource is neither possible nor needed. -/
theorem actual_existing_labels_event :
    ∃ (target : LTerm) (projection : ParallelHistory repeatedSource.erase target.erase),
      LabelledGraphEvent (.beta 0) (ActualNet.initial identityApp)
        (ActualNet.ofNet actualBetaSite.reduce) (.inl ()) repeatedSource target projection ∧
      History projection.derivation.paths repeatedSource target ∧
      Matches actualBetaSite.reduce (.inl ()) target.erase := by
  have closed : Closed identityApp := ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
  obtain ⟨flow⟩ := encode_flowBalance identityApp 0
  obtain ⟨balance⟩ := encode_indexed_balance identityApp 0
  exact ActualTraceSoundness.actual_beta_from_encoding.labelled_event flow rfl balance rfl
    (encode_closed_independence identityApp closed 0).rootInputs
    (encode_closed_transparency identityApp closed 0) (encode_closed_matches identityApp closed 0) closed

theorem actual_empty_fiber_event :
    ∃ (target : LTerm) (projection : ParallelHistory UnpairedRootProof.identity target.erase),
      LabelledGraphEvent (.beta 1) (ActualNet.ofNet UnpairedSourceProfiles.Model.site.net)
        (ActualNet.ofNet UnpairedSourceProfiles.Model.site.reduce) ()
        (initLabels UnpairedRootProof.identity) target projection ∧
      History projection.derivation.paths (initLabels UnpairedRootProof.identity) target ∧
      Matches UnpairedSourceProfiles.Model.site.reduce () target.erase := by
  open UnpairedSourceProfiles.Model in
    exact actual_beta_step.labelled_event (source:=initLabels UnpairedRootProof.identity)
      flow rfl indexed rfl UnpairedRootProof.root_inputs UnpairedRootProof.root_transparency
      UnpairedRootProof.root_matches (by change 0<1; decide)

#print axioms GraphStep.labelled_event
#print axioms actual_existing_labels_event
#print axioms actual_empty_fiber_event

theorem actual_existing_labels_trace :
    ∃ (target : LTerm) (projection : ParallelHistory repeatedSource.erase target.erase),
      LabelledGraphProjection (ActualNet.initial identityApp)
        (ActualNet.ofNet actualBetaSite.reduce) (.inl ()) [.beta 0] repeatedSource target projection ∧
      History projection.derivation.paths repeatedSource target ∧
      RootInputs actualBetaSite.reduce (.inl ()) ∧ Matches actualBetaSite.reduce (.inl ()) target.erase :=
  initial_labelled_trace_projection repeatedSource ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
    (ActualNet.ofNet actualBetaSite.reduce) [.beta 0] (.single ActualTraceSoundness.actual_beta_from_encoding)

/-- Zero graph steps keep the existing non-INIT labels exactly; raw history
projection does not assert that the initial redex has already normalized. -/
theorem actual_zero_trace_retains_labels :
    ∃ (projection : ParallelHistory repeatedSource.erase repeatedSource.erase),
      LabelledGraphProjection (ActualNet.initial identityApp) (ActualNet.initial identityApp)
        (.inl ()) [] repeatedSource repeatedSource projection ∧
      History projection.derivation.paths repeatedSource repeatedSource ∧ IsRedex repeatedSource.erase := by
  obtain ⟨target,projection,aligned,labels,_inputs,_matching⟩ :=
    initial_labelled_trace_projection repeatedSource ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
      (ActualNet.initial identityApp) [] (.refl _)
  cases aligned with
  | iso same => exact ⟨.nil _,.iso same,labels,True.intro⟩

#print axioms GraphTrace.labelled_projection
#print axioms initial_labelled_trace_projection
#print axioms actual_existing_labels_trace
#print axioms actual_zero_trace_retains_labels
end Lamping.Checks.Phase6Projection
