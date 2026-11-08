import Lamping.Lamping.ObservableTraceProjection
import Lamping.Checks.Phase6Projection

namespace Lamping.Checks.ObservableTraceProjection
open AG Graph Lambda Lambda.Labelled Phase6Projection SoundnessBetaAncestor

/-- A real encoded beta supplies the aligned raw event and retains the
existing non-INIT labels through observable history projection. -/
theorem actual_existing_labels_observable :
    ∃ (target : LTerm) (raw observed : ParallelHistory repeatedSource.erase target.erase),
      LabelledGraphProjection (ActualNet.initial identityApp)
        (ActualNet.ofNet actualBetaSite.reduce) (.inl ()) [.beta 0] repeatedSource target raw ∧
      ParallelHistory.Observable observed ∧ raw.derivation=observed.derivation ∧
      PermEq raw observed ∧ History observed.derivation.paths repeatedSource target ∧
      RootInputs actualBetaSite.reduce (.inl ()) ∧ Matches actualBetaSite.reduce (.inl ()) target.erase :=
  initial_observable_trace_projection repeatedSource ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
    (ActualNet.ofNet actualBetaSite.reduce) [.beta 0] (.single ActualTraceSoundness.actual_beta_from_encoding)

/-- A real root-invisible physical beta yields a raw event with an empty
schedule. Its only observable projection is the empty syntax history here;
the physical graph step and the existing labels are both retained. -/
theorem actual_empty_fiber_silent :
    ∃ raw : ParallelHistory UnpairedRootProof.identity UnpairedRootProof.identity,
      LabelledGraphEvent (.beta 1) (ActualNet.ofNet UnpairedSourceProfiles.Model.site.net)
        (ActualNet.ofNet UnpairedSourceProfiles.Model.site.reduce) ()
        (initLabels UnpairedRootProof.identity) (initLabels UnpairedRootProof.identity) raw ∧
      raw.derivation=(ParallelHistory.nil UnpairedRootProof.identity).derivation ∧
      PermEq raw (.nil UnpairedRootProof.identity) := by
  obtain ⟨ps,marked,target,complete,labels,erased,_matching⟩ := actual_empty_fiber_projects
  have no_steps : ps=[] :=
    (redexFiber_complete_empty_endpoint complete (by rfl)).1
  subst ps
  cases labels
  let step : ParallelStep [] UnpairedRootProof.identity UnpairedRootProof.identity :=
    ⟨[],marked,complete,erased.symm⟩
  refine ⟨.single step,.beta _ UnpairedSourceProfiles.Model.site (.refl _) (.refl _)
    complete (.nil _) erased.symm,?_,.empty step⟩
  apply Derivation.ext
  rfl

#print axioms GraphTrace.observable_projection
#print axioms initial_observable_trace_projection
#print axioms actual_existing_labels_observable
#print axioms actual_empty_fiber_silent
end Lamping.Checks.ObservableTraceProjection
