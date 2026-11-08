import Lamping.Lambda.ObservableFamilyHistory
import Lamping.Checks.BetaFiberFamilies

namespace Lamping.Checks.ObservableFamilyHistory
open AG Graph Lambda Lambda.Labelled

private abbrev original := initLabels identityApp

/-- A real physical whole-family development is placed between empty
boundaries. The certificate after the first empty boundary is transported
through generated permutation, retaining the original source history.
Normalization yields a complete observable history with the same actual
contraction paths and the same matched physical RHS. -/
theorem physical_family_survives_silent_boundaries :
    ∃ target : LTerm,∃ step : ParallelStep
      (actualBetaSite.betaSyntaxFiber (.inl ()) original.erase) original.erase target.erase,
    ∃ observed : ParallelHistory original.erase target.erase,
      ParallelHistory.Observable observed ∧CompleteDerivation observed ∧
      observed.derivation.paths=step.paths ∧
      PermEq (.cons (ParallelStep.empty original.erase)
        (.cons step (.single (ParallelStep.empty target.erase)))) observed ∧
      Matches actualBetaSite.reduce (.inl ()) target.erase := by
  obtain ⟨target,step,_labels,matching,whole,_complete⟩ :=
    BetaFiberFamilies.actual_physical_beta_projects_complete_family
  let prior := ParallelHistory.nil original.erase
  let silence := ParallelStep.empty original.erase
  have afterSilence : CompleteFamilyStep (prior.append (.single silence)) step :=
    whole.prefix_permutation (PermEq.empty silence).symm
  let raw : ParallelHistory original.erase target.erase :=
    .cons silence (.cons step (.single (ParallelStep.empty target.erase)))
  have certified : FamilyStepsOrSilent prior raw :=
    .cons (.inl rfl) (.cons (.inr afterSilence) (.cons (.inl rfl) (.nil _)))
  obtain ⟨observed,positive,same,permutation,complete⟩ :=
    certified.observable_complete (.nil _)
  refine ⟨target,step,observed,positive,complete,?_,permutation,matching⟩
  rw [←same]
  change []++(step.paths++([]++[]))=step.paths
  simp only [List.nil_append,List.append_nil]

#print axioms CompleteFamilyStep.prefix_permutation
#print axioms FamilyStepsOrSilent.observable_complete
#print axioms physical_family_survives_silent_boundaries
end Lamping.Checks.ObservableFamilyHistory
