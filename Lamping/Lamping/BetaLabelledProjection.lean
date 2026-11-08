import Lamping.Lamping.BetaStepSoundness

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
variable {root : B} {source : LTerm}

/-- Lift the SAME actual complete OLD-fiber schedule from the existing source
labels. Local INIT is used only inside the erased matching proof. No INIT
condition is imposed on the existing source, and no family completeness is
asserted by this lemma. -/
theorem PathSite.beta_labelled_projection
    (closed : Closed source.erase) (matching : Matches site.net root source.erase)
    (inputs : RootInputs site.net root)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {heights : B → Int} (balance : IndexedLevelBalance site.net heights) (rootDepth : heights root=0)
    (transparency : Transparency site.net root) :
    ∃ ps marked target,
      Marked.CompleteOldDevelopment (site.betaSyntaxFiber root source.erase) source.erase ps marked ∧
      History ps source target ∧ target.erase=marked.erase ∧ Matches site.reduce root target.erase := by
  obtain ⟨ps,marked,complete⟩ := site.betaSyntaxFiber_complete_exists root source.erase
  have erasedHistory := physicalBetaFiber_complete_betaHistory complete
  obtain ⟨target,history,erased⟩ := lift_history erasedHistory source rfl
  obtain ⟨localTarget,localHistory,localErased⟩ :=
    lift_history erasedHistory (initLabels source.erase) (erase_initLabels _)
  obtain ⟨relative,normal⟩ := (Marked.completeOld_iff _ _).mp complete
  have localMatching : Matches site.net root (initLabels source.erase).erase := by
    simpa only [erase_initLabels] using matching
  have finalMatching := site.beta_complete_matches (init_is_INIT source.erase)
    (by simpa only [erase_initLabels] using closed) localMatching inputs flow positive balance rootDepth
    transparency (by simpa only [erase_initLabels] using relative) normal localHistory
  refine ⟨ps,marked,target,complete,history,erased,?_⟩
  rw [erased,←localErased]
  exact finalMatching

end
end Lamping.AG
