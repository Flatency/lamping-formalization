import Lamping.Lamping.BetaCompleteMatching
import Lamping.Lamping.ActionMatching
import Lamping.Lamping.RootCancellationMatching

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

section
variable {B : Type} [FiniteNames B]
variable {g h : ActualNet B} {directions : B → Bool} {heights : B → Int} {root : B}

/-- A physical beta contracts its complete OLD syntax fiber, which may be
empty or contain several occurrences. The local initial labelling is used
only to prove this erased semantic step; it does not reset a global family history. -/
theorem GraphStep.beta_soundness {i : Nat} (step : GraphStep (.beta i) g h)
    (flow : FlowBalance g.net directions) (positive : directions root=true)
    (balance : IndexedLevelBalance g.net heights) (rootDepth : heights root=0)
    (inputs : RootInputs g.net root) (oldT : Transparency g.net root)
    {t : Term} (matching : Matches g.net root t) (closed : Closed t) :
    ∃ u, Betas t u ∧ Matches h.net root u := by
  cases step with
  | atSite kept site sourceIso targetIso =>
    obtain ⟨ps,marked,complete⟩ := site.betaSyntaxFiber_complete_exists root t
    obtain ⟨relative,normal⟩ := (Marked.completeOld_iff _ _).mp complete
    have erasedHistory := physicalBetaFiber_complete_betaHistory complete
    obtain ⟨target,history,erased⟩ := lift_history erasedHistory (initLabels t) (erase_initLabels t)
    have sourceMatching : Matches site.net root (initLabels t).erase := by
      simpa only [erase_initLabels] using sourceIso.matches matching
    have targetMatching := site.beta_complete_matches (init_is_INIT t)
      (by simpa only [erase_initLabels] using closed) sourceMatching
      (sourceIso.rootInputs inputs) (sourceIso.flowBalance flow) positive
      (sourceIso.indexed_balance balance) rootDepth (sourceIso.transparency oldT)
      (by simpa only [erase_initLabels] using relative) normal history
    refine ⟨target.erase,?_,targetIso.matches targetMatching⟩
    rw [erased]
    exact physicalBetaFiber_complete_betas complete

/-- All seven actual graph rules are semantically sound. Auxiliary rules
stutter; a beta rule uses the actual finite complete old development. -/
theorem GraphStep.soundness {schema : Schema} (step : GraphStep schema g h)
    (flow : FlowBalance g.net directions) (positive : directions root=true)
    (balance : IndexedLevelBalance g.net heights) (rootDepth : heights root=0)
    (inputs : RootInputs g.net root) (oldT : Transparency g.net root)
    {t : Term} (matching : Matches g.net root t) (closed : Closed t) :
    ∃ u, Betas t u ∧ Matches h.net root u := by
  cases schema with
  | beta i => exact step.beta_soundness flow positive balance rootDepth inputs oldT matching closed
  | fanCancel i => exact ⟨t,.refl _,step.cancellation_matches_rootInputs (.fan i) flow positive inputs balance rootDepth oldT matching⟩
  | croCancel i => exact ⟨t,.refl _,step.cancellation_matches_rootInputs (.cro i) flow positive inputs balance rootDepth oldT matching⟩
  | braCancel i => exact ⟨t,.refl _,step.cancellation_matches_rootInputs (.bra i) flow positive inputs balance rootDepth oldT matching⟩
  | fanAction f i j lt => exact ⟨t,.refl _,step.action_matches_rootInputs (.fan f i j lt) flow positive balance rootDepth inputs oldT matching⟩
  | croAction f i j lt => exact ⟨t,.refl _,step.action_matches_rootInputs (.cro f i j lt) flow positive balance rootDepth inputs oldT matching⟩
  | braAction f i j lt => exact ⟨t,.refl _,step.action_matches_rootInputs (.bra f i j lt) flow positive balance rootDepth inputs oldT matching⟩
end
end Lamping.AG
