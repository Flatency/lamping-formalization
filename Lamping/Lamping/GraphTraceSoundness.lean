import Lamping.Lamping.BetaStepSoundness
import Lamping.Lamping.GraphRootInputPreservation
import Lamping.Lamping.InitialMatching
import Lamping.Lamping.InitialIndependence

namespace Lamping.AG
open Graph Lambda

private theorem append_betas {t u v : Term} (first : Betas t u) (last : Betas u v) : Betas t v := by
  induction first with
  | refl => exact last
  | cons step tail ih => exact .cons step (ih last)

section
variable {B : Type} [FiniteNames B]

/-- Soundness of arbitrary finite actual traces, including beta and carrier
isomorphisms. Intermediate Matches, root inputs and structural witnesses
are derived at each step, not supplied by the caller. -/
theorem GraphTrace.soundness
    {g h : ActualNet B} {schemas : List Schema} (trace : GraphTrace g h schemas)
    {directions : B → Bool} {heights : B → Int} {root : B}
    (flow : FlowBalance g.net directions) (positive : directions root=true)
    (balance : IndexedLevelBalance g.net heights) (rootDepth : heights root=0)
    (inputs : RootInputs g.net root) (oldT : Transparency g.net root)
    {t : Term} (matching : Matches g.net root t) (closed : Closed t) :
    ∃ u, Betas t u ∧ RootInputs h.net root ∧ Matches h.net root u := by
  induction trace generalizing t with
  | iso same => exact ⟨t,.refl _,same.rootInputs inputs,same.matches matching⟩
  | cons step tail ih =>
    obtain ⟨middle,reductions,nextMatching⟩ := step.soundness flow positive balance rootDepth inputs oldT matching closed
    have nextInputs := step.rootInputs flow positive balance rootDepth inputs oldT matching
    obtain ⟨nextFlow⟩ := step.flowBalance flow
    obtain ⟨nextBalance⟩ := step.indexed_balance balance
    have nextT := step.transparency_indexed flow positive balance rootDepth oldT
    obtain ⟨u,remaining,finalInputs,finalMatching⟩ := ih nextFlow nextBalance nextInputs nextT nextMatching (reductions.scoped closed)
    exact ⟨u,append_betas reductions remaining,finalInputs,finalMatching⟩
end

/-- Closed initial encodings have actual Matches after every finite trace.
The reduct and its beta derivation are constructed from that trace. -/
theorem initial_trace_soundness (t : Term) (closed : Closed t)
    (target : ActualNet (Boundary t)) (schemas : List Schema)
    (trace : GraphTrace (ActualNet.initial t) target schemas) :
    ∃ u, Betas t u ∧ RootInputs target.net (.inl ()) ∧ Matches target.net (.inl ()) u := by
  obtain ⟨flow⟩ := encode_flowBalance t 0
  obtain ⟨balance⟩ := encode_indexed_balance t 0
  exact trace.soundness flow rfl balance rfl (encode_closed_independence t closed 0).rootInputs
    (encode_closed_transparency t closed 0) (encode_closed_matches t closed 0) closed

end Lamping.AG
