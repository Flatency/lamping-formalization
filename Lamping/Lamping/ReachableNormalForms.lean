import Lamping.Lamping.GraphTraceSoundness
import Lamping.Lamping.RootNormalFormReflection

namespace Lamping.AG
open Graph Lambda

/-- If an actual finite trace from a closed initial encoding ends in a
graph normal form, its matched syntax is a beta normal reduct. This is
reflection at a given endpoint, not an assertion that every trace terminates. -/
theorem initial_trace_normal_form (t : Term) (closed : Closed t)
    (target : ActualNet (Boundary t)) (schemas : List Schema)
    (trace : GraphTrace (ActualNet.initial t) target schemas)
    (normal : GraphNormal target) :
    ∃ u, Betas t u ∧ Closed u ∧ Matches target.net (.inl ()) u ∧ ¬∃ v,Beta u v := by
  obtain ⟨u,reductions,inputs,matching⟩ := initial_trace_soundness t closed target schemas trace
  obtain ⟨flow⟩ := initial_trace_flowBalance t target schemas trace
  obtain ⟨balance⟩ := initial_trace_indexed_balance t target schemas trace
  have packed : ActualNet.ofNet target.net=target := by cases target; rfl
  have endpointNormal : GraphNormal (ActualNet.ofNet target.net) := packed.symm ▸ normal
  exact ⟨u,reductions,reductions.scoped closed,matching,
    endpointNormal.no_syntax_beta_of_root_inputs matching inputs balance rfl flow⟩

/-- The same result with the finite schema list hidden by reachability. -/
theorem initial_reachable_normal_form (t : Term) (closed : Closed t)
    (target : ActualNet (Boundary t))
    (reachable : GraphReachable (ActualNet.initial t) target)
    (normal : GraphNormal target) :
    ∃ u, Betas t u ∧ Closed u ∧ Matches target.net (.inl ()) u ∧ ¬∃ v,Beta u v := by
  obtain ⟨schemas,trace⟩ := reachable
  exact initial_trace_normal_form t closed target schemas trace normal

end Lamping.AG
