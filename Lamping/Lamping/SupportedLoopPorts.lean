import Lamping.Lamping.SupportedExpandedLoops
import Lamping.Lamping.BetaDetourCoherence
namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}

/-- Finite supported insertion preserves the original binder's two physical
ports. This is endpoint geometry only; no expanded shell or labels follow. -/
theorem SupportedExpandedBindingLoop.beta_endpoints {ambient binder loop}
    (support : SupportedExpandedBindingLoop g root ambient binder loop)
    (edge : BetaEdge g) (sameBinder : binder=edge.lam) :
    loop.head?=some (.inl ⟨edge.lam,edge.lamBody⟩) ∧
      loop.getLast?=some (g.wire (.inl ⟨edge.lam,edge.lamBind⟩)) := by
  induction support generalizing edge with
  | base ambient es a b binding =>
    obtain ⟨first,last,_⟩ := binding.beta_ports edge sameBinder
    exact ⟨first,last⟩
  | insert ambient binder inner pre innerLoop tail outer nested previousBody nestedBody preEnd innerStart innerEnd outerIH nestedIH =>
    obtain ⟨first,last⟩ := outerIH edge sameBinder
    have nonempty : pre≠[] := by intro empty; rw [empty] at preEnd; cases preEnd
    constructor
    · cases pre with
      | nil => exact False.elim (nonempty rfl)
      | cons x xs => exact first
    · cases lastTail : tail.getLast? <;>
        simpa [List.getLast?_append,List.getLast?_cons,lastTail] using last

/-- The finite support supplies its own lambda ports. Only the actual
argument/body trees, ambient equality and application-prefix endpoint remain
caller obligations. Actual-history construction of the support is separate. -/
theorem SupportedExpandedBindingLoop.insert_at_beta {ambient binder loop}
    (support : SupportedExpandedBindingLoop g root ambient binder loop)
    (edge : BetaEdge g) (stem suffix : List (Endpoint g))
    (ambientEq : ambient=stem++edge.principal) (sameBinder : binder=edge.lam)
    (argument : GeneratedExpandedProperPath g root (stem++edge.argEnd::suffix))
    (body : GeneratedExpandedProperPath g root (ambient++loop))
    (stemEnd : stem.getLast?=some (g.wire (.inl ⟨edge.app,edge.appCtx⟩))) :
    GeneratedExpandedProperPath g root
      (stem++edge.principal++loop++edge.reverseRoute++[edge.argEnd]++suffix) := by
  obtain ⟨first,last⟩ := support.beta_endpoints edge sameBinder
  exact support.insert_admissible edge stem suffix ambientEq sameBinder argument body stemEnd first last
end
end Lamping.AG
