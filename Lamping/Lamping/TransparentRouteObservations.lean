import Lamping.Lamping.CancellationTypedBlocks
namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

/-- A finite transparent route with an unobservable terminal arrival has no
proper arrival at any position. This preserves occurrences, not just nodes. -/
theorem transparent_route_no_proper_arrivals (route : List (Endpoint g))
    (last : Endpoint g) (finish : route.getLast?=some last)
    (terminal : accessKind g [last]=none)
    (turns : ∀ e f,(e,f)∈route.zip route.tail →
      ∃ w d,g.wire e=.inr (.inr (w,d)) ∧f=.inr (.inr (w,!d))) :
    ∀ e∈route,accessKind g [e]=none := by
  induction route with
  | nil => cases finish
  | cons e route ih =>
    cases route with
    | nil =>
      have same : e=last := Option.some.inj (by simpa using finish)
      intro x member
      have sameX : x=e := List.mem_singleton.mp member
      rw [sameX,same]
      exact terminal
    | cons f route =>
      obtain ⟨w,d,arrives,_⟩ := turns e f (by simp)
      have firstNone : accessKind g [e]=none := by
        change (match g.wire e with
          | .inl ⟨node,p⟩ => portKind (g.label node).sort p
          | _ => none)=none
        rw [arrives]
      have after := ih (by simpa only [List.getLast?_cons_cons] using finish)
        (by intro x y member; exact turns x y (by
          simp only [List.tail_cons,List.zip_cons_cons,List.mem_cons]; exact Or.inr member))
      intro x member
      rcases List.mem_cons.mp member with same | later
      · subst x
        exact firstNone
      · exact after x later
end
end Lamping.AG
