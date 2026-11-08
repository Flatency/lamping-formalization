import Lamping.Lamping.PathRewrite
namespace Lamping.AG
open Graph

/-- An alternating principal route, indexed by its arriving endpoint. The
snoc constructor crosses a genuine transparent vertex before the next segment. -/
inductive PrincipalRoute {V : Type} (p : Pairing (Bool ⊕ (V × Bool))) :
    Bool ⊕ (V × Bool) → Prop where
  | single : PrincipalRoute p (p (.inl false))
  | snoc {v d} : PrincipalRoute p (.inr (v,d)) →
      PrincipalRoute p (p (.inr (v,!d)))

private inductive RouteState {V : Type} (p : Pairing (Bool ⊕ (V × Bool))) :
    Bool ⊕ (V × Bool) → Prop where
  | root : RouteState p (.inl false)
  | arrival {x} : PrincipalRoute p x → RouteState p x
  | departure {v d} : PrincipalRoute p (.inr (v,d)) → RouteState p (.inr (v,!d))

private theorem RouteState.segment (h : RouteState p x) : RouteState p (p x) := by
  cases h with
  | root => exact .arrival .single
  | arrival h =>
    cases h with
    | single => simpa only [Pairing.involutive] using RouteState.root (p:=p)
    | snoc h => simpa only [Pairing.involutive] using RouteState.departure h
  | departure h => exact .arrival (.snoc h)

private theorem RouteState.vertex (h : RouteState p (.inr (v,d))) :
    RouteState p (.inr (v,!d)) := by
  cases h with
  | arrival h => exact .departure h
  | departure h => simpa using RouteState.arrival h

private theorem InternalReach.route_state (h : InternalReach p x y) :
    RouteState p x → RouteState p y := by
  induction h with
  | refl => exact id
  | segment => exact RouteState.segment
  | vertex => exact RouteState.vertex
  | trans h k ih ik => exact fun hx => ik (ih hx)

/-- Connectivity alone supplies the alternating route. No chosen route,
simple-path certificate, bound, or target rewrite property is an input. -/
theorem InternalReach.principal_route
    (h : InternalReach p (.inl false) (.inl true)) : PrincipalRoute p (.inl true) := by
  have state := h.route_state RouteState.root
  cases state with
  | arrival route => exact route

private theorem adjacent_snoc {A : Type} {R : A → A → Prop}
    {es : List A} {e f : A}
    (h : ∀ x y, (x,y) ∈ es.zip es.tail → R x y)
    (last : es.getLast?=some e) (new : R e f) :
    ∀ x y, (x,y) ∈ (es++[f]).zip (es++[f]).tail → R x y := by
  induction es with
  | nil => simp at last
  | cons a es ih =>
    cases es with
    | nil =>
      simp only [List.getLast?_cons,List.getLast?_nil,Option.some.injEq] at last
      subst e
      simpa using new
    | cons b es =>
      intro x y mem
      simp only [List.cons_append,List.tail_cons,List.zip_cons_cons,List.mem_cons] at mem
      rcases mem with eq | mem
      · cases eq
        exact h a b (by simp)
      · exact ih (fun x y hh => h x y (by
          change (x,y) ∈ (a,b)::(b::es).zip es
          exact List.mem_cons_of_mem _ hh)) (by simpa using last) x y mem

theorem PrincipalRoute.realize {V : Type} {p : Pairing (Bool ⊕ (V × Bool))}
    {y : Bool ⊕ (V × Bool)} (h : PrincipalRoute p y) :
    ∃ es : List (Bool ⊕ (V × Bool)), es.head?=some (.inl false) ∧
      es.getLast?=some (p y) ∧
      ∀ e f, (e,f) ∈ es.zip es.tail →
        ∃ v d, p e=.inr (v,d) ∧ f=.inr (v,!d) := by
  induction h with
  | single =>
    refine ⟨[.inl false],rfl,?_,?_⟩
    · simp [Pairing.involutive]
    · simp
  | @snoc v d h ih =>
    obtain ⟨es,start,finish,turns⟩ := ih
    refine ⟨es++[.inr (v,!d)],?_,?_,?_⟩
    · cases es with
      | nil => simp at start
      | cons e es => simpa using start
    · simp [Pairing.involutive]
    · apply adjacent_snoc turns finish
      exact ⟨v,d,p.involutive _,rfl⟩
end Lamping.AG
