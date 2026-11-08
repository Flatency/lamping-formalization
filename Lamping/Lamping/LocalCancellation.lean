import Lamping.Lamping.LocalTransport
namespace Lamping.AG
open Graph

/-- A control pair cannot carry a proper path back out of its entrance side.
The proof uses actual incidence and the prohibition of boundary turns, so it
does not assume paths are simple or of bounded length. -/
theorem left_control_no_same_side (f h : Op)
    (control : f=.fan ∨ f=.cro ∨ f=.bra) (i j : Nat)
    (x y : Aux f) (p : LocalPath (leftNet f h i j) (.inl x) (.inl y) a b) : False := by
  rcases p with ⟨es,start,finish,labels⟩
  cases es with
  | nil => simp at start
  | cons e es =>
    simp only [List.head?_cons,Option.some.injEq] at start
    subst e
    cases es with
    | nil => simp [leftNet] at finish
    | cons e es =>
      cases labels with
      | cons first rest =>
        obtain ⟨q,hq,hfirst⟩ := first.from_node (.inl ()) (.inr x) rfl
        have principal : q=Sum.inl () := by
          rcases control with eq | eq | eq
          · subst f; exact hfirst.control_aux
          · subst f; exact hfirst.control_aux
          · subst f; exact hfirst.control_aux
        subst q; subst e
        cases es with
        | nil => simp [leftNet] at finish
        | cons e es =>
          cases rest with
          | cons second tail =>
            obtain ⟨q,hq,hsecond⟩ := second.from_node (.inr ()) (.inl ()) rfl
            cases q with
            | inl u => cases u; exact hsecond.distinct rfl
            | inr z =>
              subst e
              cases es with
              | nil => simp [leftNet] at finish
              | cons e es =>
                cases tail with
                | cons third _ => exact third.not_boundary (.inr z) rfl

theorem right_control_no_same_side (f h : Op)
    (control : h=.fan ∨ h=.cro ∨ h=.bra) (i j : Nat)
    (x y : Aux h) (p : LocalPath (leftNet f h i j) (.inr x) (.inr y) a b) : False := by
  rcases p with ⟨es,start,finish,labels⟩
  cases es with
  | nil => simp at start
  | cons e es =>
    simp only [List.head?_cons,Option.some.injEq] at start
    subst e
    cases es with
    | nil => simp [leftNet] at finish
    | cons e es =>
      cases labels with
      | cons first rest =>
        obtain ⟨q,hq,hfirst⟩ := first.from_node (.inr ()) (.inr x) rfl
        have principal : q=Sum.inl () := by
          rcases control with eq | eq | eq
          · subst h; exact hfirst.control_aux
          · subst h; exact hfirst.control_aux
          · subst h; exact hfirst.control_aux
        subst q; subst e
        cases es with
        | nil => simp [leftNet] at finish
        | cons e es =>
          cases rest with
          | cons second tail =>
            obtain ⟨q,hq,hsecond⟩ := second.from_node (.inl ()) (.inl ()) rfl
            cases q with
            | inl u => cases u; exact hsecond.distinct rfl
            | inr z =>
              subst e
              cases es with
              | nil => simp [leftNet] at finish
              | cons e es =>
                cases tail with
                | cons third _ => exact third.not_boundary (.inl z) rfl

theorem LocalPath.left_control_shape (f h : Op)
    (control : f=.fan ∨ f=.cro ∨ f=.bra) (i j : Nat)
    (x : Aux f) (y : Aux h)
    (p : LocalPath (leftNet f h i j) (.inl x) (.inr y) a b) :
    p.edges=leftRoute f h i j x y := by
  rcases p with ⟨es,start,finish,labels⟩
  cases es with
  | nil => simp at start
  | cons e es =>
    simp only [List.head?_cons,Option.some.injEq] at start
    subst e
    exact left_control_route_shape f h control i j x y es a b labels finish

/-- Full frontier transport for fan cancellation, including reverse crossings
and excluding all same-side paths. No particular route is assumed. -/
theorem fanCancel_transport (i : Nat) (x y : Bool ⊕ Bool)
    (p : LocalPath (Schema.fanCancel i).left x y a b) :
    Nonempty (LocalPath (Schema.fanCancel i).right.net x y a b) := by
  cases x with
  | inl x =>
    cases y with
    | inl y => exact False.elim (left_control_no_same_side .fan .fan (Or.inl rfl) i i x y p)
    | inr y =>
      have shape := p.left_control_shape .fan .fan (Or.inl rfl) i i x y
      exact fanCancel_route_transport i x y a b (shape ▸ p.labeling)
  | inr x =>
    cases y with
    | inr y => exact False.elim (right_control_no_same_side .fan .fan (Or.inl rfl) i i x y p)
    | inl y =>
      have rev := p.reverse
      have shape := rev.left_control_shape .fan .fan (Or.inl rfl) i i y x
      obtain ⟨q⟩ := fanCancel_route_transport i y x b a (shape ▸ rev.labeling)
      exact ⟨q.reverse⟩

theorem croCancel_transport (i : Nat) (x y : Unit ⊕ Unit)
    (p : LocalPath (Schema.croCancel i).left x y a b) :
    Nonempty (LocalPath (Schema.croCancel i).right.net x y a b) := by
  cases x with
  | inl x =>
    cases x; cases y with
    | inl y => exact False.elim (left_control_no_same_side .cro .cro (Or.inr (Or.inl rfl)) i i () y p)
    | inr y =>
      cases y
      have shape := p.left_control_shape .cro .cro (Or.inr (Or.inl rfl)) i i () ()
      exact croCancel_route_transport i a b (shape ▸ p.labeling)
  | inr x =>
    cases x; cases y with
    | inr y => exact False.elim (right_control_no_same_side .cro .cro (Or.inr (Or.inl rfl)) i i () y p)
    | inl y =>
      cases y
      have rev := p.reverse
      have shape := rev.left_control_shape .cro .cro (Or.inr (Or.inl rfl)) i i () ()
      obtain ⟨q⟩ := croCancel_route_transport i b a (shape ▸ rev.labeling)
      exact ⟨q.reverse⟩

theorem braCancel_transport (i : Nat) (x y : Unit ⊕ Unit)
    (p : LocalPath (Schema.braCancel i).left x y a b) :
    Nonempty (LocalPath (Schema.braCancel i).right.net x y a b) := by
  cases x with
  | inl x =>
    cases x; cases y with
    | inl y => exact False.elim (left_control_no_same_side .bra .bra (Or.inr (Or.inr rfl)) i i () y p)
    | inr y =>
      cases y
      have shape := p.left_control_shape .bra .bra (Or.inr (Or.inr rfl)) i i () ()
      exact braCancel_route_transport i a b (shape ▸ p.labeling)
  | inr x =>
    cases x; cases y with
    | inr y => exact False.elim (right_control_no_same_side .bra .bra (Or.inr (Or.inr rfl)) i i () y p)
    | inl y =>
      cases y
      have rev := p.reverse
      have shape := rev.left_control_shape .bra .bra (Or.inr (Or.inr rfl)) i i () ()
      obtain ⟨q⟩ := braCancel_route_transport i b a (shape ▸ rev.labeling)
      exact ⟨q.reverse⟩
end Lamping.AG

