import Lamping.Lamping.LocalTransport
namespace Lamping.AG
open Graph

private theorem control_output {f : Op} {i p q a b}
    (control : f=.fan ∨f=.cro ∨f=.bra)
    (rule : Traversal i (.op f) (.inr p) q a b) : q=.inl () := by
  rcases control with same |same |same <;> subst f <;> exact rule.control_aux

/-- Arbitrary complete active-entry paths in the actual two-node LHS have
the literal principal-crossing shape. -/
theorem left_active_path_shape (f h : Op) (control : f=.fan ∨f=.cro ∨f=.bra)
    (i j : Nat) (p : Aux f) (exit : Aux f⊕Aux h)
    (es : List (Endpoint (leftNet f h i j))) (a b : Context)
    (labels : Labelling (leftNet f h i j) es a b)
    (start : es.head?=some (.inr (.inl (.inl p))))
    (finish : es.getLast?=some ((leftNet f h i j).wire (.inr (.inl exit)))) :
    ∃ q,exit=.inr q ∧es=leftRoute f h i j p q := by
  obtain ⟨tail,split⟩ := List.head?_eq_some_iff.mp start
  subst es
  cases tail with
  | nil => cases exit <;> cases finish
  | cons e tail =>
    cases labels with
    | cons first rest =>
      obtain ⟨port,out,rule⟩ := first.from_node (.inl ()) (.inr p) rfl
      have principal : port=.inl () := control_output control rule
      subst port
      subst e
      cases tail with
      | nil => cases exit <;> cases finish
      | cons e tail =>
        cases rest with
        | cons second after =>
          obtain ⟨port,out,rule⟩ := second.from_node (.inr ()) (.inl ()) rfl
          cases port with
          | inl u => cases u; exact False.elim (rule.distinct rfl)
          | inr q =>
            subst e
            cases tail with
            | nil =>
              have ends := congrArg (leftNet f h i j).wire.mate (Option.some.inj finish)
              rw [Pairing.involutive] at ends
              have same : exit=.inr q := (Sum.inl.inj (Sum.inr.inj ends)).symm
              exact ⟨q,same,rfl⟩
            | cons e tail =>
              cases after with
              | cons turn _ => exact False.elim (turn.not_boundary (.inr q) rfl)

/-- Passive-entry LHS paths either cross the principal pair in reverse, or
make the one actual passive auxiliary-to-auxiliary turn. -/
theorem left_passive_path_shape (f h : Op) (i j : Nat) (p : Aux h) (exit : Aux f⊕Aux h)
    (es : List (Endpoint (leftNet f h i j))) (a b : Context)
    (labels : Labelling (leftNet f h i j) es a b)
    (start : es.head?=some (.inr (.inl (.inr p))))
    (finish : es.getLast?=some ((leftNet f h i j).wire (.inr (.inl exit)))) :
    (∃ q,exit=.inl q ∧es=[.inr (.inl (.inr p)),.inl ⟨.inr (),.inl ()⟩,.inl ⟨.inl (),.inr q⟩]) ∨
    (∃ q,exit=.inr q ∧es=[.inr (.inl (.inr p)),.inl ⟨.inr (),.inr q⟩]) := by
  obtain ⟨tail,split⟩ := List.head?_eq_some_iff.mp start
  subst es
  cases tail with
  | nil => cases exit <;> cases finish
  | cons e tail =>
    cases labels with
    | cons first rest =>
      obtain ⟨port,out,rule⟩ := first.from_node (.inr ()) (.inr p) rfl
      cases port with
      | inr q =>
        subst e
        cases tail with
        | nil =>
          have ends := congrArg (leftNet f h i j).wire.mate (Option.some.inj finish)
          rw [Pairing.involutive] at ends
          have same : exit=.inr q := (Sum.inl.inj (Sum.inr.inj ends)).symm
          exact Or.inr ⟨q,same,rfl⟩
        | cons e tail =>
          cases rest with
          | cons turn _ => exact False.elim (turn.not_boundary (.inr q) rfl)
      | inl u =>
        cases u
        subst e
        cases tail with
        | nil => cases exit <;> cases finish
        | cons e tail =>
          cases rest with
          | cons second after =>
            obtain ⟨port,out,rule⟩ := second.from_node (.inl ()) (.inl ()) rfl
            cases port with
            | inl u => cases u; exact False.elim (rule.distinct rfl)
            | inr q =>
              subst e
              cases tail with
              | nil =>
                have ends := congrArg (leftNet f h i j).wire.mate (Option.some.inj finish)
                rw [Pairing.involutive] at ends
                have same : exit=.inl q := (Sum.inl.inj (Sum.inr.inj ends)).symm
                exact Or.inl ⟨q,same,rfl⟩
              | cons e tail =>
                cases after with
                | cons turn _ => exact False.elim (turn.not_boundary (.inl q) rfl)
end Lamping.AG
