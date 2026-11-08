import Lamping.Lamping.ActionPathShapes
namespace Lamping.AG
open Graph

private theorem control_aux_output {c : Op} {i p q a b}
    (control : c=.fan ∨c=.cro ∨c=.bra)
    (rule : Traversal i (.op c) (.inr p) q a b) : q=.inl () := by
  rcases control with same |same |same <;> subst c <;> exact rule.control_aux

private theorem unary_aux_unique {c : Op} (single : Bij Unit (Aux c)) (p : Aux c) : p=single () := by
  have same := single.right_inv p
  cases single.invFun p
  exact same.symm

/-- The real unary-action RHS admits no additional internal detours from its
active frontier, for either unary control and any passive operator. -/
theorem unaryRight_active_path_shape (c f : Op) (single : Bij Unit (Aux c))
    (control : c=.fan ∨c=.cro ∨c=.bra) (i j : Nat)
    (exit : Unit⊕Aux f) (es : List (Endpoint (unaryRightCore c f single i j))) (a b : Context)
    (labels : Labelling (unaryRightCore c f single i j) es a b)
    (start : es.head?=some (.inr (.inl (.inl ()))))
    (finish : es.getLast?=some ((unaryRightCore c f single i j).wire (.inr (.inl exit)))) :
    ∃ q,exit=.inr q ∧es=[.inr (.inl (.inl ())),.inl ⟨.inl (),.inr q⟩,
      .inl ⟨.inr q,.inl ()⟩] := by
  obtain ⟨tail,split⟩ := List.head?_eq_some_iff.mp start
  subst es
  cases tail with
  | nil => cases exit <;> cases finish
  | cons e tail =>
    cases labels with
    | cons first rest =>
      obtain ⟨q,out,rule⟩ := first.from_node (.inl ()) (.inl ()) rfl
      cases q with
      | inl u => cases u; exact False.elim (rule.distinct rfl)
      | inr q =>
        subst e
        cases tail with
        | nil => cases exit <;> cases finish
        | cons e tail =>
          cases rest with
          | cons second after =>
            obtain ⟨p,out,rule⟩ := second.from_node (.inr q) (.inr (single ())) rfl
            have principal : p=.inl () := control_aux_output control rule
            subst p
            subst e
            cases tail with
            | nil =>
              have ends := congrArg (unaryRightCore c f single i j).wire.mate (Option.some.inj finish)
              rw [Pairing.involutive] at ends
              have same : exit=.inr q := (Sum.inl.inj (Sum.inr.inj ends)).symm
              subst exit
              exact ⟨q,rfl,rfl⟩
            | cons e tail =>
              cases after with
              | cons turn _ => exact False.elim (turn.not_boundary (.inr q) rfl)

/-- Complete passive-entry unary RHS paths are exactly a reverse crossing or
a three-node crossing of two passive auxiliary positions. -/
theorem unaryRight_passive_path_shape (c f : Op) (single : Bij Unit (Aux c))
    (control : c=.fan ∨c=.cro ∨c=.bra) (i j : Nat) (q : Aux f)
    (exit : Unit⊕Aux f) (es : List (Endpoint (unaryRightCore c f single i j))) (a b : Context)
    (labels : Labelling (unaryRightCore c f single i j) es a b)
    (start : es.head?=some (.inr (.inl (.inr q))))
    (finish : es.getLast?=some ((unaryRightCore c f single i j).wire (.inr (.inl exit)))) :
    (exit=.inl () ∧es=[.inr (.inl (.inr q)),.inl ⟨.inr q,.inr (single ())⟩,
      .inl ⟨.inl (),.inl ()⟩]) ∨
    (∃ r,exit=.inr r ∧es=[.inr (.inl (.inr q)),.inl ⟨.inr q,.inr (single ())⟩,
      .inl ⟨.inl (),.inr r⟩,.inl ⟨.inr r,.inl ()⟩]) := by
  obtain ⟨tail,split⟩ := List.head?_eq_some_iff.mp start
  subst es
  cases tail with
  | nil => cases exit <;> cases finish
  | cons e tail =>
    cases labels with
    | cons first rest =>
      obtain ⟨p,out,rule⟩ := first.from_node (.inr q) (.inl ()) rfl
      cases p with
      | inl u => cases u; exact False.elim (rule.distinct rfl)
      | inr port =>
        have same := unary_aux_unique single port
        subst port
        subst e
        cases tail with
        | nil => cases exit <;> cases finish
        | cons e tail =>
          cases rest with
          | cons second after =>
            obtain ⟨p,out,rule⟩ := second.from_node (.inl ()) (.inr q) rfl
            cases p with
            | inl u =>
              cases u
              subst e
              cases tail with
              | nil =>
                have ends := congrArg (unaryRightCore c f single i j).wire.mate (Option.some.inj finish)
                rw [Pairing.involutive] at ends
                have same : exit=.inl () := (Sum.inl.inj (Sum.inr.inj ends)).symm
                exact Or.inl ⟨same,rfl⟩
              | cons e tail =>
                cases after with
                | cons turn _ => exact False.elim (turn.not_boundary (.inl ()) rfl)
            | inr r =>
              subst e
              cases tail with
              | nil => cases exit <;> cases finish
              | cons e tail =>
                cases after with
                | cons third after =>
                  obtain ⟨p,out,rule⟩ := third.from_node (.inr r) (.inr (single ())) rfl
                  have principal : p=.inl () := control_aux_output control rule
                  subst p
                  subst e
                  cases tail with
                  | nil =>
                    have ends := congrArg (unaryRightCore c f single i j).wire.mate (Option.some.inj finish)
                    rw [Pairing.involutive] at ends
                    have same : exit=.inr r := (Sum.inl.inj (Sum.inr.inj ends)).symm
                    exact Or.inr ⟨r,same,rfl⟩
                  | cons e tail =>
                    cases after with
                    | cons turn _ => exact False.elim (turn.not_boundary (.inr r) rfl)
end Lamping.AG
