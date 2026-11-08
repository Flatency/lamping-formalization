import Lamping.Lamping.LocalTransport
namespace Lamping.AG
open Graph

/-- Arbitrary actual labelled paths entering the fan-action RHS at an active
frontier have exactly the two printed node passages. Incidence and genuine
control turns force this; no simplicity or length assumption is supplied. -/
theorem fanRight_active_path_shape (f : Op) (i j : Nat) (branch : Bool)
    (exit : Bool⊕Aux f) (es : List (Endpoint (fanRight f i j))) (a b : Context)
    (labels : Labelling (fanRight f i j) es a b)
    (start : es.head?=some (.inr (.inl (.inl branch))))
    (finish : es.getLast?=some ((fanRight f i j).wire (.inr (.inl exit)))) :
    ∃ q,exit=.inr q ∧es=[.inr (.inl (.inl branch)),.inl ⟨.inl branch,.inr q⟩,
      .inl ⟨.inr q,.inl ()⟩] := by
  obtain ⟨tail,split⟩ := List.head?_eq_some_iff.mp start
  subst es
  cases tail with
  | nil => cases exit <;> cases finish
  | cons e tail =>
    cases labels with
    | cons first rest =>
      obtain ⟨q,out,rule⟩ := first.from_node (.inl branch) (.inl ()) rfl
      cases q with
      | inl u => cases u; exact False.elim (rule.distinct rfl)
      | inr q =>
        subst e
        cases tail with
        | nil => cases exit <;> cases finish
        | cons e tail =>
          cases rest with
          | cons second after =>
            obtain ⟨p,out,rule⟩ := second.from_node (.inr q) (.inr branch) rfl
            have principal : p=.inl () := rule.control_aux
            subst p
            subst e
            cases tail with
            | nil =>
              have ends := congrArg (fanRight f i j).wire.mate (Option.some.inj finish)
              rw [Pairing.involutive] at ends
              have same : exit=.inr q := (Sum.inl.inj (Sum.inr.inj ends)).symm
              subst exit
              exact ⟨q,rfl,rfl⟩
            | cons e tail =>
              cases after with
              | cons turn _ => exact False.elim (turn.not_boundary (.inr q) rfl)
/-- A passive frontier can leave through a copied principal port, or cross a
genuine auxiliary-to-auxiliary turn of the copied operator. In either case
the actual complete path is finite with exactly the displayed occurrences. -/
theorem fanRight_passive_path_shape (f : Op) (i j : Nat) (q : Aux f)
    (exit : Bool⊕Aux f) (es : List (Endpoint (fanRight f i j))) (a b : Context)
    (labels : Labelling (fanRight f i j) es a b)
    (start : es.head?=some (.inr (.inl (.inr q))))
    (finish : es.getLast?=some ((fanRight f i j).wire (.inr (.inl exit)))) :
    (∃ branch,exit=.inl branch ∧es=[.inr (.inl (.inr q)),.inl ⟨.inr q,.inr branch⟩,
      .inl ⟨.inl branch,.inl ()⟩]) ∨
    (∃ branch r,exit=.inr r ∧es=[.inr (.inl (.inr q)),.inl ⟨.inr q,.inr branch⟩,
      .inl ⟨.inl branch,.inr r⟩,.inl ⟨.inr r,.inl ()⟩]) := by
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
      | inr branch =>
        subst e
        cases tail with
        | nil => cases exit <;> cases finish
        | cons e tail =>
          cases rest with
          | cons second after =>
            obtain ⟨p,out,rule⟩ := second.from_node (.inl branch) (.inr q) rfl
            cases p with
            | inl u =>
              cases u
              subst e
              cases tail with
              | nil =>
                have ends := congrArg (fanRight f i j).wire.mate (Option.some.inj finish)
                rw [Pairing.involutive] at ends
                have same : exit=.inl branch := (Sum.inl.inj (Sum.inr.inj ends)).symm
                exact Or.inl ⟨branch,same,rfl⟩
              | cons e tail =>
                cases after with
                | cons turn _ => exact False.elim (turn.not_boundary (.inl branch) rfl)
            | inr r =>
              subst e
              cases tail with
              | nil => cases exit <;> cases finish
              | cons e tail =>
                cases after with
                | cons third after =>
                  obtain ⟨p,out,rule⟩ := third.from_node (.inr r) (.inr branch) rfl
                  have principal : p=.inl () := rule.control_aux
                  subst p
                  subst e
                  cases tail with
                  | nil =>
                    have ends := congrArg (fanRight f i j).wire.mate (Option.some.inj finish)
                    rw [Pairing.involutive] at ends
                    have same : exit=.inr r := (Sum.inl.inj (Sum.inr.inj ends)).symm
                    exact Or.inr ⟨branch,r,same,rfl⟩
                  | cons e tail =>
                    cases after with
                    | cons turn _ => exact False.elim (turn.not_boundary (.inr r) rfl)
end Lamping.AG
