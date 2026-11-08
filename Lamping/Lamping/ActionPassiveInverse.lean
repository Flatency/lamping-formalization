import Lamping.Lamping.ActionCrossingInverse
namespace Lamping.AG
open Graph

theorem Traversal.auxiliary_context {f : Op} {index : Nat} {p q : Aux f} {a b : Context}
    (rule : Traversal index (.op f) (.inr p) (.inr q) a b) : a=b := by
  cases f with
  | app => exact rule.aux_aux.2
  | lam => exact False.elim rule.aux_aux
  | fan => exact False.elim rule.aux_aux
  | cro => exact False.elim rule.aux_aux
  | bra => exact False.elim rule.aux_aux

/-- A genuine auxiliary-to-auxiliary turn is the application's identity turn
and can therefore be replayed at any index and any supplied context. -/
theorem Traversal.auxiliary_replay {f : Op} {index : Nat} {p q : Aux f} {a b : Context}
    (rule : Traversal index (.op f) (.inr p) (.inr q) a b) (newIndex : Nat) (c : Context) :
    Traversal newIndex (.op f) (.inr p) (.inr q) c c := by
  cases f with
  | app =>
    rcases rule.aux_aux.1 with ⟨rfl,rfl⟩ |⟨rfl,rfl⟩
    · exact .direct (.appArg c)
    · exact .inverse (.appArg c)
  | lam => exact False.elim rule.aux_aux
  | fan => exact False.elim rule.aux_aux
  | cro => exact False.elim rule.aux_aux
  | bra => exact False.elim rule.aux_aux

private theorem source_aux_path (active f : Op) (i j : Nat) (p q : Aux f) (a b : Context)
    (turn : Traversal j (.op f) (.inr p) (.inr q) a b) :
    Labelling (leftNet active f i j) [.inr (.inl (.inr p)),.inl ⟨.inr (),.inr q⟩] a b :=
  .cons (LabelledTurn.node (g:=leftNet active f i j) (.inr ()) _ _ turn) (.single _ _)

theorem fanAction_passive_inverse (f : Op) (i j : Nat) (branch : Bool) (p q : Aux f) (a b : Context)
    (labels : Labelling (fanRight f i j)
      [.inr (.inl (.inr p)),.inl ⟨.inr p,.inr branch⟩,
        .inl ⟨.inl branch,.inr q⟩,.inl ⟨.inr q,.inl ()⟩] a b) :
    Labelling (leftNet .fan f i j) [.inr (.inl (.inr p)),.inl ⟨.inr (),.inr q⟩] a b := by
  cases labels with
  | cons first rest =>
    obtain ⟨port,out,firstRule⟩ := first.from_node (.inr p) (.inl ()) rfl
    have same : port=.inr branch := by
      have ports := sigma_snd_heq (Sum.inl.inj out)
      exact (eq_of_heq ports).symm
    subst port
    cases rest with
    | cons second rest =>
      obtain ⟨port,out,middleRule⟩ := second.from_node (.inl branch) (.inr p) rfl
      have same : port=.inr q := by
        have ports := sigma_snd_heq (Sum.inl.inj out)
        exact (eq_of_heq ports).symm
      subst port
      cases rest with
      | cons third last =>
        cases last
        obtain ⟨port,out,lastRule⟩ := third.from_node (.inr q) (.inr branch) rfl
        have same : port=.inl () := by
          have ports := sigma_snd_heq (Sum.inl.inj out)
          exact (eq_of_heq ports).symm
        subst port
        have middleEq := middleRule.auxiliary_context
        rw [←middleEq] at lastRule
        have endpoints := firstRule.reverse.output_unique lastRule
        rw [←endpoints]
        exact source_aux_path .fan f i j p q a a (middleRule.auxiliary_replay j a)

theorem unaryAction_passive_inverse (c f : Op) (single : Bij Unit (Aux c)) (i k j : Nat)
    (p q : Aux f) (a b : Context)
    (labels : Labelling (unaryRightCore c f single i k)
      [.inr (.inl (.inr p)),.inl ⟨.inr p,.inr (single ())⟩,
        .inl ⟨.inl (),.inr q⟩,.inl ⟨.inr q,.inl ()⟩] a b) :
    Labelling (leftNet c f i j) [.inr (.inl (.inr p)),.inl ⟨.inr (),.inr q⟩] a b := by
  cases labels with
  | cons first rest =>
    obtain ⟨port,out,firstRule⟩ := first.from_node (.inr p) (.inl ()) rfl
    have same : port=.inr (single ()) := by
      have ports := sigma_snd_heq (Sum.inl.inj out)
      exact (eq_of_heq ports).symm
    subst port
    cases rest with
    | cons second rest =>
      obtain ⟨port,out,middleRule⟩ := second.from_node (.inl ()) (.inr p) rfl
      have same : port=.inr q := by
        have ports := sigma_snd_heq (Sum.inl.inj out)
        exact (eq_of_heq ports).symm
      subst port
      cases rest with
      | cons third last =>
        cases last
        obtain ⟨port,out,lastRule⟩ := third.from_node (.inr q) (.inr (single ())) rfl
        have same : port=.inl () := by
          have ports := sigma_snd_heq (Sum.inl.inj out)
          exact (eq_of_heq ports).symm
        subst port
        have middleEq := middleRule.auxiliary_context
        rw [←middleEq] at lastRule
        have endpoints := firstRule.reverse.output_unique lastRule
        rw [←endpoints]
        exact source_aux_path c f i j p q a a (middleRule.auxiliary_replay j a)
end Lamping.AG

