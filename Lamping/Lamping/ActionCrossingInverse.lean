import Lamping.Lamping.PrimitiveTailTransport
import Lamping.Lamping.PathLabelDeterminism
namespace Lamping.AG
open Graph

theorem fanRight_cross_passages (f : Op) (i j : Nat) (branch : Bool) (q : Aux f) (a b : Context)
    (labels : Labelling (fanRight f i j)
      [.inr (.inl (.inl branch)),.inl ⟨.inl branch,.inr q⟩,.inl ⟨.inr q,.inl ()⟩] a b) :
    ∃ middle,Traversal j (.op f) (.inl ()) (.inr q) a middle ∧
      Traversal i (.op .fan) (.inr branch) (.inl ()) middle b := by
  cases labels with
  | cons first rest =>
    obtain ⟨p,out,rule⟩ := first.from_node (.inl branch) (.inl ()) rfl
    have same : p=.inr q := by
      have ports := sigma_snd_heq (Sum.inl.inj out)
      exact (eq_of_heq ports).symm
    subst p
    cases rest with
    | cons second last =>
      cases last
      obtain ⟨p,out,next⟩ := second.from_node (.inr q) (.inr branch) rfl
      have same : p=.inl () := by
        have ports := sigma_snd_heq (Sum.inl.inj out)
        exact (eq_of_heq ports).symm
      subst p
      exact ⟨_,rule,next⟩

theorem unaryRight_cross_passages (c f : Op) (single : Bij Unit (Aux c)) (i k : Nat)
    (q : Aux f) (a b : Context)
    (labels : Labelling (unaryRightCore c f single i k)
      [.inr (.inl (.inl ())),.inl ⟨.inl (),.inr q⟩,.inl ⟨.inr q,.inl ()⟩] a b) :
    ∃ middle,Traversal k (.op f) (.inl ()) (.inr q) a middle ∧
      Traversal i (.op c) (.inr (single ())) (.inl ()) middle b := by
  cases labels with
  | cons first rest =>
    obtain ⟨p,out,rule⟩ := first.from_node (.inl ()) (.inl ()) rfl
    have same : p=.inr q := by
      have ports := sigma_snd_heq (Sum.inl.inj out)
      exact (eq_of_heq ports).symm
    subst p
    cases rest with
    | cons second last =>
      cases last
      obtain ⟨p,out,next⟩ := second.from_node (.inr q) (.inr (single ())) rfl
      have same : p=.inl () := by
        have ports := sigma_snd_heq (Sum.inl.inj out)
        exact (eq_of_heq ports).symm
      subst p
      exact ⟨_,rule,next⟩

/-- RHS to source preserves the actual given contexts, rather than choosing
new labels with merely equal low shells. -/
theorem fanAction_cross_inverse (f : Op) (i j : Nat) (lt : i<j) (branch : Bool)
    (q : Aux f) (a b : Context)
    (labels : Labelling (fanRight f i j)
      [.inr (.inl (.inl branch)),.inl ⟨.inl branch,.inr q⟩,.inl ⟨.inr q,.inl ()⟩] a b) :
    Labelling (leftNet .fan f i j) (leftRoute .fan f i j branch q) a b := by
  obtain ⟨middle,passive,active⟩ := fanRight_cross_passages f i j branch q a b labels
  have initial := InitialOffsets.Event.apply_rel (.fan i branch) a
  have final := InitialOffsets.Event.apply_rel (.fan i branch) middle
  have same : b=InitialOffsets.fanAt i branch middle := active.output_unique (.direct final)
  have crossed := passive.fan_below i lt branch
  rw [same]
  exact (leftRoutePath .fan f i j branch q _ _ _ (.direct initial) crossed).labeling

theorem croAction_cross_inverse (f : Op) (i j : Nat) (lt : i<j) (q : Aux f) (a b : Context)
    (labels : Labelling (unaryRightCore .cro f (Bij.refl _) i (j-1))
      [.inr (.inl (.inl ())),.inl ⟨.inl (),.inr q⟩,.inl ⟨.inr q,.inl ()⟩] a b) :
    Labelling (leftNet .cro f i j) (leftRoute .cro f i j () q) a b := by
  obtain ⟨middle,passive,active⟩ := unaryRight_cross_passages .cro f (Bij.refl _) i (j-1) q a b labels
  have initial := InitialOffsets.Event.apply_rel (.cro i) a
  have final := InitialOffsets.Event.apply_rel (.cro i) middle
  have same : b=InitialOffsets.croAt i middle := active.output_unique (.direct final)
  have crossed := passive.cro_below i (by omega)
  have indexEq : j-1+1=j := by omega
  rw [indexEq] at crossed
  rw [same]
  exact (leftRoutePath .cro f i j () q _ _ _ (.direct initial) crossed).labeling

theorem braAction_cross_inverse (f : Op) (i j : Nat) (lt : i<j) (q : Aux f) (a b : Context)
    (labels : Labelling (unaryRightCore .bra f (Bij.refl _) i (j+1))
      [.inr (.inl (.inl ())),.inl ⟨.inl (),.inr q⟩,.inl ⟨.inr q,.inl ()⟩] a b) :
    Labelling (leftNet .bra f i j) (leftRoute .bra f i j () q) a b := by
  obtain ⟨middle,passive,active⟩ := unaryRight_cross_passages .bra f (Bij.refl _) i (j+1) q a b labels
  have initial := InitialOffsets.Event.apply_rel (.bra i) a
  have final := InitialOffsets.Event.apply_rel (.bra i) middle
  have same : b=InitialOffsets.braAt i middle := active.output_unique (.direct final)
  have crossed := passive.bra_below i (by omega)
  have indexEq : j+1-1=j := by omega
  rw [indexEq] at crossed
  rw [same]
  exact (leftRoutePath .bra f i j () q _ _ _ (.direct initial) crossed).labeling
end Lamping.AG

