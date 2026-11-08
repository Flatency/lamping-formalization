import Lamping.Lamping.LocalCancellation
namespace Lamping.AG
open Graph
/-- Every same-side path at the passive node is exactly one auxiliary-to-auxiliary
passage. Principal crossings necessarily leave on the opposite frontier. -/
theorem LocalPath.passive_same_shape (f h : Op) (i j : Nat) (x y : Aux h)
    (p : LocalPath (leftNet f h i j) (.inr x) (.inr y) a b) :
    p.edges=[.inr (.inl (.inr x)),.inl ⟨.inr (),.inr y⟩] ∧
      Traversal j (.op h) (.inr x) (.inr y) a b := by
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
        cases q with
        | inr z =>
          subst e
          cases es with
          | nil =>
            cases rest
            have pairEq : (Sigma.mk (Sum.inr ()) (Sum.inr z) : NodePort signature (Unit ⊕ Unit) (leftNet f h i j).label)=⟨.inr (),.inr y⟩ := by
              simpa [leftNet] using finish
            have hh : HEq (Sum.inr z : Port (.op h)) (Sum.inr y : Port (.op h)) := sigma_snd_heq pairEq
            have eq := Sum.inr.inj (eq_of_heq hh)
            subst z
            exact ⟨rfl,hfirst⟩
          | cons e es =>
            cases rest with
            | cons third _ => exact False.elim (third.not_boundary (.inr z) rfl)
        | inl u =>
          cases u; subst e
          cases es with
          | nil => simp [leftNet] at finish
          | cons e es =>
            cases rest with
            | cons second tail =>
              obtain ⟨q,hq,hsecond⟩ := second.from_node (.inl ()) (.inl ()) rfl
              cases q with
              | inl u => cases u; exact False.elim (hsecond.distinct rfl)
              | inr z =>
                subst e
                cases es with
                | nil => simp [leftNet] at finish
                | cons e es =>
                  cases tail with
                  | cons third _ => exact False.elim (third.not_boundary (.inl z) rfl)
end Lamping.AG

namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}
theorem ShellRelabel.reverse {x y : B} {i : Nat} {a b : Context}
    (h : ShellRelabel g x y i a b) : ShellRelabel g y x i b a := by
  obtain ⟨a',b',ha,hb,⟨p⟩⟩ := h
  exact ⟨b',a',hb,ha,⟨p.reverse⟩⟩
end
theorem fanAction_passive_same_relabel (f : Op) (i j : Nat) (lt : i<j) (x y : Aux f)
    (path : LocalPath (Schema.fanAction f i j lt).left (.inr x) (.inr y) a b) :
    ShellRelabel (Schema.fanAction f i j lt).right.net (.inr x) (.inr y) i a b := by
  obtain ⟨gap,rfl⟩ : ∃gap,j=i+1+gap := ⟨j-i-1,by omega⟩
  obtain ⟨_,step⟩ := path.passive_same_shape .fan f i (i+1+gap) x y
  cases f
  case app =>
    obtain ⟨orientation,same⟩ := step.aux_aux
    subst b
    have route := fanActionPassiveApp i gap false a Context.empty .empty
    have direct : ShellRelabel (Schema.fanAction .app i (i+1+gap) lt).right.net (.inr false) (.inr true) i a a :=
      ⟨_,_,Context.sameShell_replace a _ i,Context.sameShell_replace a _ i,⟨route⟩⟩
    rcases orientation with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact direct
    · exact direct.reverse
  all_goals exact False.elim step.aux_aux
theorem croAction_passive_same_relabel (f : Op) (i j : Nat) (lt : i<j) (x y : Aux f)
    (path : LocalPath (Schema.croAction f i j lt).left (.inr x) (.inr y) a b) :
    ShellRelabel (Schema.croAction f i j lt).right.net (.inr x) (.inr y) i a b := by
  obtain ⟨gap,rfl⟩ : ∃gap,j=i+1+gap := ⟨j-i-1,by omega⟩
  obtain ⟨_,step⟩ := path.passive_same_shape .cro f i (i+1+gap) x y
  cases f
  case app =>
    obtain ⟨orientation,same⟩ := step.aux_aux
    subst b
    have route := croActionPassiveApp i gap a Context.empty
    have direct : ShellRelabel (Schema.croAction .app i (i+1+gap) lt).right.net (.inr false) (.inr true) i a a :=
      ⟨_,_,Context.sameShell_replace a _ i,Context.sameShell_replace a _ i,⟨route⟩⟩
    rcases orientation with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact direct
    · exact direct.reverse
  all_goals exact False.elim step.aux_aux
theorem braAction_passive_same_relabel (f : Op) (i j : Nat) (lt : i<j) (x y : Aux f)
    (path : LocalPath (Schema.braAction f i j lt).left (.inr x) (.inr y) a b) :
    ShellRelabel (Schema.braAction f i j lt).right.net (.inr x) (.inr y) i a b := by
  obtain ⟨gap,rfl⟩ : ∃gap,j=i+1+gap := ⟨j-i-1,by omega⟩
  obtain ⟨_,step⟩ := path.passive_same_shape .bra f i (i+1+gap) x y
  cases f
  case app =>
    obtain ⟨orientation,same⟩ := step.aux_aux
    subst b
    have route := braActionPassiveApp i gap a Context.empty .empty .empty
    have direct : ShellRelabel (Schema.braAction .app i (i+1+gap) lt).right.net (.inr false) (.inr true) i a a :=
      ⟨_,_,Context.sameShell_replace a _ i,Context.sameShell_replace a _ i,⟨route⟩⟩
    rcases orientation with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact direct
    · exact direct.reverse
  all_goals exact False.elim step.aux_aux
end Lamping.AG
namespace Lamping.AG
/-- Full fan-action frontier coverage, preserving the meaningful low shell and
forgetting the chosen higher labeling. This is a local theorem, not global SND. -/
theorem fanAction_transport (f : Op) (i j : Nat) (lt : i<j)
    (x y : Bool ⊕ Aux f) (p : LocalPath (Schema.fanAction f i j lt).left x y a b) :
    ShellRelabel (Schema.fanAction f i j lt).right.net x y i a b := by
  cases x with
  | inl x =>
    cases y with
    | inl y => exact False.elim (left_control_no_same_side .fan f (Or.inl rfl) i j x y p)
    | inr y =>
      have shape := p.left_control_shape .fan f (Or.inl rfl) i j x y
      exact fanAction_cross_relabel f i j lt x y a b (shape ▸ p.labeling)
  | inr x =>
    cases y with
    | inr y => exact fanAction_passive_same_relabel f i j lt x y p
    | inl y =>
      have rev := p.reverse
      have shape := rev.left_control_shape .fan f (Or.inl rfl) i j y x
      exact (fanAction_cross_relabel f i j lt y x b a (shape ▸ rev.labeling)).reverse
theorem croAction_transport (f : Op) (i j : Nat) (lt : i<j)
    (x y : Unit ⊕ Aux f) (p : LocalPath (Schema.croAction f i j lt).left x y a b) :
    ShellRelabel (Schema.croAction f i j lt).right.net x y i a b := by
  cases x with
  | inl x =>
    cases x; cases y with
    | inl y => exact False.elim (left_control_no_same_side .cro f (Or.inr (Or.inl rfl)) i j () y p)
    | inr y =>
      have shape := p.left_control_shape .cro f (Or.inr (Or.inl rfl)) i j () y
      exact croAction_cross_relabel f i j lt y a b (shape ▸ p.labeling)
  | inr x =>
    cases y with
    | inr y => exact croAction_passive_same_relabel f i j lt x y p
    | inl y =>
      cases y
      have rev := p.reverse
      have shape := rev.left_control_shape .cro f (Or.inr (Or.inl rfl)) i j () x
      exact (croAction_cross_relabel f i j lt x b a (shape ▸ rev.labeling)).reverse
theorem braAction_transport (f : Op) (i j : Nat) (lt : i<j)
    (x y : Unit ⊕ Aux f) (p : LocalPath (Schema.braAction f i j lt).left x y a b) :
    ShellRelabel (Schema.braAction f i j lt).right.net x y i a b := by
  cases x with
  | inl x =>
    cases x; cases y with
    | inl y => exact False.elim (left_control_no_same_side .bra f (Or.inr (Or.inr rfl)) i j () y p)
    | inr y =>
      have shape := p.left_control_shape .bra f (Or.inr (Or.inr rfl)) i j () y
      exact braAction_cross_relabel f i j lt y a b (shape ▸ p.labeling)
  | inr x =>
    cases y with
    | inr y => exact braAction_passive_same_relabel f i j lt x y p
    | inl y =>
      cases y
      have rev := p.reverse
      have shape := rev.left_control_shape .bra f (Or.inr (Or.inr rfl)) i j () x
      exact (braAction_cross_relabel f i j lt x b a (shape ▸ rev.labeling)).reverse
end Lamping.AG
