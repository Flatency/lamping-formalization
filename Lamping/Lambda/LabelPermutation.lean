import Lamping.Lambda.LabelDevelopments
import Lamping.Lambda.LabelResiduals
namespace Lamping.Lambda.Labelled

/-- Exact schedule splitting, including empty prefixes. -/
theorem History.split (h : History (ps++qs) t u) :
    ∃ v, History ps t v ∧ History qs v u := by
  induction ps generalizing t with
  | nil => exact ⟨t,.nil _,h⟩
  | cons p ps ih =>
    cases h with
    | cons step tail =>
      obtain ⟨v,firstPart,suffix⟩ := ih tail
      exact ⟨v,.cons step firstPart,suffix⟩

theorem ParallelStep.labelled_unique (h k : ParallelStep F m n)
    (source : t.erase=m) (left : History h.derivation.paths t u)
    (right : History k.derivation.paths t v) : u=v := by
  have hh := (Marked.completeOld_iff F m).mp h.complete
  have hk := (Marked.completeOld_iff F m).mp k.complete
  exact DevelopmentEval.complete_unique hh.1 hh.2 hk.1 hk.2
    ((Marked.erase_mark F m).trans source.symm) left right

/-- The union complete-development theorem applies to the exact two schedules
of every real residual square, not just to some join of its endpoints. -/
theorem ParallelMovesSquare.labelled_unique (square : ParallelMovesSquare F G m a b c)
    (source : t.erase=m)
    (left : History (square.first.derivation.append square.afterFirst.derivation).paths t u)
    (right : History (square.second.derivation.append square.afterSecond.derivation).paths t v) : u=v := by
  have lh := square.first.composite_relative_union square.afterFirst
  have rh := square.second.composite_relative_union square.afterSecond
  rw [← marked_union_comm F G m] at rh
  exact DevelopmentEval.complete_unique lh (Marked.normal_dev _) rh (Marked.normal_dev _)
    ((Marked.erase_mark (F++G) m).trans source.symm) left right

/-- AG5.3.35(i), forward half: generated permutation equivalence preserves the
entire transported labelled endpoint for arbitrary common initial labellings. -/
theorem PermEq.labelled_unique {rho sigma : ParallelHistory m n} (perm : PermEq rho sigma)
    (source : t.erase=m) (left : History rho.derivation.paths t u)
    (right : History sigma.derivation.paths t v) : u=v := by
  induction perm generalizing t u v with
  | refl => exact left.deterministic right
  | symm _ ih => exact (ih source right left).symm
  | @trans m n h k l _ _ ih ik =>
    obtain ⟨middle,hmiddle,he⟩ := lift_history k.derivation.valid t source
    exact (ih source left hmiddle).trans (ik source hmiddle right)
  | @comp m n o h k h' k' _ _ ih ik =>
    rw [ParallelHistory.derivation_append] at left right
    obtain ⟨a,la,lb⟩ := left.split
    obtain ⟨b,ra,rb⟩ := right.split
    have eq := ih source la ra
    cases eq
    have target : a.erase=o := by
      obtain ⟨other,ho,he⟩ := lift_history h.derivation.valid t source
      have same := la.deterministic ho
      cases same; exact he
    exact ik target lb rb
  | development h k =>
    simp only [ParallelHistory.single_derivation] at left right
    exact ParallelStep.labelled_unique h k source left right
  | moves square =>
    simp only [ParallelHistory.derivation_append,ParallelHistory.single_derivation] at left right
    exact ParallelMovesSquare.labelled_unique square source left right
  | empty h =>
    simp only [ParallelHistory.single_derivation] at left
    have nilHistory : History (ParallelStep.empty m).derivation.paths t t := .nil _
    have eq := ParallelStep.labelled_unique h (ParallelStep.empty _) source left nilHistory
    cases right
    exact eq

/-- A Copy comparison uses its actual extension, exact permutation witness,
and genuine old-name residual. No equality of endpoints defines Copy. -/
theorem Copy.degreeAlong {a b : RedexWithHistory m} (copy : Copy a b)
    (t : LTerm) (source : t.erase=m) :
    degreeAlong t a.history.derivation.paths a.redex.val=
      degreeAlong t b.history.derivation.paths b.redex.val := by
  obtain ⟨extension,permutation,residual⟩ := copy
  obtain ⟨u,hu,ue⟩ := lift_history a.history.derivation.valid t source
  obtain ⟨v,hv,ve⟩ := lift_history extension.derivation.valid u ue
  obtain ⟨w,hw,we⟩ := lift_history b.history.derivation.valid t source
  have combined := hu.append hv
  have equivalent := PermEq.labelled_unique permutation source
    (by simpa only [ParallelHistory.derivation_append] using combined) hw
  cases equivalent
  have degree := Derivation.residual_degree extension.derivation u v ue hv a.redex b.redex residual
  rw [degreeAlong_witness hu,degreeAlong_witness hw]
  exact degree.symm

/-- AG5.3.41, with its original stronger arbitrary-labelling hypothesis. -/
theorem FamilyEq.degreeAlong {a b : RedexWithHistory m} (family : FamilyEq a b)
    (t : LTerm) (source : t.erase=m) :
    degreeAlong t a.history.derivation.paths a.redex.val=
      degreeAlong t b.history.derivation.paths b.redex.val := by
  induction family with
  | copy h => exact Copy.degreeAlong h t source
  | symm _ ih => exact ih.symm
  | trans _ _ ih ik => exact ih.trans ik
end Lamping.Lambda.Labelled

