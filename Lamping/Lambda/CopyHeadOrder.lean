import Lamping.Lambda.CopyInitialExtraction
import Lamping.Lambda.StandardizationNoReturn
namespace Lamping.Lambda
private theorem head_no_return (head : BetaAt t p u) (tail : ParallelHistory u v)
    (standard : Standard (.cons (singleContraction head) tail)) :
    DoesNotReturnLeft ⟨p,head.redex⟩ (.cons (singleContraction head) tail) := by
  cases standard with
  | cons _ witness lo noReturn rest =>
    have same : witness=⟨p,head.redex⟩ := Subtype.ext (List.mem_singleton.mp lo.1)
    subst witness
    exact noReturn
/-- A real first contraction in the source prefix has no old residual after
any Copy extension or generated permutation to the target prefix. -/
theorem Copy.source_head_deleted {a b : RedexWithHistory m} (copy : Copy a b) (head : BetaAt m p t)
    (tail : ParallelHistory t a.target) (source : a.history=.cons (singleContraction head) tail)
    (q : RedexOcc b.target) : ¬b.history.derivation.Residual ⟨p,head.redex⟩ q := by
  obtain ⟨extension,perm,_⟩ := copy
  intro alive
  have composite := (perm.residual ⟨p,head.redex⟩ q).mpr alive
  rw [ParallelHistory.derivation_append,Derivation.residual_append] at composite
  obtain ⟨middle,first,_⟩ := composite
  rw [source] at first
  change ((singleContraction head).derivation.append tail.derivation).Residual ⟨p,head.redex⟩ middle at first
  obtain ⟨afterHead,residual,_⟩ := (Derivation.residual_append _ _ _ middle).mp first
  exact (singleContraction head).no_selected_residual ⟨p,head.redex⟩ (by simp) afterHead residual

/-- Under the target's standard pointed-prefix condition, the source head
cannot precede a distinct target head. Common endpoints are never used. -/
theorem Copy.head_order {a b : RedexWithHistory m} (copy : Copy a b) (R : BetaAt m p t) (S : BetaAt m q u)
    (sourceTail : ParallelHistory t a.target) (targetTail : ParallelHistory u b.target)
    (source : a.history=.cons (singleContraction R) sourceTail)
    (target : b.history=.cons (singleContraction S) targetTail)
    (atomic : Atomic b.history) (standard : Standard b.history) : p=q ∨ LeftOf q p := by
  let first : RedexOcc m := ⟨p,R.redex⟩
  let second : RedexOcc m := ⟨q,S.redex⟩
  rcases first.compare second with same | before | after
  · exact Or.inl (congrArg Subtype.val same)
  · have targetStandard : Standard (.cons (singleContraction S) targetTail) := by rw [←target]; exact standard
    have actualNoReturn : DoesNotReturnLeft second b.history := by
      rw [target]; exact head_no_return S targetTail targetStandard
    have right : RightHistory first.val b.history := b.history.right_of_no_used first (by
      intro old prior
      apply actualNoReturn.no_used_left atomic old
      rcases prior with same | left
      · rw [same]; exact before
      · exact left.trans before)
    obtain ⟨image,_,alive⟩ := b.history.derivation.left_survives first right.paths_right
    exact False.elim (copy.source_head_deleted R sourceTail source image alive)
  · exact Or.inr after

/-- When the two standard ordinary prefixes have distinct heads, the target
head stays at its original position uniquely throughout the source prefix. -/
theorem Copy.protected_target_head {a b : RedexWithHistory m} (copy : Copy a b) (R : BetaAt m p t) (S : BetaAt m q u)
    (sourceTail : ParallelHistory t a.target) (targetTail : ParallelHistory u b.target)
    (source : a.history=.cons (singleContraction R) sourceTail)
    (target : b.history=.cons (singleContraction S) targetTail)
    (sourceAtomic : Atomic a.history) (targetAtomic : Atomic b.history)
    (sourceStandard : Standard a.history) (targetStandard : Standard b.history) (different : p≠q) :
    RightHistory q a.history ∧ ∃ image : RedexOcc a.target,
      image.val=q ∧ a.history.derivation.Residual ⟨q,S.redex⟩ image ∧
      ∀ other : RedexOcc a.target, a.history.derivation.Residual ⟨q,S.redex⟩ other → other=image := by
  have before : LeftOf q p := (copy.head_order R S sourceTail targetTail source target targetAtomic targetStandard).resolve_left different
  have canonical : Standard (.cons (singleContraction R) sourceTail) := by rw [←source]; exact sourceStandard
  have actualNoReturn : DoesNotReturnLeft ⟨p,R.redex⟩ a.history := by
    rw [source]; exact head_no_return R sourceTail canonical
  let cut : RedexOcc m := ⟨q,S.redex⟩
  have right : RightHistory q a.history := a.history.right_of_no_used cut (by
    intro old prior
    apply actualNoReturn.no_used_left sourceAtomic old
    rcases prior with same | earlier
    · rw [same]; exact before
    · exact earlier.trans before)
  obtain ⟨image,atCut,alive⟩ := a.history.derivation.left_survives cut right.paths_right
  refine ⟨right,image,atCut,alive,?_⟩
  intro other residual
  exact Subtype.ext (((a.history.derivation.left_fixed cut right.paths_right other).mp residual).trans atCut.symm)
end Lamping.Lambda

