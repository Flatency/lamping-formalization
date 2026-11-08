import Lamping.Lambda.StandardizationPullLeft
namespace Lamping.Lambda
/-- Explicit geometry of actual selections at each intermediate term. This
predicate contains no permutation, standardness or transport conclusion. -/
inductive RightHistory (cut : Path) : ParallelHistory t u → Prop where
  | nil (t) : RightHistory cut (.nil t)
  | cons (h : ParallelStep F t u) (tail : ParallelHistory u v) :
      (∀ r : RedexOcc t, r.val∈F → LeftOf cut r.val) →
      RightHistory cut tail → RightHistory cut (.cons h tail)
/-- Construct the entire genuine tile row pulling a later left contraction
through any right-side history. The residual row has exactly the original
number of parallel steps, including empty ones. -/
theorem RightHistory.pull_step {ρ : ParallelHistory t u} {cut : Path}
    (right : RightHistory cut ρ) (s : RedexOcc t) (atCut : s.val=cut)
    (last : BetaAt u cut w) :
    ∃ (v : Term) (source : BetaAt t cut v) (tail : ParallelHistory v w),
      PermEq (ρ.append (.single (singleContraction last)))
        ((ParallelHistory.single (singleContraction source)).append tail) ∧ tail.length=ρ.length := by
  induction right generalizing w with
  | nil t => exact ⟨w,last,.nil _,.refl _,rfl⟩
  | @cons F t u v h row allRight tailRight ih =>
    have sourceRight : ∀ r : RedexOcc t, r.val∈F → LeftOf s.val r.val := by
      intro r hr
      rw [atCut]
      exact allRight r hr
    obtain ⟨q,qAt,residual,_⟩ := h.left_residual_exists s sourceRight
    have qCut : q.val=cut := qAt.trans atCut
    obtain ⟨z,head,after,perm,length⟩ := ih q qCut last
    obtain ⟨v',source⟩ := s.contract_exists
    have sourceCut : BetaAt t cut v' := by rw [←atCut]; exact source
    have headAt : BetaAt u s.val z := by rw [atCut]; exact head
    obtain ⟨first,pull⟩ := h.pull_left_step s sourceRight source headAt
    refine ⟨v',sourceCut,.cons first after,?_,?_⟩
    · cases atCut
      have leadingPerm := PermEq.prepend (ParallelHistory.single h) perm
      have exchange := pull.append after
      exact .trans (by simpa only [ParallelHistory.append_assoc] using leadingPerm)
        (by simpa only [ParallelHistory.append_assoc,ParallelHistory.append,ParallelHistory.single] using exchange)
    · simp only [ParallelHistory.length,length]
end Lamping.Lambda
