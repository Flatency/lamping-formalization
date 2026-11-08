import Lamping.Lambda.ProjectionSplits
import Lamping.Lambda.ArgumentPullback
import Lamping.Lambda.ExtractionTermination
namespace Lamping.Lambda

theorem mapped_prefix_paths_injective (pre : Path) {xs ys : List Path}
    (he : xs.map (fun q => pre ++ q) = ys.map (fun q => pre ++ q)) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons => simp at he
  | cons x xs ih =>
    cases ys with
    | nil => simp at he
    | cons y ys =>
      have parts := List.cons.inj he
      have head := List.append_cancel_left parts.1
      cases head
      exact congrArg (List.cons x) (ih parts.2)

private theorem split_mapped_list {α β : Type} (f : α → β)
    (a b : List β) (xs : List α) (he : a ++ b = xs.map f) :
    ∃ left right, xs = left ++ right ∧ a = left.map f ∧ b = right.map f := by
  induction a generalizing xs with
  | nil => exact ⟨[], xs, rfl, rfl, he⟩
  | cons x a ih =>
    cases xs with
    | nil => simp at he
    | cons y ys =>
      have parts := List.cons.inj he
      obtain ⟨left, right, hs, ha, hb⟩ := ih ys parts.2
      exact ⟨y :: left, right, by rw [hs]; rfl, by rw [ha, parts.1]; rfl, hb⟩

/-- Cut the original argument history at an actual chosen-copy boundary.
 The same concrete local path prefixes are recovered on both sides. -/
theorem ArgumentLift.split_prefix (R : BetaAt t p u)
    (copyPre : ParallelHistory u a) (copyPost : ParallelHistory a v)
    (original : ParallelHistory t w)
    (lift : ArgumentLift R (copyPre.append copyPost) original)
    (ha : Atomic copyPre) (hb : Atomic copyPost) (ho : Atomic original) :
    ∃ (mid : Term) (pre : ParallelHistory t mid) (post : ParallelHistory mid w),
      Atomic pre ∧ Atomic post ∧ original = pre.append post ∧
      ∃ left right, lift.localPaths = left ++ right ∧
        copyPre.derivation.paths = left.map (fun q => (p ++ lift.occurrence) ++ q) ∧
        copyPost.derivation.paths = right.map (fun q => (p ++ lift.occurrence) ++ q) ∧
        pre.derivation.paths = left.map (fun q => (p ++ [.arg]) ++ q) ∧
        post.derivation.paths = right.map (fun q => (p ++ [.arg]) ++ q) := by
  have copied := lift.copy_paths
  simp only [ParallelHistory.derivation_append, Derivation.append] at copied
  obtain ⟨left, right, localSplit, copyLeft, copyRight⟩ :=
    split_mapped_list _ _ _ _ copied
  have leftLength : left.length = copyPre.length := by
    have eq := congrArg List.length copyLeft
    rw [ha.paths_length, List.length_map] at eq
    exact eq.symm
  have bound : left.length ≤ original.length := by
    have length := lift.length (ha.append hb) ho
    rw [ParallelHistory.length_append] at length
    omega
  obtain ⟨mid, pre, post, hp, hq, whole, hlen⟩ := ho.split_at left.length bound
  have mapped : pre.derivation.paths ++ post.derivation.paths =
      left.map (fun q => (p ++ [.arg]) ++ q) ++ right.map (fun q => (p ++ [.arg]) ++ q) := by
    have eq := lift.original_paths
    rw [localSplit, List.map_append] at eq
    have originalPaths := congrArg (fun h => h.derivation.paths) whole
    simp only [ParallelHistory.derivation_append, Derivation.append] at originalPaths
    exact originalPaths.symm.trans eq
  have prefixLength : pre.derivation.paths.length =
      (left.map (fun q => (p ++ [.arg]) ++ q)).length := by
    rw [hp.paths_length, List.length_map, hlen]
  exact ⟨mid, pre, post, hp, hq, whole, left, right, localSplit, copyLeft, copyRight,
    List.append_inj_left mapped prefixLength, List.append_inj_right mapped prefixLength⟩

end Lamping.Lambda
