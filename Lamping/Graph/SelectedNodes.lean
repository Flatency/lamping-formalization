import Lamping.Graph.Core
namespace Lamping.Graph

/-- Names other than the two actual selected interaction nodes. -/
def RemainingNodes {N : Type} (first second : N) := {n : N // n≠first ∧ n≠second}

noncomputable def remainingNodesFinite {N : Type} [FiniteNames N] (first second : N) :
    FiniteNames (RemainingNodes first second) := by
  classical
  refine ⟨FiniteNames.all.attach.filterMap (fun n =>
    if h : n.val≠first ∧ n.val≠second then some ⟨n.val,h⟩ else none),?_⟩
  intro n
  apply List.mem_filterMap.mpr
  refine ⟨⟨n.val,FiniteNames.complete n.val⟩,List.mem_attach _ _,?_⟩
  rw [dif_pos n.property]
  exact congrArg some (Subtype.ext rfl)

/-- Select two different physical nodes without assuming that the entire
ambient graph already uses the special carrier of PathSite. -/
noncomputable def splitSelectedNodes {N : Type} (first second : N) (different : first≠second) :
    Bij (RemainingNodes first second ⊕ (Unit ⊕ Unit)) N := by
  classical
  refine {
    toFun := fun name => match name with
      | .inl n => n.val
      | .inr (.inl _) => first
      | .inr (.inr _) => second
    invFun := fun n => if h : n=first then .inr (.inl ()) else
      if k : n=second then .inr (.inr ()) else .inl ⟨n,h,k⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro name
    cases name with
    | inl n =>
      simp only [dif_neg n.property.1,dif_neg n.property.2]
      rfl
    | inr selected => cases selected <;> rename_i tag <;> cases tag <;> simp [Ne.symm different]
  · intro n
    by_cases h : n=first
    · simp only [dif_pos h]; exact h.symm
    · simp only [dif_neg h]
      by_cases k : n=second
      · simp only [dif_pos k]; exact k.symm
      · simp only [dif_neg k]
end Lamping.Graph
