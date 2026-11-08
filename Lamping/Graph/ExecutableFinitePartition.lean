import Lamping.Graph.SelectedNodes

namespace Lamping.Graph.Executable

/-- Filter the actual enumeration stably, preserving its repeated names. -/
def finiteSubtype {A : Type} [FiniteNames A] (predicate : A → Prop)
    [DecidablePred predicate] : FiniteNames {a : A // predicate a} := by
  refine ⟨FiniteNames.all.attach.filterMap (fun a =>
    if h : predicate a.val then some ⟨a.val,h⟩ else none), ?_⟩
  intro a
  apply List.mem_filterMap.mpr
  refine ⟨⟨a.val,FiniteNames.complete a.val⟩, List.mem_attach _ _, ?_⟩
  rw [dif_pos a.property]

/-- Decidable selection gives an explicit partition inverse on every name. -/
def partitionNames {A : Type} (predicate : A → Prop) [DecidablePred predicate] :
    Bij ({a : A // ¬ predicate a} ⊕ {a : A // predicate a}) A := by
  refine {
    toFun := fun side => match side with | .inl a => a.val | .inr a => a.val
    invFun := fun a => if h : predicate a then .inr ⟨a,h⟩ else .inl ⟨a,h⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro side
    cases side with
    | inl a => rw [dif_neg a.property]
    | inr a => rw [dif_pos a.property]
  · intro a
    by_cases selected : predicate a
    · simp only [dif_pos selected]
    · simp only [dif_neg selected]

def remainingNodesFinite {N : Type} [FiniteNames N] [DecidableEq N]
    (first second : N) : FiniteNames (RemainingNodes first second) :=
  finiteSubtype (fun n => n ≠ first ∧ n ≠ second)

def splitSelectedNodes {N : Type} [DecidableEq N]
    (first second : N) (different : first ≠ second) :
    Bij (RemainingNodes first second ⊕ (Unit ⊕ Unit)) N := by
  refine {
    toFun := fun name => match name with
      | .inl n => n.val
      | .inr (.inl _) => first
      | .inr (.inr _) => second
    invFun := fun n => if h : n = first then .inr (.inl ()) else
      if k : n = second then .inr (.inr ()) else .inl ⟨n,h,k⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro name
    cases name with
    | inl n =>
      simp only [dif_neg n.property.1, dif_neg n.property.2]
      rfl
    | inr selected => cases selected <;> rename_i tag <;> cases tag <;> simp [Ne.symm different]
  · intro n
    by_cases h : n = first
    · simp only [dif_pos h]; exact h.symm
    · simp only [dif_neg h]
      by_cases k : n = second
      · simp only [dif_pos k]; exact k.symm
      · simp only [dif_neg k]
end Lamping.Graph.Executable
