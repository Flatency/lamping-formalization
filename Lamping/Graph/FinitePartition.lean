import Lamping.Graph.Core
namespace Lamping.Graph

/-- The actual finite subtype enumeration, without changing the ambient names. -/
noncomputable def finiteSubtype {A : Type} [FiniteNames A] (predicate : A → Prop) :
    FiniteNames {a : A // predicate a} := by
  classical
  refine ⟨FiniteNames.all.attach.filterMap (fun a =>
    if h : predicate a.val then some ⟨a.val,h⟩ else none),?_⟩
  intro a
  apply List.mem_filterMap.mpr
  refine ⟨⟨a.val,FiniteNames.complete a.val⟩,List.mem_attach _ _,?_⟩
  rw [dif_pos a.property]

/-- A chosen physical subset partitions all names into the kept and selected
carriers. Every name appears on exactly one side, with the original value. -/
noncomputable def partitionNames {A : Type} (predicate : A → Prop) :
    Bij ({a : A // ¬predicate a} ⊕ {a : A // predicate a}) A := by
  classical
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
end Lamping.Graph
