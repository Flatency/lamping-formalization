import Lamping.Lambda.FamilyDevelopments
import Lamping.Lambda.HistoryProjection
import Lamping.Lambda.ProjectionSelections
import Lamping.Lambda.ResidualSetComposition
namespace Lamping.Lambda

/-- Actual final selected redexes have actual initial selected ancestors,
even when the initial list also contains invalid names. -/
theorem StepProjection.final_selection_actual {step : ParallelStep F t u}
    {σ : ParallelHistory t v} {σ' : ParallelHistory u w} {last : ParallelStep G v w}
    (row : StepProjection step σ σ' last) (s : RedexOcc v) :
    s.val∈G ↔ ∃ r : RedexOcc t, r.val∈F ∧ σ.derivation.Residual r s := by
  induction row with
  | nil =>
    constructor
    · intro hs; exact ⟨s,hs,(Derivation.residual_nil _ _).mpr rfl⟩
    · rintro ⟨r,hr,hs⟩
      cases (Derivation.residual_nil r s).mp hs
      exact hr
  | cons sq tail ih =>
    rw [ih]
    constructor
    · rintro ⟨mid,selected,residual⟩
      obtain ⟨p,hp,trace⟩ := (Marked.mem_setResidualPositions _ _ _).mp selected
      let r : RedexOcc _ := ⟨p,sq.second.trace_source_valid trace⟩
      exact ⟨r,hp,(Derivation.residual_append _ _ r s).mpr
        ⟨mid,(sq.second.residual_iff r mid).mpr trace,residual⟩⟩
    · rintro ⟨r,hr,residual⟩
      obtain ⟨mid,first,last⟩ := (Derivation.residual_append _ _ r s).mp residual
      exact ⟨mid,(Marked.mem_setResidualPositions _ _ _).mpr
        ⟨r.val,hr,(sq.second.residual_iff r mid).mp first⟩,last⟩

theorem StepProjection.selected_copy {step : ParallelStep F t u}
    {σ : ParallelHistory t v} {σ' : ParallelHistory u w} {last : ParallelStep G v w}
    (row : StepProjection step σ σ' last) (pre : ParallelHistory m t)
    (s : RedexOcc v) (selected : s.val∈G) :
    ∃ r : RedexOcc t, r.val∈F ∧ Copy ⟨t,pre,r⟩ ⟨v,pre.append σ,s⟩ := by
  obtain ⟨r,hr,residual⟩ := (row.final_selection_actual s).mp selected
  exact ⟨r,hr,⟨σ,.refl _,residual⟩⟩

/-- Every selected event in the residual of the left history is a genuine
Copy-family event of that history, at its original global source. -/
theorem HistoryProjection.used_left {ρ : ParallelHistory t u} {σ : ParallelHistory t v}
    {ρ' : ParallelHistory v w} {σ' : ParallelHistory u w} (grid : HistoryProjection ρ σ ρ' σ')
    (pre : ParallelHistory m t) (used : FamilyUsedAt (pre.append σ) ρ' a) :
    FamilyUsedAt pre ρ a := by
  induction grid with
  | nil => cases used
  | @cons t u v w F z h σ mid σ₁ G last ρ ρ' σ' row tail ih =>
    rcases (FamilyUsedAt.append_iff (pre.append σ) (.single last) ρ' a).mp used with first | rest
    · cases first with
      | head selected family =>
        obtain ⟨r,selected,copy⟩ := row.selected_copy pre _ selected
        exact .head selected (.trans (.copy copy) family)
      | tail impossible => cases impossible
    · have perm : PermEq ((pre.append (.single h)).append σ₁)
          ((pre.append σ).append (.single last)) := by
        simpa only [ParallelHistory.append_assoc] using PermEq.prepend pre row.permutation
      have changed := rest.prefix_permutation perm.symm
      exact .tail (ih (pre.append (.single h)) changed)

end Lamping.Lambda
