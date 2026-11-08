import Lamping.Lambda.OccurrenceRank
import Lamping.Lambda.DerivationProjection
import Lamping.Lambda.StandardizationFactorization
namespace Lamping.Lambda
/-- Genuine selected LO occurrences are unique, even for repeated list names. -/
theorem LeftmostSelected.unique (hr : LeftmostSelected F r) (hs : LeftmostSelected F s) : r=s := by
  rcases r.compare s with eq | before | after
  · exact eq
  · exact False.elim (hs.2 r hr.1 before)
  · exact False.elim (hr.2 s hs.1 after)
/-- A single genuine parallel step never returns left of its own selected LO. -/
theorem DoesNotReturnLeft.single (h : ParallelStep F t u) (r : RedexOcc t)
    (hr : LeftmostSelected F r) : DoesNotReturnLeft r (ParallelHistory.single h) := by
  intro s before v w G pre step suffix eq q selected residual
  cases pre with
  | nil =>
    simp only [ParallelHistory.append] at eq
    cases eq
    have same : r=q := hr.unique selected
    have ancestor : s=q := (Derivation.residual_nil s q).mp residual
    subst q
    subst s
    exact LeftOf.irrefl _ before
  | cons first tail =>
    have lengths := congrArg ParallelHistory.length eq
    simp only [ParallelHistory.single,ParallelHistory.length,ParallelHistory.length_append] at lengths
    omega

theorem Standard.single_step (h : ParallelStep F t u) (r : RedexOcc t)
    (hr : LeftmostSelected F r) : Standard (ParallelHistory.single h) :=
  .cons h r hr (DoesNotReturnLeft.single h r hr) (.nil u)
end Lamping.Lambda
namespace Lamping.Lambda
/-- A real LO exists whenever a finite list selects any actual redex; invalid
path names and duplicates remain permitted in the original selection. -/
theorem leftmost_actual_selected_exists (F : List Path)
    (inhabited : ∃ r : RedexOcc t, r.val∈F) : ∃ r : RedexOcc t, LeftmostSelected F r := by
  let G := F.filter (fun p => p∈redexPositions t)
  have valid : ∀ p∈G, ∃ v, subtermAt t p=some v ∧ IsRedex v := by
    intro p hp
    exact (mem_redexPositions t p).mp (of_decide_eq_true (List.mem_filter.mp hp).2)
  have nonempty : G≠[] := by
    intro empty
    obtain ⟨r,hr⟩ := inhabited
    have mem : r.val∈G := List.mem_filter.mpr ⟨hr,by simpa using (mem_redexPositions t r.val).mpr r.property⟩
    rw [empty] at mem
    exact List.not_mem_nil mem
  obtain ⟨r,hr⟩ := leftmost_selected_exists G valid nonempty
  refine ⟨r,(List.mem_filter.mp hr.1).1,?_⟩
  intro q hq
  exact hr.2 q (List.mem_filter.mpr ⟨hq,by simpa using (mem_redexPositions t q.val).mpr q.property⟩)

theorem ParallelStep.no_actual_endpoint (h : ParallelStep F t u)
    (noneSelected : ∀ r : RedexOcc t, r.val∉F) : u=t := by
  have normal : Marked.Normal (Marked.mark F t) := Marked.normal_of_no_active (by
    intro p hp
    obtain ⟨member,valid⟩ := (Marked.active_mark F t p).mp hp
    exact noneSelected ⟨p,(mem_redexPositions t p).mp valid⟩ member)
  have complete := (Marked.completeOld_iff F t).mp h.complete
  have same : h.markedTarget=Marked.mark F t :=
    Marked.complete_unique ⟨complete.1.steps,complete.2⟩ ⟨.refl _,normal⟩
  exact h.target_eq.symm.trans ((congrArg Marked.erase same).trans (Marked.erase_mark F t))

theorem PermEq.no_actual_selection (h : ParallelStep F t t)
    (noneSelected : ∀ r : RedexOcc t, r.val∉F) :
    PermEq (ParallelHistory.single h) (.nil t) := by
  let empty := ParallelStep.empty t
  have residualEmpty : empty.residualSet F=[] := by
    have impossible (p : Path) (hp : p∈empty.residualSet F) : False := by
      obtain ⟨r,member,trace⟩ := (Marked.mem_setResidualPositions F _ p).mp hp
      obtain ⟨same,valid⟩ := (Marked.trace_mark [] t r p).mp trace
      subst r
      exact noneSelected ⟨p,(mem_redexPositions t p).mp valid⟩ member
    cases eq : empty.residualSet F with
    | nil => rfl
    | cons p ps => exact False.elim (impossible p (by simp [eq]))
  let afterH : ParallelStep (h.residualSet []) t t := ParallelStep.empty t
  let afterEmpty : ParallelStep (empty.residualSet F) t t := by rw [residualEmpty]; exact ParallelStep.empty t
  have moves := PermEq.moves (⟨h,empty,afterH,afterEmpty⟩ : ParallelMovesSquare F [] t t t t)
  have left := PermEq.comp (PermEq.refl (ParallelHistory.single h)) (PermEq.empty_of_selection afterH rfl)
  rw [ParallelHistory.append_nil] at left
  have right := PermEq.comp (PermEq.empty empty) (PermEq.empty_of_selection afterEmpty residualEmpty)
  simp only [ParallelHistory.append] at right
  exact .trans left.symm (.trans moves right)
/-- A fully general one-step existence case, including nonempty lists whose
names select no redex. It retains the original unrestricted selection interface. -/
theorem standardize_single (h : ParallelStep F t u) :
    ∃ σ : ParallelHistory t u, Standard σ ∧ PermEq (ParallelHistory.single h) σ := by
  classical
  by_cases selected : ∃ r : RedexOcc t, r.val∈F
  · obtain ⟨r,hr⟩ := leftmost_actual_selected_exists F selected
    exact ⟨.single h,Standard.single_step h r hr,.refl _⟩
  · have noneSelected : ∀ r : RedexOcc t, r.val∉F := fun r hr => selected ⟨r,hr⟩
    have endpoint := h.no_actual_endpoint noneSelected
    subst u
    exact ⟨.nil t,.nil t,PermEq.no_actual_selection h noneSelected⟩
end Lamping.Lambda
