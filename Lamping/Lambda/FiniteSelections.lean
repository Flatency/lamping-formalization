import Lamping.Lambda.PermutationResidual
namespace Lamping.Lambda
 theorem ParallelStep.endpoint_selection (h : ParallelStep F t u) (k : ParallelStep G t v)
     (he : ∀ p, p ∈ F ↔ p ∈ G) : u = v := by
   have hm : Marked.mark F t = Marked.mark G t := by
     apply Marked.selected_passive_injective (Marked.selected_mark F t)
     · exact (Marked.selected_mark G t).mem_congr (fun p => (he p).symm)
     · rw [Marked.passive_mark, Marked.passive_mark]
   have hh := (Marked.completeOld_iff F t).mp h.complete
   have hk := (Marked.completeOld_iff G t).mp k.complete
   have hhs := hh.1.steps
   rw [hm] at hhs
   have ht := Marked.complete_unique ⟨hhs, hh.2⟩ ⟨hk.1.steps, hk.2⟩
   exact h.target_eq.symm.trans ((congrArg Marked.erase ht).trans k.target_eq)
 theorem ParallelStep.residualSet_empty_of_equiv (h : ParallelStep F t u)
     (he : ∀ p, p ∈ F ↔ p ∈ G) : h.residualSet G = [] := by
   have hn (p : Path) (hp : p ∈ h.residualSet G) : False := by
     obtain ⟨r, hr, hpr⟩ := (Marked.mem_setResidualPositions G _ p).mp hp
     have hm := (Marked.mem_setResidualPositions F _ p).mpr ⟨r, (he r).mpr hr, hpr⟩
     rw [h.complete.2] at hm
     exact List.not_mem_nil hm
   cases hh : h.residualSet G with
   | nil => rfl
   | cons p ps => exact False.elim (hn p (by simp [hh]))

 theorem PermEq.empty_of_selection (h : ParallelStep F t t) (he : F = []) :
     PermEq (ParallelHistory.single h) (.nil t) := by
   subst F
   exact .empty h

/-- Extensional finite-set representation: reordering or repeating selection
 entries cannot produce a distinct permutation class. Derived solely from
 genuine moves and deletion of empty residues, not an added equality axiom. -/
 theorem PermEq.selection (h : ParallelStep F t u) (k : ParallelStep G t u)
     (he : ∀ p, p ∈ F ↔ p ∈ G) :
     PermEq (ParallelHistory.single h) (.single k) := by
   have hFG := h.residualSet_empty_of_equiv he
   have hGF := k.residualSet_empty_of_equiv (fun p => (he p).symm)
   let a : ParallelStep (h.residualSet G) u u := by rw [hFG]; exact ParallelStep.empty u
   let b : ParallelStep (k.residualSet F) u u := by rw [hGF]; exact ParallelStep.empty u
   have ha := PermEq.comp (PermEq.refl (ParallelHistory.single h)) (PermEq.empty_of_selection a hFG)
   have hb := PermEq.comp (PermEq.refl (ParallelHistory.single k)) (PermEq.empty_of_selection b hGF)
   rw [ParallelHistory.append_nil] at ha hb
   exact .trans (.symm ha) (.trans (.moves ⟨h, k, a, b⟩) hb)
end Lamping.Lambda

