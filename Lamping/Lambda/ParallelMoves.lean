import Lamping.Lambda.Permutation
import Lamping.Lambda.ResidualSkeleton
namespace Lamping.Lambda
 theorem ParallelStep.residual_skeleton (h : ParallelStep F t u) (G : List Path) :
     (Marked.reselect G h.markedTarget).skeleton =
       (Marked.mark (h.residualSet G) u).skeleton := by
   have hv : Marked.Valid h.markedTarget :=
     ((Marked.completeOld_iff F t).mp h.complete).1.general.valid (Marked.valid_mark F t)
   apply Marked.skeleton_of_shape
   · rw [Marked.erase_mark, Marked.reselect_erase, h.target_eq]
   · intro p
     rw [Marked.active_mark, Marked.reselect_active G h.markedTarget hv]
     constructor
     · intro hr
       have hm : p ∈ h.residualSet G := (Marked.mem_setResidualPositions G _ p).mpr hr
       refine ⟨hm, (mem_redexPositions u p).mpr ?_⟩
       have hp := Marked.setResidualPositions_sound hv hm
       rw [h.target_eq] at hp
       exact hp
     · rintro ⟨hp, _⟩
       exact (Marked.mem_setResidualPositions G _ p).mp hp


 theorem ParallelStep.postdevelopment (h : ParallelStep F t u) (G : List Path) :
     Nonempty (ParallelStep (h.residualSet G) u
       (Marked.dev (Marked.reselect G h.markedTarget)).erase) := by
   have hv : Marked.Valid h.markedTarget :=
     ((Marked.completeOld_iff F t).mp h.complete).1.general.valid (Marked.valid_mark F t)
   let raw := Marked.reselect G h.markedTarget
   have hs := h.residual_skeleton G
   obtain ⟨qs, hqs⟩ := (Marked.steps_to_dev raw).relativeHistory
   obtain ⟨w, hw, hew⟩ := hqs.lift_skeleton hs
   have hn := Marked.normal_of_skeleton hew (Marked.normal_dev raw)
   have he : w.erase = (Marked.dev raw).erase := by
     rw [← Marked.skeleton_erase w, ← hew, Marked.skeleton_erase]
   exact ⟨⟨qs, w, (Marked.completeOld_iff (h.residualSet G) u).mpr ⟨hw, hn⟩, he⟩⟩

/-- AG5.1.4/5.1.5 parallel-moves existence for every pair of real complete
 developments. The common endpoint is constructed, never assumed. -/
 theorem ParallelMovesSquare.exists (h : ParallelStep F t u) (k : ParallelStep G t v) :
     ∃ w, Nonempty (ParallelMovesSquare F G t u v w) := by
   obtain ⟨afterH⟩ := h.postdevelopment G
   obtain ⟨afterK⟩ := k.postdevelopment F
   have he := parallel_marked_diamond h k
   rw [← he] at afterK
   exact ⟨_, ⟨⟨h, k, afterH, afterK⟩⟩⟩

 theorem parallel_moves (h : ParallelStep F t u) (k : ParallelStep G t v) :
     ∃ (w : Term) (afterH : ParallelStep (h.residualSet G) u w)
       (afterK : ParallelStep (k.residualSet F) v w),
       PermEq ((ParallelHistory.single h).append (.single afterH))
         ((ParallelHistory.single k).append (.single afterK)) := by
   obtain ⟨afterH⟩ := h.postdevelopment G
   obtain ⟨afterK⟩ := k.postdevelopment F
   have he := parallel_marked_diamond h k
   rw [← he] at afterK
   exact ⟨_, afterH, afterK, .moves ⟨h, k, afterH, afterK⟩⟩
end Lamping.Lambda


