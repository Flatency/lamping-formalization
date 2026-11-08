import Lamping.Lambda.ParallelMoves
namespace Lamping.Lambda
 theorem Derivation.residual_iff_tracking (h : Derivation t u)
     (ht : Marked.History h.paths (Marked.mark [] t) v)
     (r : RedexOcc t) (s : RedexOcc u) :
     h.Residual r s ↔ s.val ∈ Marked.tracePositions r.val v := by
   constructor
   · rintro ⟨w, hw, _, hs⟩
     rw [hw.deterministic ht] at hs
     exact hs
   · intro hs
     obtain ⟨w, hw, he⟩ := h.tracked
     have hh := hw.deterministic ht
     cases hh
     exact ⟨_, hw, he, hs⟩

 theorem ParallelStep.postdevelopment_tracking (h : ParallelStep F t u)
     (k : ParallelStep (h.residualSet G) u v) :
     Marked.History k.paths (Marked.reselect G h.markedTarget)
       (Marked.dev (Marked.reselect G h.markedTarget)) := by
   have hk := (Marked.completeOld_iff (h.residualSet G) u).mp k.complete
   obtain ⟨w, hw, hew⟩ := hk.1.lift_skeleton (h.residual_skeleton G).symm
   have hn := Marked.normal_of_skeleton hew hk.2
   have he : w = Marked.dev (Marked.reselect G h.markedTarget) :=
     Marked.complete_unique ⟨hw.steps, hn⟩ ⟨Marked.steps_to_dev _, Marked.normal_dev _⟩
   cases he
   exact hw.general

 theorem ParallelStep.composite_tracking (h : ParallelStep F t u)
     (k : ParallelStep (h.residualSet G) u v) :
     Marked.History (h.derivation.append k.derivation).paths (Marked.mark [] t)
       (Marked.dev (Marked.reselect G h.markedTarget)).passive := by
   have hh := (h.postdevelopment_tracking k).passive
   rw [Marked.passive_reselect] at hh
   exact h.tracked.append hh

/-- The square preserves every original redex, including redexes outside F∪G.
 Both sides are compared by actual beta-history transport, not re-enumeration. -/
 theorem ParallelMovesSquare.residual (s : ParallelMovesSquare F G t u v w)
     (r : RedexOcc t) (q : RedexOcc w) :
     (s.first.derivation.append s.afterFirst.derivation).Residual r q ↔
       (s.second.derivation.append s.afterSecond.derivation).Residual r q := by
   rw [Derivation.residual_iff_tracking _ (s.first.composite_tracking s.afterFirst),
     Derivation.residual_iff_tracking _ (s.second.composite_tracking s.afterSecond),
     parallel_marked_diamond s.first s.second]
end Lamping.Lambda
