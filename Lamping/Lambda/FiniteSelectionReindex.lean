import Lamping.Lambda.FiniteSelections
import Lamping.Lambda.NoTagTransport
import Lamping.Lambda.DisjointCommutation
namespace Lamping.Lambda

/-- Change only the finite-list representation of a selected set; preserve
 the actual development paths and marked output. -/
def ParallelStep.reindex (h : ParallelStep F t u) (G : List Path)
     (he : ∀ p, p ∈ F ↔ p ∈ G) : ParallelStep G t u where
   paths := h.paths
   markedTarget := h.markedTarget
   target_eq := h.target_eq
   complete := by
     have hm : Marked.mark F t = Marked.mark G t := by
       apply Marked.selected_passive_injective (Marked.selected_mark F t)
       · exact (Marked.selected_mark G t).mem_congr (fun p => (he p).symm)
       · rw [Marked.passive_mark, Marked.passive_mark]
     apply (Marked.completeOld_iff G t).mpr
     have hh := (Marked.completeOld_iff F t).mp h.complete
     rw [← hm]
     exact hh

/-- Disjoint singleton contractions give a genuine parallel-moves square
 whose two residual developments each have the original singleton path. -/
 theorem BetaAt.disjoint_parallel_square (hR : BetaAt t p u) (hS : BetaAt t q v)
     (hd : DisjointPositions p q) :
     ∃ w, ∃ sq : ParallelMovesSquare [p] [q] t u v w,
       sq.first = singleContraction hR ∧ sq.second = singleContraction hS ∧
       sq.afterFirst.paths = [q] ∧ sq.afterSecond.paths = [p] := by
   obtain ⟨w, hS', hR'⟩ := hR.disjoint_square hS hd
   let a := (singleContraction hS').reindex ((singleContraction hR).residualSet [q])
     (fun z => by
       rw [hR.disjoint_residualSet ⟨q, hS.redex⟩ hd]
       exact List.mem_singleton)
   let b := (singleContraction hR').reindex ((singleContraction hS).residualSet [p])
     (fun z => by
       rw [hS.disjoint_residualSet ⟨p, hR.redex⟩ ⟨hd.2, hd.1⟩]
       exact List.mem_singleton)
   exact ⟨w, ⟨singleContraction hR, singleContraction hS, a, b⟩, rfl, rfl, rfl, rfl⟩
end Lamping.Lambda
