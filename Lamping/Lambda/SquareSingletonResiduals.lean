import Lamping.Lambda.ParallelPrefixResidualSet
import Lamping.Lambda.ResidualComposition
namespace Lamping.Lambda

theorem ParallelStep.residual_singleton_iff (h : ParallelStep F t u)
    (r : RedexOcc t) (a s : RedexOcc u)
    (image : h.residualSet [r.val] = [a.val]) : h.derivation.Residual r s ↔ s = a := by
  have trace : Marked.tracePositions r.val h.markedTarget = [a.val] := by
    simpa only [ParallelStep.residualSet, Marked.setResidualPositions, List.flatMap_cons,
      List.flatMap_nil, List.append_nil] using image
  rw [h.residual_iff, trace, List.mem_singleton]
  exact ⟨Subtype.ext, congrArg Subtype.val⟩

theorem ParallelStep.residual_append_singleton (h : ParallelStep F t u)
    (k : Derivation u v) (r : RedexOcc t) (a : RedexOcc u) (q : RedexOcc v)
    (image : h.residualSet [r.val] = [a.val]) :
    (h.derivation.append k).Residual r q ↔ k.Residual a q := by
  rw [Derivation.residual_append]
  constructor
  · rintro ⟨s,hs,hsq⟩
    cases (h.residual_singleton_iff r a s image).mp hs
    exact hsq
  · intro hq
    exact ⟨a,(h.residual_singleton_iff r a a image).mpr rfl,hq⟩

/-- A square transports any singleton old image to the same literal residual
 list on both opposite sides. Fixed occurrence-tree order is retained. -/
theorem ParallelMovesSquare.singleton_residualSet
    (sq : ParallelMovesSquare F G t u v w) (r : RedexOcc t)
    (a : RedexOcc u) (b : RedexOcc v)
    (left : sq.first.residualSet [r.val] = [a.val])
    (right : sq.second.residualSet [r.val] = [b.val]) :
    sq.afterFirst.residualSet [a.val] = sq.afterSecond.residualSet [b.val] := by
  have equivalence (q : RedexOcc w) :
      sq.afterFirst.derivation.Residual a q ↔ sq.afterSecond.derivation.Residual b q :=
    (sq.first.residual_append_singleton sq.afterFirst.derivation r a q left).symm.trans
      ((sq.residual r q).trans (sq.second.residual_append_singleton sq.afterSecond.derivation r b q right))
  simp only [ParallelStep.residualSet, Marked.setResidualPositions, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]
  apply Marked.trace_eq_of_members (sq.afterFirst.target_eq.trans sq.afterSecond.target_eq.symm)
  have validLeft := ((Marked.completeOld_iff _ _).mp sq.afterFirst.complete).1.general.valid (Marked.valid_mark _ _)
  have validRight := ((Marked.completeOld_iff _ _).mp sq.afterSecond.complete).1.general.valid (Marked.valid_mark _ _)
  intro q
  constructor
  · intro hq
    have redex := Marked.tracePositions_sound validLeft hq
    rw [sq.afterFirst.target_eq] at redex
    let occurrence : RedexOcc w := ⟨q,redex⟩
    exact (sq.afterSecond.residual_iff b occurrence).mp
      ((equivalence occurrence).mp ((sq.afterFirst.residual_iff a occurrence).mpr hq))
  · intro hq
    have redex := Marked.tracePositions_sound validRight hq
    rw [sq.afterSecond.target_eq] at redex
    let occurrence : RedexOcc w := ⟨q,redex⟩
    exact (sq.afterFirst.residual_iff a occurrence).mp
      ((equivalence occurrence).mpr ((sq.afterSecond.residual_iff b occurrence).mpr hq))

end Lamping.Lambda
