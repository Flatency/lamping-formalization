import Lamping.Lambda.OccurrenceOrder
import Lamping.Lambda.ContextualResiduals
import Lamping.Lambda.SingleContraction
namespace Lamping.Lambda
/-- A strictly earlier occurrence cannot lie inside the later occurrence. -/
theorem LeftOf.not_inside_right (h : LeftOf p q) : ¬∃ tail, p=q++tail := by
  induction h with
  | outer s p => rintro ⟨tail,eq⟩; cases eq
  | child s h ih =>
    rintro ⟨tail,eq⟩
    exact ih ⟨tail,(List.cons.inj eq).2⟩
  | branch p q => rintro ⟨tail,eq⟩; cases eq
/-- A contraction strictly to the right preserves the left source redex at
exactly its original occurrence, proved using real old-name tracking. -/
theorem BetaAt.left_residual_iff (h : BetaAt t p u) (s : RedexOcc t)
    (before : LeftOf s.val p) (q : RedexOcc u) :
    (singleContraction h).derivation.Residual s q ↔ q.val=s.val := by
  have tracked : Marked.History ([[]].map (fun q => p++q)) (Marked.mark [] t)
      (singleContraction h).markedTarget.passive := by
    simpa only [List.map_cons,List.map_nil,List.append_nil] using (singleContraction h).tracked
  have fixed := tracked.trace_fixed_outside (r:=s.val) (by
    intro tail trace
    have same := (Marked.initial_residual [] t s (p++tail)).mp trace
    exact before.not_inside_right ⟨tail,same.symm⟩)
  rw [(singleContraction h).residual_iff,←Marked.passive_trace,fixed]
  exact Marked.initial_residual [] t s q.val
/-- Existence accompanies the equality characterization; no target residual
certificate is required to establish that the old left redex survives. -/
theorem BetaAt.left_residual_exists (h : BetaAt t p u) (s : RedexOcc t)
    (before : LeftOf s.val p) :
    ∃ q : RedexOcc u, q.val=s.val ∧ (singleContraction h).derivation.Residual s q ∧
      ∀ q' : RedexOcc u, (singleContraction h).derivation.Residual s q' → q'=q := by
  have tracked : Marked.History ([[]].map (fun q => p++q)) (Marked.mark [] t)
      (singleContraction h).markedTarget.passive := by
    simpa only [List.map_cons,List.map_nil,List.append_nil] using (singleContraction h).tracked
  have fixed := tracked.trace_fixed_outside (r:=s.val) (by
    intro tail trace
    have same := (Marked.initial_residual [] t s (p++tail)).mp trace
    exact before.not_inside_right ⟨tail,same.symm⟩)
  have alive : s.val∈Marked.tracePositions s.val (singleContraction h).markedTarget.passive := by
    rw [fixed]
    exact (Marked.initial_residual [] t s s.val).mpr rfl
  have valid := tracked.valid (Marked.valid_mark [] t)
  have isRedex := Marked.tracePositions_sound valid alive
  have erase : (singleContraction h).markedTarget.passive.erase=u :=
    (Marked.passive_erase _).trans (singleContraction h).target_eq
  rw [erase] at isRedex
  let q : RedexOcc u := ⟨s.val,isRedex⟩
  refine ⟨q,rfl,(h.left_residual_iff s before q).mpr rfl,?_⟩
  intro q' residual
  exact Subtype.ext ((h.left_residual_iff s before q').mp residual)
end Lamping.Lambda
