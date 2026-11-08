import Lamping.Lambda.ResidualComposition
import Lamping.Lambda.RootHeadGuard
namespace Lamping.Lambda.Marked

theorem History.trace_empty (h : History ps t u) (empty : tracePositions r t=[]) :
    tracePositions r u=[] := by
  induction h with
  | nil => exact empty
  | cons head tail ih => exact ih (head.trace_empty empty)

end Lamping.Lambda.Marked
namespace Lamping.Lambda

/-- An old tag appearing after an actual development already named an
actual source redex. Invalid selection names cannot turn into old tags. -/
theorem ParallelStep.trace_source_valid (h : ParallelStep F t u)
    (trace : q∈Marked.tracePositions r h.markedTarget) :
    ∃ z,subtermAt t r=some z ∧ IsRedex z := by
  classical
  by_cases redex : ∃ z,subtermAt t r=some z ∧ IsRedex z
  · exact redex
  · have initialEmpty : Marked.tracePositions r (Marked.mark [] t)=[] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro p hp
      obtain ⟨same,valid⟩ := (Marked.trace_mark [] t r p).mp hp
      exact redex (same ▸ (mem_redexPositions t p).mp valid)
    have empty := h.tracked.trace_empty initialEmpty
    rw [Marked.passive_trace] at empty
    exact False.elim (List.not_mem_nil (empty ▸ trace))

theorem ParallelStep.residualSet_redex (h : ParallelStep F t u)
    (member : q∈h.residualSet names) : ∃ z,subtermAt u q=some z ∧ IsRedex z := by
  have valid := ((Marked.completeOld_iff F t).mp h.complete).1.general.valid (Marked.valid_mark F t)
  have redex := Marked.setResidualPositions_sound valid member
  rw [h.target_eq] at redex
  exact redex

/-- Fresh-middle residual-set composition, stated by membership. The order
of a flatMap over intermediate copies is deliberately not equated to the
final occurrence-tree order. Names may be invalid or repeated. -/
theorem ParallelStep.residualSet_compose_iff (h : ParallelStep F t u)
    (k : ParallelStep G u v) (names : List Path) (q : RedexOcc v) :
    q.val∈k.residualSet (h.residualSet names) ↔
      ∃ r : RedexOcc t, r.val∈names ∧ (h.derivation.append k.derivation).Residual r q := by
  constructor
  · intro member
    obtain ⟨a,ha,aq⟩ := (Marked.mem_setResidualPositions _ _ _).mp member
    let mid : RedexOcc u := ⟨a,h.residualSet_redex ha⟩
    obtain ⟨r,hr,ra⟩ := (Marked.mem_setResidualPositions _ _ _).mp ha
    let old : RedexOcc t := ⟨r,h.trace_source_valid ra⟩
    exact ⟨old,hr,(Derivation.residual_append _ _ old q).mpr
      ⟨mid,(h.residual_iff old mid).mpr ra,(k.residual_iff mid q).mpr aq⟩⟩
  · rintro ⟨r,hr,residual⟩
    obtain ⟨mid,first,last⟩ := (Derivation.residual_append _ _ r q).mp residual
    apply (Marked.mem_setResidualPositions _ _ _).mpr
    refine ⟨mid.val,?_,(k.residual_iff mid q).mp last⟩
    exact (Marked.mem_setResidualPositions _ _ _).mpr ⟨r.val,hr,(h.residual_iff r mid).mp first⟩

/-- All three-dimensional selections transported through the two paths of
a genuine square agree extensionally, for arbitrary initial name lists. -/
theorem ParallelMovesSquare.composite_residualSet_members (sq : ParallelMovesSquare F G t u v w)
    (names : List Path) (p : Path) :
    p∈sq.afterFirst.residualSet (sq.first.residualSet names) ↔
      p∈sq.afterSecond.residualSet (sq.second.residualSet names) := by
  constructor
  · intro member
    let q : RedexOcc w := ⟨p,sq.afterFirst.residualSet_redex member⟩
    obtain ⟨r,hr,residual⟩ := (sq.first.residualSet_compose_iff sq.afterFirst names q).mp member
    exact (sq.second.residualSet_compose_iff sq.afterSecond names q).mpr
      ⟨r,hr,(sq.residual r q).mp residual⟩
  · intro member
    let q : RedexOcc w := ⟨p,sq.afterSecond.residualSet_redex member⟩
    obtain ⟨r,hr,residual⟩ := (sq.second.residualSet_compose_iff sq.afterSecond names q).mp member
    exact (sq.first.residualSet_compose_iff sq.afterFirst names q).mpr
      ⟨r,hr,(sq.residual r q).mpr residual⟩

end Lamping.Lambda
