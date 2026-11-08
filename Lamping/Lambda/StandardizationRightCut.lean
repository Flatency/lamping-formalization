import Lamping.Lambda.StandardizationLeftResiduals
namespace Lamping.Lambda.Marked
private theorem nil_cut_lam (b : Marked) : ∀ q∈activePositions (.lam b), LeftOf [] q := by
  intro q hq
  obtain ⟨p,_,rfl⟩ := List.mem_map.mp hq
  exact .outer _ _
private theorem nil_cut_app (l : List Path) (f a : Marked) :
    ∀ q∈activePositions (.app l f a), LeftOf [] q := by
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  all_goals obtain ⟨p,_,rfl⟩ := List.mem_map.mp hq; exact .outer _ _
private theorem body_cut_lam {cut : Path} {b : Marked}
    (right : ∀ q∈activePositions (.lam b), LeftOf (.body::cut) q) :
    ∀ q∈activePositions b, LeftOf cut q := by
  intro q hq
  have h := right (.body::q) (List.mem_map.mpr ⟨q,hq,rfl⟩)
  cases h with | child _ h => exact h
private theorem fn_cut_app {cut : Path} {l : List Path} {f a : Marked}
    (right : ∀ q∈activePositions (.app l f a), LeftOf (.fn::cut) q) :
    ∀ q∈activePositions f, LeftOf cut q := by
  intro q hq
  have h := right (.fn::q) (List.mem_append_left _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
  cases h with | child _ h => exact h
private theorem arg_cut_app {cut : Path} {l : List Path} {f a : Marked}
    (right : ∀ q∈activePositions (.app l f a), LeftOf (.arg::cut) q) :
    ∀ q∈activePositions a, LeftOf cut q := by
  intro q hq
  have h := right (.arg::q) (List.mem_append_right _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
  cases h with | child _ h => exact h
/-- All remaining active residuals stay strictly to the right of a fixed cut.
The premise is an independently checked source active-set geometry property. -/
theorem StepAt.right_cut (h : StepAt p t u)
    (right : ∀ q∈activePositions t, LeftOf cut q) :
    ∀ q∈activePositions u, LeftOf cut q := by
  induction h generalizing cut with
  | root l b a => have impossible:=right [] (by simp [activePositions]); cases impossible
  | @lam p b b' h ih =>
    have before := right (.body::p) (by simp [activePositions,h.active])
    cases cut with
    | nil => exact nil_cut_lam b'
    | cons s cut =>
      cases s with
      | fn => cases before
      | arg => cases before
      | body =>
        intro q hq
        obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hq
        exact .child _ (ih (body_cut_lam right) p hp)
  | @appL p f f' l a h ih =>
    have before := right (.fn::p) (by simp [activePositions,h.active])
    cases cut with
    | nil => exact nil_cut_app l f' a
    | cons s cut =>
      cases s with
      | body => cases before
      | arg => cases before
      | fn =>
        intro q hq
        rcases List.mem_append.mp hq with hf | ha
        · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hf
          exact .child _ (ih (fn_cut_app right) p hp)
        · obtain ⟨p,_,rfl⟩ := List.mem_map.mp ha
          exact .branch _ _
  | @appR p a a' l f h ih =>
    have before := right (.arg::p) (by simp [activePositions,h.active])
    cases cut with
    | nil => exact nil_cut_app l f a'
    | cons s cut =>
      cases s with
      | body => cases before
      | fn =>
        intro q hq
        rcases List.mem_append.mp hq with hf | ha
        · exact right q (List.mem_append_left _ hf)
        · obtain ⟨p,_,rfl⟩ := List.mem_map.mp ha
          exact .branch _ _
      | arg =>
        intro q hq
        rcases List.mem_append.mp hq with hf | ha
        · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hf
          have impossible := right (.fn::p) (List.mem_append_left _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
          cases impossible
        · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp ha
          exact .child _ (ih (arg_cut_app right) p hp)
  | redL h ih => have impossible:=right [] (by simp [activePositions]); cases impossible
  | redR h ih => have impossible:=right [] (by simp [activePositions]); cases impossible
end Lamping.Lambda.Marked
namespace Lamping.Lambda.Marked
/-- Every actual contraction in the relative development remains right of the
cut; the invariant is derived through the real active-set transitions. -/
theorem RelativeHistory.right_paths (h : RelativeHistory ps t u)
    (right : ∀ q∈activePositions t, LeftOf cut q) : ∀ q∈ps, LeftOf cut q := by
  induction h with
  | nil => simp
  | cons first tail ih =>
    intro q hq
    rcases List.mem_cons.mp hq with same | later
    · subst q; exact right _ first.active
    · exact ih (first.right_cut right) q later
/-- Actual old-name traces at the cut are fixed by any history whose concrete
contraction occurrences all lie strictly to its right. -/
theorem History.trace_fixed_right (h : History ps t u)
    (right : ∀ q∈ps, LeftOf cut q)
    (atCut : ∀ q∈tracePositions name t, q=cut) : tracePositions name u=tracePositions name t := by
  induction h with
  | nil => rfl
  | @cons p t v ps u first tail ih =>
    have before := right p (List.mem_cons_self ..)
    have fixed := first.trace_outside (r:=name) (by
      intro suffix member
      exact before.not_inside_right ⟨suffix,(atCut _ member).symm⟩)
    have last := ih (fun q hq => right q (List.mem_cons_of_mem _ hq)) (by
      intro q hq
      rw [fixed] at hq
      exact atCut q hq)
    exact last.trans fixed
end Lamping.Lambda.Marked
namespace Lamping.Lambda
/-- An entire arbitrary complete parallel step preserves every source redex
strictly left of all its actually selected redexes, at the original path. -/
theorem ParallelStep.left_residual_iff (h : ParallelStep F t u) (s : RedexOcc t)
    (right : ∀ r : RedexOcc t, r.val∈F → LeftOf s.val r.val) (q : RedexOcc u) :
    h.derivation.Residual s q ↔ q.val=s.val := by
  have initial : ∀ p∈Marked.activePositions (Marked.mark F t), LeftOf s.val p := by
    intro p hp
    obtain ⟨selected,valid⟩ := (Marked.active_mark F t p).mp hp
    exact right ⟨p,(mem_redexPositions t p).mp valid⟩ selected
  have paths := ((Marked.completeOld_iff F t).mp h.complete).1.right_paths initial
  have fixed := h.tracked.trace_fixed_right paths (fun p hp => (Marked.initial_residual [] t s p).mp hp)
  rw [h.residual_iff,←Marked.passive_trace,fixed]
  exact Marked.initial_residual [] t s q.val

theorem ParallelStep.left_residual_exists (h : ParallelStep F t u) (s : RedexOcc t)
    (right : ∀ r : RedexOcc t, r.val∈F → LeftOf s.val r.val) :
    ∃ q : RedexOcc u, q.val=s.val ∧ h.derivation.Residual s q ∧
      ∀ q' : RedexOcc u, h.derivation.Residual s q' → q'=q := by
  have initial : ∀ p∈Marked.activePositions (Marked.mark F t), LeftOf s.val p := by
    intro p hp
    obtain ⟨selected,valid⟩ := (Marked.active_mark F t p).mp hp
    exact right ⟨p,(mem_redexPositions t p).mp valid⟩ selected
  have paths := ((Marked.completeOld_iff F t).mp h.complete).1.right_paths initial
  have fixed := h.tracked.trace_fixed_right paths (fun p hp => (Marked.initial_residual [] t s p).mp hp)
  have alive : s.val∈Marked.tracePositions s.val h.markedTarget.passive := by
    rw [fixed]
    exact (Marked.initial_residual [] t s s.val).mpr rfl
  have isRedex := Marked.tracePositions_sound (h.tracked.valid (Marked.valid_mark [] t)) alive
  have erase : h.markedTarget.passive.erase=u := (Marked.passive_erase _).trans h.target_eq
  rw [erase] at isRedex
  let q : RedexOcc u := ⟨s.val,isRedex⟩
  exact ⟨q,rfl,(h.left_residual_iff s right q).mpr rfl,
    fun q' residual => Subtype.ext ((h.left_residual_iff s right q').mp residual)⟩
/-- The LO comparison used in source standardness supplies the entire cut
premise, including selections with repeated/invalid path names. -/
theorem LeftmostSelected.right_of_left {t : Term} {F : List Path} {r s : RedexOcc t} (hr : LeftmostSelected F r) (before : LeftOf s.val r.val)
    (q : RedexOcc t) (selected : q.val∈F) : LeftOf s.val q.val := by
  rcases r.compare q with same | later | earlier
  · cases same; exact before
  · exact before.trans later
  · exact False.elim (hr.2 q selected earlier)

theorem ParallelStep.left_of_lo_residual_iff (h : ParallelStep F t u)
    (r s : RedexOcc t) (hr : LeftmostSelected F r) (before : LeftOf s.val r.val) (q : RedexOcc u) :
    h.derivation.Residual s q ↔ q.val=s.val :=
  h.left_residual_iff s (hr.right_of_left before) q
end Lamping.Lambda
