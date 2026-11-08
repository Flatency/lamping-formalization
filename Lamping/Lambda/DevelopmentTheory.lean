import Lamping.Lambda.ResidualSelection
namespace Lamping.Lambda

/-- An actual occurrence-indexed beta derivation, independently of markings. -/
inductive BetaHistory : List Path → Term → Term → Prop where
  | nil (t) : BetaHistory [] t t
  | cons : BetaAt t p u → BetaHistory ps u v → BetaHistory (p :: ps) t v

namespace Marked

theorem History.betaHistory (h : History ps t u) : BetaHistory ps t.erase u.erase := by
  induction h with
  | nil => exact .nil _
  | cons h hs ih => exact .cons h.betaAt ih

theorem lift_betaHistory (h : BetaHistory ps m n) (t : Marked) (ht : t.erase = m) :
    ∃ u, History ps t u ∧ u.erase = n := by
  induction h generalizing t with
  | nil m => exact ⟨t, .nil t, ht⟩
  | cons hb hs ih =>
    rw [← ht] at hb
    obtain ⟨u, hu, he⟩ := lift_general_betaAt hb
    obtain ⟨v, hv, hev⟩ := ih u he
    exact ⟨v, .cons hu hv, hev⟩

/-- Relative histories contract precisely an active residual at each step. -/
inductive RelativeHistory : List Path → Marked → Marked → Prop where
  | nil (t) : RelativeHistory [] t t
  | cons : StepAt p t u → RelativeHistory ps u v → RelativeHistory (p :: ps) t v

theorem RelativeHistory.steps (h : RelativeHistory ps t u) : Steps t u := by
  induction h with
  | nil => exact .refl _
  | cons h hs ih => exact .cons h.step ih

theorem RelativeHistory.general (h : RelativeHistory ps t u) : History ps t u := by
  induction h with
  | nil => exact .nil _
  | cons h hs ih => exact .cons h.reductionAt ih

theorem Steps.relativeHistory (h : Steps t u) : ∃ ps, RelativeHistory ps t u := by
  induction h with
  | refl => exact ⟨[], .nil _⟩
  | cons h hs ih =>
    obtain ⟨p, hp⟩ := h.at
    obtain ⟨ps, hps⟩ := ih
    exact ⟨p :: ps, .cons hp hps⟩

theorem RelativeHistory.append (h : RelativeHistory ps t u) (k : RelativeHistory qs u v) :
    RelativeHistory (ps ++ qs) t v := by
  induction h with
  | nil => exact k
  | cons h hs ih => exact .cons h (ih k)

/-- An explicit bound for every order, not only a chosen normalization strategy. -/
theorem RelativeHistory.length_bound (h : RelativeHistory ps t u) (e : Nat → Nat) :
    ps.length + weight e u ≤ weight e t := by
  induction h with
  | nil => simp
  | cons h hs ih =>
    have hw := h.step.weight_lt e
    simp only [List.length_cons]
    omega

theorem RelativeHistory.completable (h : RelativeHistory ps t u) :
    ∃ qs v, RelativeHistory (ps ++ qs) t v ∧ RelativeHistory qs u v ∧ Normal v := by
  obtain ⟨qs, hqs⟩ := (steps_to_dev u).relativeHistory
  exact ⟨qs, dev u, h.append hqs, hqs, normal_dev u⟩

theorem normal_iff_active_empty (t : Marked) : Normal t ↔ activePositions t = [] := by
  constructor
  · intro h; exact complete_active_empty ⟨.refl t, h⟩
  · intro h
    apply (normal_iff_no_step t).mpr
    rintro ⟨u, hu⟩
    obtain ⟨p, hp⟩ := hu.at
    have hh := hp.active
    simp [h] at hh

/-- Finite sets of old names are transported by union of their individual
    residuals; duplicates are harmless because membership is the set interface. -/
def setResidualPositions (F : List Path) (t : Marked) : List Path :=
  F.flatMap (fun r => tracePositions r t)

theorem mem_setResidualPositions (F : List Path) (t : Marked) (p : Path) :
    p ∈ setResidualPositions F t ↔ ∃ r ∈ F, p ∈ tracePositions r t := by
  simp [setResidualPositions]

theorem setResidualPositions_sound (ht : Valid t) (hp : p ∈ setResidualPositions F t) :
    ∃ u, subtermAt t.erase p = some u ∧ IsRedex u := by
  obtain ⟨r, hr, hp⟩ := (mem_setResidualPositions F t p).mp hp
  exact tracePositions_sound ht hp

theorem complete_setResidual_independent (h : Complete t u) (k : Complete t v) (F : List Path) :
    setResidualPositions F u = setResidualPositions F v :=
  congrArg (setResidualPositions F) (complete_unique h k)

/-- Initial marking erases to the actual starting term and gives every original
    redex its own unique old name, including names outside F. -/
theorem initial_residual (F : List Path) (t : Term) (r : RedexOcc t) (p : Path) :
    p ∈ tracePositions r.val (mark F t) ↔ p = r.val := by
  rw [trace_mark]
  constructor
  · intro h; exact h.1.symm
  · intro h; subst p; exact ⟨rfl, (mem_redexPositions t r.val).mpr r.property⟩

theorem initial_active (F : List Path) (t : Term) (r : RedexOcc t) :
    r.val ∈ activePositions (mark F t) ↔ r.val ∈ F := by
  rw [active_mark]
  exact and_iff_left ((mem_redexPositions t r.val).mpr r.property)

/-- Any initial finite selection has a real complete development. -/
theorem finite_selection_complete (F : List Path) (t : Term) :
    ∃ ps u, RelativeHistory ps (mark F t) u ∧ Normal u ∧ Betas t u.erase := by
  obtain ⟨ps, hp⟩ := (steps_to_dev (mark F t)).relativeHistory
  refine ⟨ps, dev (mark F t), hp, normal_dev _, ?_⟩
  simpa only [erase_mark] using hp.steps.erase

/-- Any two complete developments of the same finite initial selection have
    equal terms and equal residuals of every initial redex R, whether R∈F or not. -/
theorem finite_developments_independent (F : List Path) (t : Term)
    (h : RelativeHistory ps (mark F t) u) (hu : Normal u)
    (k : RelativeHistory qs (mark F t) v) (hv : Normal v) (r : RedexOcc t) :
    u.erase = v.erase ∧ tracePositions r.val u = tracePositions r.val v :=
  ⟨complete_term_independent ⟨h.steps, hu⟩ ⟨k.steps, hv⟩,
    complete_residual_independent ⟨h.steps, hu⟩ ⟨k.steps, hv⟩ _⟩

theorem initial_history_scoped (h : History ps (mark F t) u) (ht : Scoped n t) :
    Scoped n u.erase := by
  have hh := h.erase
  rw [erase_mark] at hh
  exact hh.scoped ht





/-- A general actual contraction is an active contraction exactly when its
    position is selected; deterministic transport identifies the same target. -/
theorem ReductionAt.active_stepAt (h : ReductionAt p t u) (hp : p ∈ activePositions t) :
    StepAt p t u := by
  obtain ⟨v, hv⟩ := active_has_step hp
  cases h.deterministic hv.reductionAt
  exact hv

/-- AG-relative histories use old residual membership, independently of the
    red-constructor definition of RelativeHistory. -/
inductive RelativeOldHistory (F : List Path) : List Path → Marked → Marked → Prop where
  | nil (t) : RelativeOldHistory F [] t t
  | cons : ReductionAt p t u → p ∈ setResidualPositions F t →
      RelativeOldHistory F ps u v → RelativeOldHistory F (p :: ps) t v

theorem relativeOld_iff_relative (ht : Selected F t) :
    RelativeOldHistory F ps t u ↔ RelativeHistory ps t u := by
  constructor
  · intro h
    induction h with
    | nil => exact .nil _
    | cons hr hp hs ih =>
      have ha : _ ∈ activePositions _ := (active_iff_selected_trace ht _).mpr
        ((mem_setResidualPositions _ _ _).mp hp)
      exact .cons (hr.active_stepAt ha) (ih (hr.selected ht))
  · intro h
    induction h with
    | nil => exact .nil _
    | cons hr hs ih =>
      have hp : _ ∈ setResidualPositions _ _ := (mem_setResidualPositions _ _ _).mpr
        ((active_iff_selected_trace ht _).mp hr.active)
      exact .cons hr.reductionAt hp (ih (hr.selected ht))

theorem normal_iff_selected_residual_empty (ht : Selected F t) :
    Normal t ↔ setResidualPositions F t = [] := by
  rw [normal_iff_active_empty]
  have hm (p) : p ∈ activePositions t ↔ p ∈ setResidualPositions F t :=
    (active_iff_selected_trace ht p).trans (mem_setResidualPositions F t p).symm
  constructor
  · intro h
    cases he : setResidualPositions F t with
    | nil => rfl
    | cons p ps =>
      have hp : p ∈ setResidualPositions F t := by simp [he]
      have ha := (hm p).mpr hp
      simp [h] at ha
  · intro h
    cases he : activePositions t with
    | nil => rfl
    | cons p ps =>
      have hp : p ∈ activePositions t := by simp [he]
      have ha := (hm p).mp hp
      simp [h] at ha

/-- Completion means relative to F and no residual of F remains. -/
def CompleteOldDevelopment (F : List Path) (t : Term) (ps : List Path) (u : Marked) : Prop :=
  RelativeOldHistory F ps (mark F t) u ∧ setResidualPositions F u = []

theorem completeOld_iff (F : List Path) (t : Term) :
    CompleteOldDevelopment F t ps u ↔ RelativeHistory ps (mark F t) u ∧ Normal u := by
  constructor
  · rintro ⟨hh, he⟩
    have h := (relativeOld_iff_relative (selected_mark F t)).mp hh
    have hs := h.general.selected (selected_mark F t)
    exact ⟨h, (normal_iff_selected_residual_empty hs).mpr he⟩
  · rintro ⟨h, hn⟩
    exact ⟨(relativeOld_iff_relative (selected_mark F t)).mpr h,
      (normal_iff_selected_residual_empty (h.general.selected (selected_mark F t))).mp hn⟩

theorem completeOld_exists (F : List Path) (t : Term) :
    ∃ ps u, CompleteOldDevelopment F t ps u := by
  obtain ⟨ps, u, hh, hn, _⟩ := finite_selection_complete F t
  exact ⟨ps, u, (completeOld_iff F t).mpr ⟨hh, hn⟩⟩

theorem completeOld_independent (h : CompleteOldDevelopment F t ps u)
    (k : CompleteOldDevelopment F t qs v) (r : RedexOcc t) :
    u.erase = v.erase ∧ tracePositions r.val u = tracePositions r.val v := by
  obtain ⟨hh, hn⟩ := (completeOld_iff F t).mp h
  obtain ⟨kh, kn⟩ := (completeOld_iff F t).mp k
  exact finite_developments_independent F t hh hn kh kn r

theorem relativeOld_length_bound (h : RelativeOldHistory F ps (mark F t) u) :
    ps.length + weight (fun _ => 1) u ≤ weight (fun _ => 1) (mark F t) :=
  ((relativeOld_iff_relative (selected_mark F t)).mp h).length_bound _

/-- Strong finiteness for the old-name definition of relativity, including
    arbitrary choices at each real beta step. -/
theorem no_infinite_relativeOld (F : List Path) (t : Term) :
    ¬ ∃ f : Nat → Marked, f 0 = mark F t ∧
      ∀ n, ∃ p, ReductionAt p (f n) (f (n+1)) ∧ p ∈ setResidualPositions F (f n) := by
  rintro ⟨f, hzero, h⟩
  have hs (n) : Selected F (f n) := by
    induction n with
    | zero => rw [hzero]; exact selected_mark F t
    | succ n ih => obtain ⟨p, hp, _⟩ := h n; exact hp.selected ih
  apply no_infinite_development
  refine ⟨f, ?_⟩
  intro n
  obtain ⟨p, hp, hr⟩ := h n
  have ha := (active_iff_selected_trace (hs n) p).mpr
    ((mem_setResidualPositions F (f n) p).mp hr)
  exact (hp.active_stepAt ha).step

end Marked
end Lamping.Lambda
