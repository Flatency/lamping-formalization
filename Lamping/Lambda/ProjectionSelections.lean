import Lamping.Lambda.ProjectionFamilies
import Lamping.Lambda.ContextualResiduals
import Lamping.Lambda.ResidualComposition
import Lamping.Lambda.SingletonPaths
import Lamping.Lambda.FiniteSelectionReindex
namespace Lamping.Lambda

theorem ParallelStep.mem_residualSet_iff (h : ParallelStep F t u)
    (valid : ∀ p ∈ G, ∃ z, subtermAt t p = some z ∧ IsRedex z) (s : RedexOcc u) :
    s.val ∈ h.residualSet G ↔
      ∃ r : RedexOcc t, r.val ∈ G ∧ h.derivation.Residual r s := by
  constructor
  · intro hs
    obtain ⟨p, hp, htrace⟩ := (Marked.mem_setResidualPositions G h.markedTarget s.val).mp hs
    exact ⟨⟨p, valid p hp⟩, hp, (h.residual_iff _ s).mpr htrace⟩
  · rintro ⟨r, hr, hs⟩
    exact (Marked.mem_setResidualPositions G h.markedTarget s.val).mpr
      ⟨r.val, hr, (h.residual_iff r s).mp hs⟩

theorem ParallelStep.residualSet_valid (h : ParallelStep F t u) (p : Path)
    (hp : p ∈ h.residualSet G) : ∃ z, subtermAt u p = some z ∧ IsRedex z := by
  have valid := ((Marked.completeOld_iff F t).mp h.complete).1.general.valid (Marked.valid_mark F t)
  have hs := Marked.setResidualPositions_sound valid hp
  rw [h.target_eq] at hs
  exact hs

/-- The selected set on the last vertical side of an actual tile row is the
 true image of the initial selected set along the top horizontal history. -/
theorem StepProjection.final_selection {step : ParallelStep F t u}
    {σ : ParallelHistory t v} {σ' : ParallelHistory u w} {last : ParallelStep G v w}
    (row : StepProjection step σ σ' last)
    (valid : ∀ p ∈ F, ∃ z, subtermAt t p = some z ∧ IsRedex z) (s : RedexOcc v) :
    s.val ∈ G ↔ ∃ r : RedexOcc t, r.val ∈ F ∧ σ.derivation.Residual r s := by
  induction row with
  | nil step =>
    constructor
    · intro hs; exact ⟨s, hs, (Derivation.residual_nil s s).mpr rfl⟩
    · rintro ⟨r, hr, hs⟩
      have he := (Derivation.residual_nil r s).mp hs
      cases he
      exact hr
  | cons sq tail ih =>
    rw [ih (fun p hp => sq.second.residualSet_valid p hp)]
    constructor
    · rintro ⟨middle, hm, hs⟩
      obtain ⟨r, hr, hfirst⟩ := (sq.second.mem_residualSet_iff valid middle).mp hm
      exact ⟨r, hr, (Derivation.residual_append _ _ r s).mpr ⟨middle, hfirst, hs⟩⟩
    · rintro ⟨r, hr, hs⟩
      obtain ⟨middle, hfirst, hrest⟩ := (Derivation.residual_append _ _ r s).mp hs
      exact ⟨middle, (sq.second.mem_residualSet_iff valid middle).mpr ⟨r, hr, hfirst⟩, hrest⟩

private theorem paths_prefix_decompose (ps : List Path)
    (inside : ∀ p ∈ ps, ∃ q, p = site ++ q) :
    ∃ qs : List Path, ps = qs.map (fun p => site ++ p) := by
  induction ps with
  | nil => exact ⟨[], rfl⟩
  | cons p ps ih =>
    obtain ⟨q, hq⟩ := inside p (List.mem_cons_self)
    obtain ⟨qs, hqs⟩ := ih (fun p hp => inside p (List.mem_cons_of_mem _ hp))
    exact ⟨q :: qs, by simp only [List.map_cons, hq, hqs]⟩

theorem Internal.paths_prefix {ρ : ParallelHistory t u} (inside : Internal site ρ) :
    ∃ ps : List Path, ρ.derivation.paths = ps.map (fun p => site ++ p) :=
  paths_prefix_decompose ρ.derivation.paths inside

theorem ParallelHistory.residual_outside_internal (ρ : ParallelHistory t u) (inside : Internal site ρ)
    (r : RedexOcc t) (s : RedexOcc u) (outside : ¬ ∃ q, r.val = site ++ q) :
    ρ.derivation.Residual r s ↔ r.val = s.val := by
  obtain ⟨ps, hps⟩ := inside.paths_prefix
  obtain ⟨v, hv, _⟩ := ρ.derivation.tracked
  have hh : Marked.History (ps.map (fun p => site ++ p)) (Marked.mark [] t) v := by
    simpa only [hps] using hv
  have he := hh.trace_fixed_outside (r := r.val) (by
    intro q hq
    exact outside ⟨q, ((Marked.initial_residual [] t r (site ++ q)).mp hq).symm⟩)
  rw [Derivation.residual_iff_tracking _ hv, he, Marked.initial_residual]
  exact eq_comm

theorem ParallelHistory.residual_outside_internal_exists (ρ : ParallelHistory t u) (inside : Internal site ρ)
    (r : RedexOcc t) (outside : ¬ ∃ q, r.val = site ++ q) :
    ∃ s : RedexOcc u, s.val = r.val ∧ ρ.derivation.Residual r s := by
  obtain ⟨ps, hps⟩ := inside.paths_prefix
  obtain ⟨v, hv, hev⟩ := ρ.derivation.tracked
  have hh : Marked.History (ps.map (fun p => site ++ p)) (Marked.mark [] t) v := by
    simpa only [hps] using hv
  have he := hh.trace_fixed_outside (r := r.val) (by
    intro q hq
    exact outside ⟨q, ((Marked.initial_residual [] t r (site ++ q)).mp hq).symm⟩)
  have ht : r.val ∈ Marked.tracePositions r.val v := by
    rw [he]
    exact (Marked.initial_residual [] t r r.val).mpr rfl
  have valid := hv.valid (Marked.valid_mark [] t)
  have hr := Marked.tracePositions_sound valid ht
  rw [hev] at hr
  refine ⟨⟨r.val, hr⟩, rfl, ?_⟩
  exact ⟨v, hv, hev, ht⟩

/-- In the disjoint/function-part cases every vertical selection remains
 the single unchanged original redex, even for arbitrary chosen schedules. -/
theorem StepProjection.final_selection_outside
    {R : BetaAt t p u} {σ : ParallelHistory t v} {σ' : ParallelHistory u w}
    {last : ParallelStep G v w} (row : StepProjection (singleContraction R) σ σ' last)
    (inside : Internal site σ) (outside : ¬ ∃ q, p = site ++ q) (s : RedexOcc v) :
    s.val ∈ G ↔ s.val = p := by
  rw [row.final_selection (by intro q hq; cases List.mem_singleton.mp hq; exact R.redex)]
  constructor
  · rintro ⟨r, hr, hs⟩
    have hp : r.val = p := List.mem_singleton.mp hr
    have hn : ¬ ∃ q, r.val = site ++ q := by simpa only [hp] using outside
    exact ((σ.residual_outside_internal inside r s hn).mp hs).symm.trans hp
  · intro hs
    let r : RedexOcc t := ⟨p, R.redex⟩
    exact ⟨r, List.mem_singleton_self _,
      (σ.residual_outside_internal inside r s outside).mpr hs.symm⟩

theorem StepProjection.final_selection_valid {step : ParallelStep F t u}
    {σ : ParallelHistory t v} {σ' : ParallelHistory u w} {last : ParallelStep G v w}
    (row : StepProjection step σ σ' last)
    (valid : ∀ p ∈ F, ∃ z, subtermAt t p = some z ∧ IsRedex z) :
    ∀ p ∈ G, ∃ z, subtermAt v p = some z ∧ IsRedex z := by
  induction row with
  | nil => exact valid
  | cons sq tail ih => exact ih (fun p hp => sq.second.residualSet_valid p hp)

theorem StepProjection.final_selection_outside_members
    {R : BetaAt t p u} {σ : ParallelHistory t v} {σ' : ParallelHistory u w}
    {last : ParallelStep G v w} (row : StepProjection (singleContraction R) σ σ' last)
    (inside : Internal site σ) (outside : ¬ ∃ q, p = site ++ q) (z : Path) :
    z ∈ G ↔ z = p := by
  constructor
  · intro hz
    have hr := row.final_selection_valid (by intro q hq; cases List.mem_singleton.mp hq; exact R.redex) z hz
    exact (row.final_selection_outside inside outside ⟨z, hr⟩).mp hz
  · intro hz
    subst z
    obtain ⟨s, hs, _⟩ := σ.residual_outside_internal_exists inside ⟨p, R.redex⟩ outside
    have hm := (row.final_selection_outside inside outside s).mpr hs
    simpa only [hs] using hm

theorem StepProjection.final_vertical_singleton
    {R : BetaAt t p u} {σ : ParallelHistory t v} {σ' : ParallelHistory u w}
    {last : ParallelStep G v w} (row : StepProjection (singleContraction R) σ σ' last)
    (inside : Internal site σ) (outside : ¬ ∃ q, p = site ++ q) :
    last.paths = [p] ∧ BetaAt v p w := by
  let last' := last.reindex [p] (fun z => (row.final_selection_outside_members inside outside z).trans List.mem_singleton.symm)
  obtain ⟨s, hs, _⟩ := σ.residual_outside_internal_exists inside ⟨p, R.redex⟩ outside
  have hp : last.paths = [p] := last'.singleton_paths s hs
  refine ⟨hp, ?_⟩
  have hv := last.derivation.valid
  change BetaHistory last.paths v w at hv
  rw [hp] at hv
  cases hv with
  | cons h hs => cases hs; exact h
end Lamping.Lambda
