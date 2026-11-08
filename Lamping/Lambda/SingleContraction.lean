import Lamping.Lambda.Histories
namespace Lamping.Lambda
namespace Marked

theorem normal_of_no_active (h : ∀ q, q ∉ activePositions t) : Normal t := by
  apply (normal_iff_no_step t).mpr
  rintro ⟨u,hs⟩
  obtain ⟨p,hp⟩ := hs.at
  exact h p hp.active

/-- A development with exactly one selected occurrence completes in one step.
The premise excludes selected descendants that could be duplicated. -/
theorem StepAt.single_normal (hs : StepAt p t u)
    (only : ∀ q, q ∈ activePositions t → q = p) : Normal u := by
  induction hs with
  | root l b a =>
    have hb : Normal b := normal_of_no_active (by
      intro q hq
      have hh := only (.fn :: .body :: q) (by simp [activePositions,hq])
      cases hh)
    have ha : Normal a := normal_of_no_active (by
      intro q hq
      have hh := only (.arg :: q) (by simp [activePositions,hq])
      cases hh)
    apply normal_subst hb
    intro i; cases i with
    | zero => exact ha
    | succ i => trivial
  | lam hs ih =>
    apply ih
    intro q hq
    exact (List.cons.inj (only (.body :: q) (by simpa [activePositions] using hq))).2
  | appL hs ih =>
    constructor
    · apply ih
      intro q hq
      exact (List.cons.inj (only (.fn :: q) (by simp [activePositions,hq]))).2
    · apply normal_of_no_active
      intro q hq
      have hh := only (.arg :: q) (by simp [activePositions,hq])
      cases hh
  | appR hs ih =>
    constructor
    · apply normal_of_no_active
      intro q hq
      have hh := only (.fn :: q) (by simp [activePositions,hq])
      cases hh
    · apply ih
      intro q hq
      exact (List.cons.inj (only (.arg :: q) (by simp [activePositions,hq]))).2
  | redL hs ih =>
    have hh := only [] (by simp [activePositions])
    cases hh
  | redR hs ih =>
    have hh := only [] (by simp [activePositions])
    cases hh

theorem singleton_complete (hβ : BetaAt t p u) :
    CompleteOldDevelopment [p] t [p] (dev (mark [p] t)) ∧ (dev (mark [p] t)).erase = u := by
  have hr := hβ.redex
  have hp : p ∈ activePositions (mark [p] t) :=
    (active_mark [p] t p).mpr ⟨by simp,(mem_redexPositions t p).mpr hr⟩
  have hβ' : BetaAt (mark [p] t).erase p u := by simpa only [erase_mark] using hβ
  obtain ⟨v,hv,he⟩ := lift_betaAt hp hβ'
  have hn := hv.single_normal (by
    intro q hq
    exact List.mem_singleton.mp ((active_mark [p] t q).mp hq).1)
  have hd : v = dev (mark [p] t) := complete_endpoint ⟨.cons hv.step (.refl _),hn⟩
  subst v
  exact ⟨(completeOld_iff [p] t).mpr ⟨.cons hv (.nil _),hn⟩,he⟩

end Marked

/-- Computable singleton parallel realization: the marked endpoint is dev,
and the actual path list is the given one-step occurrence. -/
def singleContraction (hβ : BetaAt t p u) : ParallelStep [p] t u where
  paths := [p]
  markedTarget := Marked.dev (Marked.mark [p] t)
  complete := (Marked.singleton_complete hβ).1
  target_eq := (Marked.singleton_complete hβ).2

@[simp] theorem singleContraction_paths (hβ : BetaAt t p u) : (singleContraction hβ).paths = [p] := rfl

end Lamping.Lambda
