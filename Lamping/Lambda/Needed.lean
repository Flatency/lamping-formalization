import Lamping.Lambda.NormalForms
import Lamping.Lambda.Standardization
import Lamping.Lambda.StandardizationProtection
import Lamping.Lambda.StandardizationExtraction

namespace Lamping.Lambda

/-- Root first, then function before argument; search also beneath lambdas. -/
def loRedex : Term → Option Path
  | .var _ => none
  | .lam b => (loRedex b).map (.body :: ·)
  | .app f a =>
    if IsRedex (.app f a) then some [] else
      match loRedex f with
      | some p => some (.fn :: p)
      | none => (loRedex a).map (.arg :: ·)

/-- A residual of this actual source redex is contracted by every history
ending in ordinary beta normal form. This proposition is not computed. -/
def Needed {t : Term} (r : RedexOcc t) : Prop :=
  ∀ {u : Term} (rho : ParallelHistory t u), BetaNF u → UsedSource rho r

private def LoResultSpec (t : Term) : Option Path → Prop
  | none => BetaNF t
  | some p =>
    (∃ u, subtermAt t p=some u ∧ IsRedex u) ∧
      ∀ s : RedexOcc t, ¬LeftOf s.val p

private theorem noLeftNil (p : Path) : ¬LeftOf p [] := by
  intro earlier
  cases earlier

private theorem lo_result_spec (t : Term) : LoResultSpec t (loRedex t) := by
  induction t with
  | var i =>
    change BetaNF (.var i)
    intro r
    rcases r with ⟨p,valid⟩
    cases p with
    | nil => simp [subtermAt,IsRedex] at valid
    | cons s p => cases s <;> simp [subtermAt] at valid
  | lam b ih =>
    cases hb : loRedex b with
    | none =>
      have normal : BetaNF b := by simpa only [hb,LoResultSpec] using ih
      change LoResultSpec (.lam b) ((loRedex b).map (.body :: ·))
      rw [hb]
      change BetaNF (.lam b)
      intro r
      rcases r with ⟨p,valid⟩
      cases p with
      | nil => simp [subtermAt,IsRedex] at valid
      | cons s p =>
        cases s with
        | fn => simp [subtermAt] at valid
        | arg => simp [subtermAt] at valid
        | body => exact normal ⟨p,by simpa only [subtermAt] using valid⟩
    | some p =>
      have selected : (∃ u,subtermAt b p=some u ∧ IsRedex u) ∧
          ∀ s : RedexOcc b, ¬LeftOf s.val p := by
        simpa only [hb,LoResultSpec] using ih
      change LoResultSpec (.lam b) ((loRedex b).map (.body :: ·))
      rw [hb]
      change (∃ u,subtermAt (.lam b) (.body::p)=some u ∧ IsRedex u) ∧ _
      refine ⟨selected.1,?_⟩
      intro r earlier
      rcases r with ⟨q,valid⟩
      cases q with
      | nil => simp [subtermAt,IsRedex] at valid
      | cons s q =>
        cases s with
        | fn => simp [subtermAt] at valid
        | arg => simp [subtermAt] at valid
        | body =>
          let inner : RedexOcc b := ⟨q,by simpa only [subtermAt] using valid⟩
          cases earlier with
          | child _ earlier => exact selected.2 inner earlier
  | app f a ihf iha =>
    by_cases root : IsRedex (.app f a)
    · simp only [loRedex,if_pos root,LoResultSpec]
      refine ⟨⟨.app f a,rfl,root⟩,?_⟩
      intro r earlier
      exact noLeftNil r.val earlier
    · cases hf : loRedex f with
      | some p =>
        have selected : (∃ u,subtermAt f p=some u ∧ IsRedex u) ∧
            ∀ s : RedexOcc f, ¬LeftOf s.val p := by
          simpa only [hf,LoResultSpec] using ihf
        simp only [loRedex,if_neg root,hf,LoResultSpec]
        refine ⟨selected.1,?_⟩
        intro r earlier
        rcases r with ⟨q,valid⟩
        cases q with
        | nil => exact root (by simpa [subtermAt] using valid)
        | cons s q =>
          cases s with
          | body => simp [subtermAt] at valid
          | arg => cases earlier
          | fn =>
            let inner : RedexOcc f := ⟨q,by simpa only [subtermAt] using valid⟩
            cases earlier with
            | child _ earlier => exact selected.2 inner earlier
      | none =>
        have normalF : BetaNF f := by simpa only [hf,LoResultSpec] using ihf
        cases ha : loRedex a with
        | none =>
          have normalA : BetaNF a := by simpa only [ha,LoResultSpec] using iha
          simp only [loRedex,if_neg root,hf,ha,Option.map_none,LoResultSpec]
          intro r
          rcases r with ⟨q,valid⟩
          cases q with
          | nil => exact root (by simpa [subtermAt] using valid)
          | cons s q =>
            cases s with
            | body => simp [subtermAt] at valid
            | fn => exact normalF ⟨q,by simpa only [subtermAt] using valid⟩
            | arg => exact normalA ⟨q,by simpa only [subtermAt] using valid⟩
        | some p =>
          have selected : (∃ u,subtermAt a p=some u ∧ IsRedex u) ∧
              ∀ s : RedexOcc a, ¬LeftOf s.val p := by
            simpa only [ha,LoResultSpec] using iha
          simp only [loRedex,if_neg root,hf,ha,Option.map_some,LoResultSpec]
          refine ⟨selected.1,?_⟩
          intro r earlier
          rcases r with ⟨q,valid⟩
          cases q with
          | nil => exact root (by simpa [subtermAt] using valid)
          | cons s q =>
            cases s with
            | body => simp [subtermAt] at valid
            | fn => exact normalF ⟨q,by simpa only [subtermAt] using valid⟩
            | arg =>
              let inner : RedexOcc a := ⟨q,by simpa only [subtermAt] using valid⟩
              cases earlier with
              | child _ earlier => exact selected.2 inner earlier

theorem loRedex_none_iff (t : Term) : loRedex t=none ↔ BetaNF t := by
  constructor
  · intro none
    simpa only [none,LoResultSpec] using lo_result_spec t
  · intro normal
    cases hit : loRedex t with
    | none => rfl
    | some p =>
      have selected : (∃ u,subtermAt t p=some u ∧ IsRedex u) ∧
          ∀ s : RedexOcc t, ¬LeftOf s.val p := by
        simpa only [hit,LoResultSpec] using lo_result_spec t
      exact False.elim (normal ⟨p,selected.1⟩)

theorem loRedex_sound {t : Term} {p : Path} (hit : loRedex t=some p) :
    ∃ u,subtermAt t p=some u ∧ IsRedex u := by
  have selected : (∃ u,subtermAt t p=some u ∧ IsRedex u) ∧
      ∀ s : RedexOcc t, ¬LeftOf s.val p := by
    simpa only [hit,LoResultSpec] using lo_result_spec t
  exact selected.1

theorem loRedex_leftmost {t : Term} {p : Path} (hit : loRedex t=some p) :
    ∀ s : RedexOcc t, ¬LeftOf s.val p := by
  have selected : (∃ u,subtermAt t p=some u ∧ IsRedex u) ∧
      ∀ s : RedexOcc t, ¬LeftOf s.val p := by
    simpa only [hit,LoResultSpec] using lo_result_spec t
  exact selected.2

theorem needed_of_leftmost {t : Term} (r : RedexOcc t)
    (leftmost : ∀ s : RedexOcc t, ¬LeftOf s.val r.val) : Needed r := by
  intro u rho normal
  apply Classical.byContradiction
  intro unused
  have right : RightHistory r.val rho := rho.right_of_no_used r (by
    intro s before
    rcases before with same | earlier
    · have equal : s=r := Subtype.ext same
      simpa only [equal] using unused
    · exact False.elim (leftmost s earlier))
  obtain ⟨q,_position,_residual⟩ := rho.derivation.left_survives r right.paths_right
  exact normal q

theorem loRedex_needed {t : Term} {p : Path} (hit : loRedex t=some p) :
    Needed (⟨p,loRedex_sound hit⟩ : RedexOcc t) :=
  needed_of_leftmost ⟨p,loRedex_sound hit⟩ (loRedex_leftmost hit)

#print axioms loRedex
#print axioms Needed
#print axioms loRedex_none_iff
#print axioms loRedex_sound
#print axioms loRedex_leftmost
#print axioms needed_of_leftmost
#print axioms loRedex_needed

end Lamping.Lambda
