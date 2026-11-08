import Lamping.Lambda.Beta
namespace Lamping.Lambda

/-- A contraction at an actual occurrence; insertion is already scoped locally. -/
def BetaAt (t : Term) (p : Path) (u : Term) : Prop :=
  ∃ b a, subtermAt t p = some (.app (.lam b) a) ∧
    replaceAt t p (contract b a) = some u

theorem BetaAt.beta (h : BetaAt t p u) : Beta t u := by
  obtain ⟨b,a,hl,hr⟩ := h
  induction p generalizing t u with
  | nil =>
    simp only [subtermAt, Option.some.injEq] at hl
    simp only [replaceAt, Option.some.injEq] at hr
    subst t; subst u; exact .root b a
  | cons s p ih =>
    cases t with
    | var i => cases s <;> simp [subtermAt] at hl
    | app f a' =>
      cases s with
      | body => simp [subtermAt] at hl
      | fn =>
        simp only [replaceAt] at hr
        cases hx : replaceAt f p (contract b a) with
        | none => simp [hx] at hr
        | some v =>
          simp only [hx, Option.map_some, Option.some.injEq] at hr
          subst u; exact .fn (ih hl hx)
      | arg =>
        simp only [replaceAt] at hr
        cases hx : replaceAt a' p (contract b a) with
        | none => simp [hx] at hr
        | some v =>
          simp only [hx, Option.map_some, Option.some.injEq] at hr
          subst u; exact .arg (ih hl hx)
    | lam c =>
      cases s with
      | fn => simp [subtermAt] at hl
      | arg => simp [subtermAt] at hl
      | body =>
        simp only [replaceAt] at hr
        cases hx : replaceAt c p (contract b a) with
        | none => simp [hx] at hr
        | some v =>
          simp only [hx, Option.map_some, Option.some.injEq] at hr
          subst u; exact .body (ih hl hx)

theorem beta_iff_betaAt : Beta t u ↔ ∃ p, BetaAt t p u := by
  constructor
  · intro h
    induction h with
    | root b a => exact ⟨[], b, a, rfl, rfl⟩
    | fn h ih =>
      obtain ⟨p,b,a,hl,hr⟩ := ih
      exact ⟨.fn :: p,b,a,hl,by simp only [replaceAt,hr,Option.map_some]⟩
    | arg h ih =>
      obtain ⟨p,b,a,hl,hr⟩ := ih
      exact ⟨.arg :: p,b,a,hl,by simp only [replaceAt,hr,Option.map_some]⟩
    | body h ih =>
      obtain ⟨p,b,a,hl,hr⟩ := ih
      exact ⟨.body :: p,b,a,hl,by simp only [replaceAt,hr,Option.map_some]⟩
  · rintro ⟨p,h⟩; exact h.beta

theorem BetaAt.redex (h : BetaAt t p u) : ∃ v, subtermAt t p = some v ∧ IsRedex v := by
  obtain ⟨b,a,hl,_⟩ := h
  exact ⟨_,hl,True.intro⟩

theorem Betas.scoped (h : Betas t u) (ht : Scoped n t) : Scoped n u := by
  induction h with
  | refl => exact ht
  | cons h _ ih => exact ih (h.scoped ht)

end Lamping.Lambda
