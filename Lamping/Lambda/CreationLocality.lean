import Lamping.Lambda.CreationDisjoint
namespace Lamping.Lambda

private def outerCtor : Term → Nat
  | .var _ => 0
  | .app _ _ => 1
  | .lam _ => 2
private def ctorAt (t : Term) (p : Path) : Option Nat := (subtermAt t p).map outerCtor

private theorem ctorAt_root (t : Term) : ctorAt t [] = some (outerCtor t) := by
  cases t <;> rfl

private theorem replace_outer (hr : replaceAt t (s :: p) a = some u) : outerCtor u = outerCtor t := by
  cases t with
  | var i => cases s <;> simp [replaceAt] at hr
  | app f b =>
    cases s with
    | body => simp [replaceAt] at hr
    | fn =>
      cases hf : replaceAt f p a with
      | none => simp [replaceAt, hf] at hr
      | some f' => simp only [replaceAt, hf, Option.map_some, Option.some.injEq] at hr; subst u; rfl
    | arg =>
      cases hb : replaceAt b p a with
      | none => simp [replaceAt, hb] at hr
      | some b' => simp only [replaceAt, hb, Option.map_some, Option.some.injEq] at hr; subst u; rfl
  | lam b =>
    cases s with
    | fn => simp [replaceAt] at hr
    | arg => simp [replaceAt] at hr
    | body =>
      cases hb : replaceAt b p a with
      | none => simp [replaceAt, hb] at hr
      | some b' => simp only [replaceAt, hb, Option.map_some, Option.some.injEq] at hr; subst u; rfl

 theorem DisjointPositions.head_ne (hne : s ≠ r) : DisjointPositions (s :: p) (r :: q) := by
   constructor
   · rintro ⟨x, hx⟩; exact hne (List.cons.inj hx).1.symm
   · rintro ⟨x, hx⟩; exact hne (List.cons.inj hx).1

private theorem replace_ctor_outside (hn : ¬ ∃ x, q = p ++ x)
    (hr : replaceAt t p a = some u) : ctorAt u q = ctorAt t q := by
  induction p generalizing t u q with
  | nil => exact False.elim (hn ⟨q, rfl⟩)
  | cons s p ih =>
    cases q with
    | nil => rw [ctorAt_root, ctorAt_root, replace_outer hr]
    | cons r q =>
      by_cases he : s = r
      · subst r
        have hn' : ¬ ∃ x, q = p ++ x := by
          rintro ⟨x, hx⟩; exact hn ⟨x, congrArg (List.cons s) hx⟩
        cases t with
        | var i => cases s <;> simp [replaceAt] at hr
        | app f b =>
          cases s with
          | body => simp [replaceAt] at hr
          | fn =>
            cases hf : replaceAt f p a with
            | none => simp [replaceAt, hf] at hr
            | some f' =>
              simp only [replaceAt, hf, Option.map_some, Option.some.injEq] at hr
              subst u
              exact ih (q := q) hn' hf
          | arg =>
            cases hb : replaceAt b p a with
            | none => simp [replaceAt, hb] at hr
            | some b' =>
              simp only [replaceAt, hb, Option.map_some, Option.some.injEq] at hr
              subst u
              exact ih (q := q) hn' hb
        | lam b =>
          cases s with
          | fn => simp [replaceAt] at hr
          | arg => simp [replaceAt] at hr
          | body =>
            cases hb : replaceAt b p a with
            | none => simp [replaceAt, hb] at hr
            | some b' =>
              simp only [replaceAt, hb, Option.map_some, Option.some.injEq] at hr
              subst u
              exact ih (q := q) hn' hb
      · exact congrArg (Option.map outerCtor) (replaceAt_disjoint (DisjointPositions.head_ne he) hr)

private theorem prefix_one_extension (he : q ++ [s] = p ++ x)
    (hn : ¬ ∃ y, q = p ++ y) : p = q ++ [s] := by
  induction q generalizing p with
  | nil =>
    cases p with
    | nil => exact False.elim (hn ⟨[], rfl⟩)
    | cons r p =>
      have hh := List.cons.inj he
      cases p with
      | nil => cases hh.1; rfl
      | cons k ps => cases hh.2
  | cons r q ih =>
    cases p with
    | nil => exact False.elim (hn ⟨r :: q, rfl⟩)
    | cons k p =>
      obtain ⟨hr, htail⟩ := List.cons.inj he
      cases hr
      have hn' : ¬ ∃ y, q = p ++ y := by
        rintro ⟨y, hy⟩; exact hn ⟨y, congrArg (List.cons r) hy⟩
      exact congrArg (List.cons r) (ih htail hn')

private theorem redex_ctor_iff (t : Term) (q : Path) :
    (∃ z, subtermAt t q = some z ∧ IsRedex z) ↔
      ctorAt t q = some 1 ∧ ctorAt t (q ++ [.fn]) = some 2 := by
  cases hq : subtermAt t q with
  | none => simp [ctorAt, subtermAt_append, hq]
  | some z =>
    cases z with
    | var i => simp [ctorAt, subtermAt_append, hq, outerCtor, IsRedex, subtermAt]
    | lam b => simp [ctorAt, subtermAt_append, hq, outerCtor, IsRedex, subtermAt]
    | app f a => cases f <;> simp [ctorAt, subtermAt_append, hq, outerCtor, IsRedex, subtermAt]

/-- Every newly exposed redex is either inside the replaced subtree, or is the
 immediate application parent whose function child was replaced. This is an
 actual syntax classification, independent of labels and family theorems. -/
 theorem BetaAt.creation_locality (h : BetaAt t p u)
     (hu : ∃ z, subtermAt u q = some z ∧ IsRedex z)
     (ht : ¬ ∃ z, subtermAt t q = some z ∧ IsRedex z) :
     (∃ x, q = p ++ x) ∨ p = q ++ [.fn] := by
   classical
   by_cases hp : ∃ x, q = p ++ x
   · exact .inl hp
   · by_cases he : p = q ++ [.fn]
     · exact .inr he
     · have hpfn : ¬ ∃ x, q ++ [.fn] = p ++ x := by
         rintro ⟨x, hx⟩; exact he (prefix_one_extension hx hp)
       obtain ⟨b, a, _, hr⟩ := h
       have hc := (redex_ctor_iff u q).mp hu
       have hc1 := replace_ctor_outside hp hr
       have hc2 := replace_ctor_outside hpfn hr
       exact False.elim (ht ((redex_ctor_iff t q).mpr
         ⟨hc1.symm.trans hc.1, hc2.symm.trans hc.2⟩))
end Lamping.Lambda

