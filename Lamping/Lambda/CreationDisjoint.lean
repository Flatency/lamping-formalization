import Lamping.Lambda.ContextualBeta
import Lamping.Lambda.Extraction
namespace Lamping.Lambda

 theorem DisjointPositions.child (h : DisjointPositions (s :: p) (s :: q)) :
     DisjointPositions p q := by
   constructor
   · rintro ⟨r, hr⟩; exact h.1 ⟨r, congrArg (List.cons s) hr⟩
   · rintro ⟨r, hr⟩; exact h.2 ⟨r, congrArg (List.cons s) hr⟩

/-- A real structural replacement preserves every disjoint subexpression,
 including its binder indices and its redex/non-redex shape. -/
 theorem replaceAt_disjoint (h : DisjointPositions p q)
     (hr : replaceAt t p a = some u) : subtermAt u q = subtermAt t q := by
   induction p generalizing t u q with
   | nil => exact False.elim (h.1 ⟨q, rfl⟩)
   | cons s p ih =>
     cases q with
     | nil => exact False.elim (h.2 ⟨s :: p, rfl⟩)
     | cons r q =>
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
             cases r with
             | fn => exact ih (q := q) h.child hf
             | arg => rfl
             | body => rfl
         | arg =>
           cases hb : replaceAt b p a with
           | none => simp [replaceAt, hb] at hr
           | some b' =>
             simp only [replaceAt, hb, Option.map_some, Option.some.injEq] at hr
             subst u
             cases r with
             | arg => exact ih (q := q) h.child hb
             | fn => rfl
             | body => rfl
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
             cases r with
             | body => exact ih (q := q) h.child hb
             | fn => rfl
             | arg => rfl

 theorem BetaAt.disjoint_subterm (hb : BetaAt t p u) (h : DisjointPositions p q) :
     subtermAt u q = subtermAt t q := by
   obtain ⟨b, a, _, hr⟩ := hb
   exact replaceAt_disjoint h hr

/-- In particular a contraction cannot create a redex in a disjoint subtree.
 Upward/function-parent and contractum cases remain separate obligations. -/
 theorem BetaAt.disjoint_redex_iff (hb : BetaAt t p u) (h : DisjointPositions p q) :
     (∃ z, subtermAt u q = some z ∧ IsRedex z) ↔
       ∃ z, subtermAt t q = some z ∧ IsRedex z := by
   rw [hb.disjoint_subterm h]
end Lamping.Lambda

