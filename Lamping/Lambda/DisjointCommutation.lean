import Lamping.Lambda.CreationDisjointResidual
namespace Lamping.Lambda

/-- Disjoint replacements commute at their original paths, with an actual
 common term and successful replacements in both orders. -/
 theorem replaceAt_disjoint_square (hd : DisjointPositions p q)
     (hp : replaceAt t p a = some u) (hq : replaceAt t q b = some v) :
     ∃ w, replaceAt u q b = some w ∧ replaceAt v p a = some w := by
   induction p generalizing t u v q with
   | nil => exact False.elim (hd.1 ⟨q, rfl⟩)
   | cons s p ih =>
     cases q with
     | nil => exact False.elim (hd.2 ⟨s :: p, rfl⟩)
     | cons r q =>
       cases t with
       | var i => cases s <;> simp [replaceAt] at hp
       | lam c =>
         cases s with
         | fn => simp [replaceAt] at hp
         | arg => simp [replaceAt] at hp
         | body =>
           cases r with
           | fn => simp [replaceAt] at hq
           | arg => simp [replaceAt] at hq
           | body =>
             cases h1 : replaceAt c p a with
             | none => simp [replaceAt, h1] at hp
             | some c1 =>
               simp only [replaceAt, h1, Option.map_some, Option.some.injEq] at hp
               subst u
               cases h2 : replaceAt c q b with
               | none => simp [replaceAt, h2] at hq
               | some c2 =>
                 simp only [replaceAt, h2, Option.map_some, Option.some.injEq] at hq
                 subst v
                 obtain ⟨w, hw1, hw2⟩ := ih hd.child h1 h2
                 exact ⟨.lam w, by simp [replaceAt, hw1], by simp [replaceAt, hw2]⟩
       | app f c =>
         cases s with
         | body => simp [replaceAt] at hp
         | fn =>
           cases h1 : replaceAt f p a with
           | none => simp [replaceAt, h1] at hp
           | some f1 =>
             simp only [replaceAt, h1, Option.map_some, Option.some.injEq] at hp
             subst u
             cases r with
             | body => simp [replaceAt] at hq
             | fn =>
               cases h2 : replaceAt f q b with
               | none => simp [replaceAt, h2] at hq
               | some f2 =>
                 simp only [replaceAt, h2, Option.map_some, Option.some.injEq] at hq
                 subst v
                 obtain ⟨w, hw1, hw2⟩ := ih hd.child h1 h2
                 exact ⟨.app w c, by simp [replaceAt, hw1], by simp [replaceAt, hw2]⟩
             | arg =>
               cases h2 : replaceAt c q b with
               | none => simp [replaceAt, h2] at hq
               | some c2 =>
                 simp only [replaceAt, h2, Option.map_some, Option.some.injEq] at hq
                 subst v
                 exact ⟨.app f1 c2, by simp [replaceAt, h2], by simp [replaceAt, h1]⟩
         | arg =>
           cases h1 : replaceAt c p a with
           | none => simp [replaceAt, h1] at hp
           | some c1 =>
             simp only [replaceAt, h1, Option.map_some, Option.some.injEq] at hp
             subst u
             cases r with
             | body => simp [replaceAt] at hq
             | arg =>
               cases h2 : replaceAt c q b with
               | none => simp [replaceAt, h2] at hq
               | some c2 =>
                 simp only [replaceAt, h2, Option.map_some, Option.some.injEq] at hq
                 subst v
                 obtain ⟨w, hw1, hw2⟩ := ih hd.child h1 h2
                 exact ⟨.app f w, by simp [replaceAt, hw1], by simp [replaceAt, hw2]⟩
             | fn =>
               cases h2 : replaceAt f q b with
               | none => simp [replaceAt, h2] at hq
               | some f2 =>
                 simp only [replaceAt, h2, Option.map_some, Option.some.injEq] at hq
                 subst v
                 exact ⟨.app f2 c1, by simp [replaceAt, h2], by simp [replaceAt, h1]⟩

 theorem BetaAt.disjoint_square (hR : BetaAt t p u) (hS : BetaAt t q v)
     (hd : DisjointPositions p q) : ∃ w, BetaAt u q w ∧ BetaAt v p w := by
   obtain ⟨rb, ra, hrl, hrr⟩ := hR
   obtain ⟨sb, sa, hsl, hsr⟩ := hS
   obtain ⟨w, hw1, hw2⟩ := replaceAt_disjoint_square hd hrr hsr
   refine ⟨w, ⟨sb, sa, ?_, hw1⟩, ⟨rb, ra, ?_, hw2⟩⟩
   · rw [replaceAt_disjoint hd hrr]; exact hsl
   · rw [replaceAt_disjoint ⟨hd.2, hd.1⟩ hsr]; exact hrl
/-- Same-position old redexes in a disjoint subtree are actual residuals. -/
 theorem BetaAt.disjoint_residual (h : BetaAt t p u)
     (r : RedexOcc t) (s : RedexOcc u) (he : r.val = s.val)
     (hd : DisjointPositions p s.val) : (singleContraction h).derivation.Residual r s := by
   obtain ⟨r', hr', hh⟩ := h.disjoint_initial_ancestor s hd
   have hrr : r' = r := Subtype.ext (hr'.trans he.symm)
   cases hrr
   exact hh
end Lamping.Lambda

