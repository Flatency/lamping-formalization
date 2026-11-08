import Lamping.Lambda.Extraction
namespace Lamping.Lambda
 theorem BetaHistory.atomic (h : BetaHistory ps t u) :
     ∃ ρ : ParallelHistory t u, Atomic ρ ∧ ρ.derivation.paths = ps := by
   induction h with
   | nil t => exact ⟨.nil t, .nil t, rfl⟩
   | @cons t p u ps v hb hs ih =>
     obtain ⟨ρ, hρ, he⟩ := ih
     refine ⟨.cons (singleContraction hb) ρ, .cons hb hρ, ?_⟩
     change [p] ++ ρ.derivation.paths = p :: ps
     rw [he]; rfl

 theorem Derivation.atomic (h : Derivation t u) :
     ∃ ρ : ParallelHistory t u, Atomic ρ ∧ ρ.derivation = h := by
   obtain ⟨ρ, hρ, he⟩ := h.valid.atomic
   exact ⟨ρ, hρ, Derivation.ext he⟩

/-- A nonempty ordinary run has a last actual contraction, so it determines a
 redex with history; the empty extraction normal form is not used as a family
 representative. -/
 theorem Atomic.last {ρ : ParallelHistory t u} (ha : Atomic ρ) (hp : 0 < ρ.length) :
     ∃ (v : Term) (p : Path) (pre : ParallelHistory t v) (hb : BetaAt v p u),
       Atomic pre ∧ ρ = pre.append (.single (singleContraction hb)) := by
   induction ha with
   | nil => exact False.elim (Nat.lt_irrefl 0 hp)
   | @cons t p v target σ hb ha ih =>
     cases σ with
     | nil => exact ⟨_, _, .nil _, hb, .nil _, rfl⟩
     | cons next tail =>
       obtain ⟨z, q, pre, last, hpre, he⟩ := ih (by simp only [ParallelHistory.length]; omega)
       exact ⟨z, q, .cons (singleContraction hb) pre, last, .cons hb hpre,
         by rw [he]; rfl⟩
end Lamping.Lambda



