import Lamping.Lambda.Occurrences
import Lamping.Lambda.Beta

namespace Lamping.Lambda

/-- Ordinary beta normality, distinct from marked-development normality. -/
def BetaNF (t : Term) : Prop := ∀ _r : RedexOcc t, False

/-- Weak beta normalization is a proposition, never a search oracle. -/
def HasNF (t : Term) : Prop := ∃ n : Term, Betas t n ∧ BetaNF n

/-- Finite inspection of the term's actual redex occurrences. -/
def isBetaNormal (t : Term) : Bool := (redexPositions t).isEmpty

theorem betaNF_iff_redexPositions_nil (t : Term) :
    BetaNF t ↔ redexPositions t=[] := by
  constructor
  · intro normal
    cases h : redexPositions t with
    | nil => rfl
    | cons p ps =>
      exfalso
      have member : p∈redexPositions t := by
        rw [h]
        exact List.mem_cons_self
      exact normal ⟨p,(mem_redexPositions t p).mp member⟩
  · intro empty r
    have member : r.val∈redexPositions t := (mem_redexPositions t r.val).mpr r.property
    rw [empty] at member
    exact List.not_mem_nil member

theorem isBetaNormal_eq_true_iff (t : Term) :
    isBetaNormal t=true ↔ BetaNF t := by
  rw [betaNF_iff_redexPositions_nil]
  unfold isBetaNormal
  cases redexPositions t <;> simp

#print axioms BetaNF
#print axioms HasNF
#print axioms isBetaNormal
#print axioms betaNF_iff_redexPositions_nil
#print axioms isBetaNormal_eq_true_iff

end Lamping.Lambda
