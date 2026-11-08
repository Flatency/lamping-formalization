import Lamping.Lambda.Permutation
namespace Lamping.Lambda

/-- The source M₀ is an index, shared by every history in a family comparison. -/
structure RedexWithHistory (source : Term) where
  target : Term
  history : ParallelHistory source target
  redex : RedexOcc target

/-- AG5.1.7: extension modulo generated permutation, with an actual old-redex
 residual along the extension. A common target is insufficient. -/
def Copy (a b : RedexWithHistory m) : Prop :=
  ∃ τ : ParallelHistory a.target b.target,
    PermEq (a.history.append τ) b.history ∧
      τ.derivation.Residual a.redex b.redex

namespace Copy
 theorem refl (a : RedexWithHistory m) : Copy a a := by
   refine ⟨.nil _, ?_, ?_⟩
   · rw [ParallelHistory.append_nil]; exact .refl _
   · exact (Derivation.residual_nil _ _).mpr rfl

 theorem history_left {a b : RedexWithHistory m}
     (ρ : ParallelHistory m a.target) (h : PermEq ρ a.history) (hc : Copy a b) :
     Copy ⟨a.target, ρ, a.redex⟩ b := by
   obtain ⟨τ, hp, hr⟩ := hc
   exact ⟨τ, .trans (h.append τ) hp, hr⟩

 theorem history_right {a b : RedexWithHistory m}
     (σ : ParallelHistory m b.target) (h : PermEq b.history σ) (hc : Copy a b) :
     Copy a ⟨b.target, σ, b.redex⟩ := by
   obtain ⟨τ, hp, hr⟩ := hc
   exact ⟨τ, .trans hp h, hr⟩
end Copy

/-- AG5.1.8: the finite symmetric transitive closure of Copy. Reflexivity is
 inherited from Copy; it does not identify arbitrary histories. -/
inductive FamilyEq : RedexWithHistory m → RedexWithHistory m → Prop where
  | copy : Copy a b → FamilyEq a b
  | symm : FamilyEq a b → FamilyEq b a
  | trans : FamilyEq a b → FamilyEq b c → FamilyEq a c

namespace FamilyEq
 theorem refl (a : RedexWithHistory m) : FamilyEq a a := .copy (Copy.refl a)
 theorem equivalence : Equivalence (@FamilyEq m) := ⟨refl, symm, trans⟩

 theorem of_permutation (a : RedexWithHistory m) (σ : ParallelHistory m a.target)
     (h : PermEq a.history σ) : FamilyEq a ⟨a.target, σ, a.redex⟩ := by
   apply FamilyEq.copy
   exact Copy.history_right σ h (Copy.refl a)

 theorem least (R : RedexWithHistory m → RedexWithHistory m → Prop)
     (hc : ∀ {a b}, Copy a b → R a b)
     (hs : ∀ {a b}, R a b → R b a)
     (ht : ∀ {a b c}, R a b → R b c → R a c)
     (h : FamilyEq a b) : R a b := by
   induction h with
   | copy h => exact hc h
   | symm _ ih => exact hs ih
   | trans _ _ ih ik => exact ht ih ik
end FamilyEq

def familySetoid (m : Term) : Setoid (RedexWithHistory m) where
  r := FamilyEq
  iseqv := FamilyEq.equivalence

abbrev FamilyClass (m : Term) := Quotient (familySetoid m)
end Lamping.Lambda
