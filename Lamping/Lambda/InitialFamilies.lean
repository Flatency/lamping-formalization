import Lamping.Lambda.ResidualOrigins
import Lamping.Lambda.PermutationResidual
namespace Lamping.Lambda

/-- Copy preserves and reflects ancestry from a fixed initial redex. Reflection
 uses uniqueness of the middle-term ancestor, not an existence assumption for
 arbitrary newly-created redexes. -/
 theorem Copy.initial_residual {a b : RedexWithHistory m} (h : Copy a b) (R : RedexOcc m) :
     a.history.derivation.Residual R a.redex ↔ b.history.derivation.Residual R b.redex := by
   obtain ⟨τ, hp, hr⟩ := h
   have hpRes := hp.residual R b.redex
   rw [ParallelHistory.derivation_append, Derivation.residual_append] at hpRes
   constructor
   · intro ha
     exact hpRes.mp ⟨a.redex, ha, hr⟩
   · intro hb
     obtain ⟨s, hRs, hsB⟩ := hpRes.mpr hb
     have he := τ.derivation.residual_unique_source s a.redex b.redex hsB hr
     cases he
     exact hRs

 theorem FamilyEq.initial_residual {a b : RedexWithHistory m} (h : FamilyEq a b) (R : RedexOcc m) :
     a.history.derivation.Residual R a.redex ↔ b.history.derivation.Residual R b.redex := by
   induction h with
   | copy h => exact h.initial_residual R
   | symm h ih => exact ih.symm
   | trans h k ih ik => exact ih.trans ik

/-- AG Exercise5.1.14(ii): an initial redex's family consists exactly of its
 genuine residuals along the given history. This does not characterize newly
 created families by a common bare ancestor. -/
 theorem initial_family_iff (R : RedexOcc m) (a : RedexWithHistory m) :
     FamilyEq ⟨m, .nil m, R⟩ a ↔ a.history.derivation.Residual R a.redex := by
   constructor
   · intro hf
     exact (hf.initial_residual R).mp ((Derivation.residual_nil R R).mpr rfl)
   · intro hr
     exact .copy ⟨a.history, .refl _, hr⟩

 theorem initial_families_injective (R S : RedexOcc m) :
     FamilyEq ⟨m, .nil m, R⟩ ⟨m, .nil m, S⟩ ↔ R = S := by
   rw [initial_family_iff]
   exact Derivation.residual_nil R S
end Lamping.Lambda

