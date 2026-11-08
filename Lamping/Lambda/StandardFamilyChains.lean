import Lamping.Lambda.CopyCommonExtraction
import Lamping.Lambda.StandardizationGeneral
namespace Lamping.Lambda

/-- A genuine Copy zigzag whose pointed prefixes are ordinary and standard.
Intermediate original family histories need not have been standard. -/
inductive StandardFamilyEq : RedexWithHistory m → RedexWithHistory m → Prop where
  | copy (relation : Copy a b) (sourceAtomic : Atomic a.history) (targetAtomic : Atomic b.history)
      (sourceStandard : Standard a.history) (targetStandard : Standard b.history) : StandardFamilyEq a b
  | symm : StandardFamilyEq a b → StandardFamilyEq b a
  | trans : StandardFamilyEq a b → StandardFamilyEq b c → StandardFamilyEq a c

theorem StandardFamilyEq.properties (chain : StandardFamilyEq a b) :
    Atomic a.history ∧ Standard a.history ∧ Atomic b.history ∧ Standard b.history := by
  induction chain with
  | copy _ ha hb sa sb => exact ⟨ha,sa,hb,sb⟩
  | symm _ ih => exact ⟨ih.2.2.1,ih.2.2.2,ih.1,ih.2.1⟩
  | trans _ _ ih ik => exact ⟨ih.1,ih.2.1,ik.2.2.1,ik.2.2.2⟩

theorem StandardFamilyEq.family (chain : StandardFamilyEq a b) : FamilyEq a b := by
  induction chain with
  | copy relation => exact .copy relation
  | symm _ ih => exact .symm ih
  | trans _ _ ih ik => exact .trans ih ik

/-- Every family zigzag can be represented by genuinely standard ordinary
prefixes. Copy is transported by generated PermEq on both histories, never
by endpoint equality. -/
theorem FamilyEq.standardize {a b : RedexWithHistory m} (family : FamilyEq a b)
    (ρ : ParallelHistory m a.target) (ha : Atomic ρ) (sa : Standard ρ) (pa : PermEq a.history ρ)
    (σ : ParallelHistory m b.target) (hb : Atomic σ) (sb : Standard σ) (pb : PermEq b.history σ) :
    StandardFamilyEq ⟨a.target,ρ,a.redex⟩ ⟨b.target,σ,b.redex⟩ := by
  induction family with
  | copy relation =>
    exact .copy ((relation.history_left ρ pa.symm).history_right σ pb) ha hb sa sb
  | symm relation ih => exact .symm (ih σ hb sb pb ρ ha sa pa)
  | @trans a b c first last ih ik =>
    obtain ⟨middle,atomic,standard,perm⟩ := atomic_standardization_exists b.history
    exact .trans (ih ρ ha sa pa middle atomic standard perm) (ik middle atomic standard perm σ hb sb pb)

theorem FamilyEq.standard_chain {a b : RedexWithHistory m} (family : FamilyEq a b)
    (ha : Atomic a.history) (hb : Atomic b.history)
    (sa : Standard a.history) (sb : Standard b.history) : StandardFamilyEq a b :=
  family.standardize a.history ha sa (.refl _) b.history hb sb (.refl _)

end Lamping.Lambda

