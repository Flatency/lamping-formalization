import Lamping.Lambda.HistoryPreorder
namespace Lamping.Lambda

/-- An actual selected redex event, closed under the genuine family relation.
The prefix is explicit so that residual grids retain the original source. -/
inductive FamilyUsedAt : {t u : Term} → ParallelHistory m t → ParallelHistory t u → RedexWithHistory m → Prop where
  | head {h : ParallelStep F t v} {tail : ParallelHistory v u} {r : RedexOcc t}
      (selected : r.val∈F) (family : FamilyEq ⟨t,pre,r⟩ a) : FamilyUsedAt pre (.cons h tail) a
  | tail {h : ParallelStep F t v} {tail : ParallelHistory v u}
      (used : FamilyUsedAt (pre.append (.single h)) tail a) : FamilyUsedAt pre (.cons h tail) a

/-- AG5.4.1 FAM, as the family-closed predicate on pointed representatives.
Invalid names in a selection list are not events. Repeated names are allowed. -/
def FamilyUsed (ρ : ParallelHistory m t) (a : RedexWithHistory m) : Prop := FamilyUsedAt (.nil m) ρ a
abbrev FAM := @FamilyUsed

def FamilyClosed (X : RedexWithHistory m → Prop) : Prop :=
  ∀ {a b}, FamilyEq a b → X a → X b

def RelativeFamilies (ρ : ParallelHistory m t) (X : RedexWithHistory m → Prop) : Prop :=
  ∀ a, FamilyUsed ρ a → X a

/-- AG5.4.2, making the source's relative-to-X convention explicit. This
asserts neither existence nor termination of developments. -/
def DevelopsFamilies (ρ : ParallelHistory m t) (X : RedexWithHistory m → Prop) : Prop :=
  RelativeFamilies ρ X ∧ ∀ r : RedexOcc t, ¬X ⟨t,ρ,r⟩

theorem FamilyUsedAt.family (used : FamilyUsedAt pre ρ a) (family : FamilyEq a b) :
    FamilyUsedAt pre ρ b := by
  induction used with
  | head selected original => exact .head selected (.trans original family)
  | tail _ ih => exact .tail (ih family)

theorem FamilyUsed.closed (ρ : ParallelHistory m t) : FamilyClosed (FamilyUsed ρ) :=
  fun family used => used.family family

theorem FamilyUsedAt.prefix_permutation (used : FamilyUsedAt pre ρ a) (perm : PermEq pre pre') :
    FamilyUsedAt pre' ρ a := by
  induction used with
  | head selected family =>
    exact .head selected (.trans (.symm (FamilyEq.of_permutation _ _ perm)) family)
  | tail _ ih => exact .tail (ih (perm.append _))

theorem FamilyUsedAt.append_iff (pre : ParallelHistory m t) (ρ : ParallelHistory t u)
    (σ : ParallelHistory u v) (a : RedexWithHistory m) :
    FamilyUsedAt pre (ρ.append σ) a ↔ FamilyUsedAt pre ρ a ∨ FamilyUsedAt (pre.append ρ) σ a := by
  induction ρ with
  | nil =>
    simp only [ParallelHistory.append,ParallelHistory.append_nil]
    constructor
    · exact Or.inr
    · rintro (h|h)
      · cases h
      · exact h
  | cons h tail ih =>
    constructor
    · intro used
      cases used with
      | head selected family => exact .inl (.head selected family)
      | tail used =>
        rcases (ih (pre:=pre.append (.single h)) σ).mp used with first | last
        · exact .inl (.tail first)
        · exact .inr (by simpa only [ParallelHistory.append_assoc,ParallelHistory.single,ParallelHistory.append] using last)
    · rintro (first|last)
      · cases first with
        | head selected family => exact .head selected family
        | tail used => exact .tail ((ih (pre:=pre.append (.single h)) σ).mpr (.inl used))
      · apply FamilyUsedAt.tail
        apply (ih (pre:=pre.append (.single h)) σ).mpr
        exact .inr (by simpa only [ParallelHistory.append_assoc,ParallelHistory.single,ParallelHistory.append] using last)

end Lamping.Lambda
