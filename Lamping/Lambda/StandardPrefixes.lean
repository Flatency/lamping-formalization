import Lamping.Lambda.Standardization
namespace Lamping.Lambda

theorem DoesNotReturnLeft.prefix (h : DoesNotReturnLeft r (ρ.append σ)) :
    DoesNotReturnLeft r ρ := by
  intro s before v w F pre step suffix decomposition q lo residual
  apply h s before pre step (suffix.append σ) ?_ q lo residual
  rw [decomposition,ParallelHistory.append_assoc]
  rfl

/-- Restricting a genuinely standard history to an actual initial segment
preserves standardness, with its original selected LO witnesses. -/
theorem Standard.prefix {ρ : ParallelHistory t u} {σ : ParallelHistory u v}
    (h : Standard (ρ.append σ)) : Standard ρ := by
  induction ρ with
  | nil => exact .nil _
  | cons first rest ih =>
    cases h with
    | empty h ht => exact .empty h (ih ht)
    | cons _ r lo noReturn ht => exact .cons first r lo noReturn.prefix (ih ht)

theorem Standard.suffix {ρ : ParallelHistory t u} {σ : ParallelHistory u v}
    (h : Standard (ρ.append σ)) : Standard σ := by
  induction ρ with
  | nil => exact h
  | cons first rest ih =>
    cases h with
    | empty _ ht => exact ih ht
    | cons _ _ _ _ ht => exact ih ht

end Lamping.Lambda
