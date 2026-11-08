import Lamping.Lamping.Encoding
namespace Lamping.AG
open Graph Lambda

/-- Structural initial-level bound. This is independent of the yet-to-be-proved
proper-path transparency/independence bundle (AG Exercise 3.5.25). -/
theorem encode_level_lower (t : Term) (n : Nat) : ∀ v,
    ((encode n t).net.label v).sort = .op f → n ≤ ((encode n t).net.label v).index := by
  induction t generalizing n with
  | var k => intro v _; exact Nat.le_refl n
  | lam b ih =>
    dsimp only [encode]
    by_cases used : free b 0
    · rw [dif_pos used]
      rintro (u | v) h
      · exact Nat.le_refl n
      · exact ih n v h
    · rw [dif_neg used]
      rintro ((u | u) | v) h
      · exact Nat.le_refl n
      · cases h
      · exact ih n v h
  | app f a hf ha =>
    simp only [encode]
    rintro ((u | (x | x)) | (v | w)) h
    · exact Nat.le_refl n
    · exact Nat.le_refl n
    · exact Nat.le_refl n
    · exact hf n v h
    · exact Nat.le_trans (Nat.le_succ n) (ha (n+1) w h)

/-- All initial node labels have the source convention: either canonical
Garbage zero or an indexed operator at least the current translation level. -/
theorem encode_label_range (t : Term) (n : Nat) (v : (encode n t).N) :
    (((encode n t).net.label v).sort = .garbage ∧ ((encode n t).net.label v).index = 0) ∨
      ∃ f, ((encode n t).net.label v).sort = .op f ∧ n ≤ ((encode n t).net.label v).index := by
  cases h : ((encode n t).net.label v).sort with
  | garbage => exact .inl ⟨rfl,encode_garbage_zero t n v h⟩
  | op f => exact .inr ⟨f,rfl,encode_level_lower t n v h⟩

end Lamping.AG
