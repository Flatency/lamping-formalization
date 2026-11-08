import Lamping.Lambda.Syntax
import Lamping.Graph.Core
namespace Lamping.AG
open Lambda

/-- De Bruijn free index relative to the current root. -/
def free : Term → Nat → Prop
  | .var i, k => k = i
  | .app f a, k => free f k ∨ free a k
  | .lam b, k => free b (k+1)

def freeDecidable : (t : Term) → (k : Nat) → Decidable (free t k)
  | .var i, k => inferInstanceAs (Decidable (k = i))
  | .app f a, k => @instDecidableOr (free f k) (free a k) (freeDecidable f k) (freeDecidable a k)
  | .lam b, k => freeDecidable b (k+1)
instance (t : Term) (k : Nat) : Decidable (free t k) := freeDecidable t k

def lower : List Nat → List Nat
  | [] => []
  | 0 :: xs => lower xs
  | (k+1) :: xs => k :: lower xs

@[simp] theorem mem_lower (k : Nat) (xs : List Nat) : k ∈ lower xs ↔ k+1 ∈ xs := by
  induction xs with
  | nil => simp [lower]
  | cons x xs ih =>
    cases x with
    | zero => simpa only [lower, List.mem_cons, Nat.succ_ne_zero, false_or] using ih
    | succ x => simp only [lower, List.mem_cons, Nat.add_right_cancel_iff, ih]

def freeList : Term → List Nat
  | .var i => [i]
  | .app f a => freeList f ++ freeList a
  | .lam b => lower (freeList b)

@[simp] theorem mem_freeList (k : Nat) (t : Term) : k ∈ freeList t ↔ free t k := by
  induction t generalizing k with
  | var i => simp [freeList,free]
  | app f a hf ha => simp [freeList,free,hf,ha]
  | lam b hb => simp [freeList,free,hb]

abbrev FV (t : Term) := {k : Nat // free t k}

instance (t : Term) : Graph.FiniteNames (FV t) where
  all := (freeList t).attach.map (fun x => ⟨x.val,(mem_freeList x.val t).mp x.property⟩)
  complete x := by
    apply List.mem_map.mpr
    refine ⟨⟨x.val,(mem_freeList x.val t).mpr x.property⟩, ?_, ?_⟩
    · exact List.mem_attach _ _
    · exact Subtype.ext rfl

theorem scoped_free_lt (ht : Scoped n t) (hk : free t k) : k < n := by
  induction t generalizing n k with
  | var i => simp only [free] at hk; subst k; exact ht
  | app f a hf ha => cases hk with
    | inl h => exact hf ht.1 h
    | inr h => exact ha ht.2 h
  | lam b hb => exact Nat.lt_of_succ_lt_succ (hb ht hk)

theorem scoped_iff_free_lt (t : Term) (n : Nat) : Scoped n t ↔ ∀ k, free t k → k < n := by
  constructor
  · intro ht k hk; exact scoped_free_lt ht hk
  · induction t generalizing n with
    | var i => intro h; exact h i rfl
    | app f a hf ha =>
      intro h
      exact ⟨hf n (fun k hk => h k (.inl hk)), ha n (fun k hk => h k (.inr hk))⟩
    | lam b hb =>
      intro h
      apply hb
      intro k hk
      cases k with
      | zero => omega
      | succ k => exact Nat.succ_lt_succ (h k hk)

theorem closed_no_free (ht : Closed t) (hk : free t k) : False :=
  Nat.not_lt_zero k (scoped_free_lt ht hk)

theorem closed_fv_empty (ht : Closed t) : FV t → False :=
  fun x => closed_no_free ht x.property

end Lamping.AG
