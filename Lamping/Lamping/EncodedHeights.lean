import Lamping.Lamping.CompositionalHeights
namespace Lamping.AG
open Graph Lambda
def boundaryHeightAt (level : Nat) {t : Term} : Boundary t → Option Nat
  | .inl _ => some level
  | .inr _ => none

def varNet_heighting (n k : Nat) : Heighting (varNet n k) (boundaryHeightAt n) where
  vertices := Empty.elim
  wiring := by
    rintro (⟨u,p⟩ | ((u | x) | ⟨w,d⟩))
    · cases p <;> rfl
    · rfl
    · rfl
    · exact nomatch w

def lambdaUsed_heighting (n : Nat) (body : Term) (used : free body 0) :
    Heighting (lambdaUsed n body used) (Sum.elim (boundaryHeightAt n) (boundaryHeightAt n)) where
  vertices := Empty.elim
  wiring := by
    rintro (⟨u,p⟩ | (((u | x) | (v | ⟨k,h⟩)) | ⟨w,d⟩))
    · cases p with | inl u => rfl | inr p => cases p <;> rfl
    · rfl
    · rfl
    · rfl
    · cases k <;> rfl
    · exact nomatch w

def lambdaUnused_heighting (n : Nat) (body : Term) (unused : ¬free body 0) :
    Heighting (lambdaUnused n body unused) (Sum.elim (boundaryHeightAt n) (boundaryHeightAt n)) where
  vertices := Empty.elim
  wiring := by
    rintro (⟨u | v,p⟩ | (((u | x) | (v | ⟨k,h⟩)) | ⟨w,d⟩))
    · cases p with | inl u => rfl | inr p => cases p <;> rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · cases k with | zero => exact False.elim (unused h) | succ k => rfl
    · exact nomatch w

def appPatch_heighting (n : Nat) (f arg : Term) :
    Heighting (appPatch n f arg) (Sum.elim (boundaryHeightAt n)
      (Sum.elim (boundaryHeightAt n) (boundaryHeightAt (n+1)))) where
  vertices := Empty.elim
  wiring := by
    rintro (⟨u | (x | x),p⟩ | (((u | x) | ((v | x) | (z | x))) | ⟨w,d⟩))
    · cases p with | inl u => rfl | inr p => cases p <;> rfl
    · cases p with
      | inl u => dsimp only [appPatch,appMate]; split <;> rfl
      | inr u => rfl
    · cases p with | inl u => rfl | inr p => cases p <;> rfl
    · rfl
    · dsimp only [appPatch,appMate]; split <;> (try split) <;> rfl
    · rfl
    · dsimp only [appPatch,appMate]; split <;> rfl
    · rfl
    · rfl
    · exact nomatch w

/-- Wire heights are constructed from actual initial patches and transparent
seams. No path-level bound or Independence premise is needed. -/
theorem encode_heighting (t : Term) (n : Nat) : Nonempty (Heighting (encode n t).net (boundaryHeightAt n)) := by
  induction t generalizing n with
  | var k => exact ⟨varNet_heighting n k⟩
  | lam body ih =>
    obtain ⟨child⟩ := ih n
    dsimp only [encode]
    by_cases used : free body 0
    · rw [dif_pos used]
      exact ⟨Heighting.plug (lambdaUsed n body used) (encode n body).net _ _
        (lambdaUsed_heighting n body used) child⟩
    · rw [dif_neg used]
      exact ⟨Heighting.plug (lambdaUnused n body used) (encode n body).net _ _
        (lambdaUnused_heighting n body used) child⟩
  | app f arg hf ha =>
    obtain ⟨left⟩ := hf n
    obtain ⟨right⟩ := ha (n+1)
    exact ⟨Heighting.plug (appPatch n f arg) (unionNet (encode n f).net (encode (n+1) arg).net) _ _
      (appPatch_heighting n f arg)
      (Heighting.union (encode n f).net (encode (n+1) arg).net _ _ left right)⟩
end Lamping.AG
