import Lamping.Lamping.CompositionalBalance
namespace Lamping.AG
open Graph Lambda
def boundaryDepthAt (level : Nat) {t : Term} : Boundary t → Int
  | .inl _ => (level : Int)
  | .inr _ => (level : Int)+1

def varNet_balance (n k : Nat) : LevelBalance (varNet n k) (boundaryDepthAt n) where
  nodes := fun _ => (n : Int)
  vertices := Empty.elim
  wiring := by
    rintro (⟨u,p⟩ | ((u | x) | ⟨w,d⟩))
    · cases p <;> (first | rfl | simp [endpointDepth,portDepth,boundaryDepthAt,Int.natCast_add,Int.natCast_one])
    · (first | rfl | simp [endpointDepth,portDepth,boundaryDepthAt,Int.natCast_add,Int.natCast_one])
    · (first | rfl | simp [endpointDepth,portDepth,boundaryDepthAt,Int.natCast_add,Int.natCast_one])
    · exact nomatch w

def lambdaUsed_balance (n : Nat) (body : Term) (used : free body 0) :
    LevelBalance (lambdaUsed n body used) (Sum.elim (boundaryDepthAt n) (boundaryDepthAt n)) where
  nodes := fun _ => (n : Int)+1
  vertices := Empty.elim
  wiring := by
    rintro (⟨u,p⟩ | (((u | x) | (v | ⟨k,h⟩)) | ⟨w,d⟩))
    · cases p with | inl u => (first | rfl | simp [endpointDepth,portDepth,boundaryDepthAt,Int.natCast_add,Int.natCast_one]) | inr p => cases p <;> (first | rfl | simp [endpointDepth,portDepth,boundaryDepthAt,Int.natCast_add,Int.natCast_one])
    · (first | rfl | simp [endpointDepth,portDepth,boundaryDepthAt,Int.natCast_add,Int.natCast_one])
    · (first | rfl | simp [endpointDepth,portDepth,boundaryDepthAt,Int.natCast_add,Int.natCast_one])
    · (first | rfl | simp [endpointDepth,portDepth,boundaryDepthAt,Int.natCast_add,Int.natCast_one])
    · cases k <;> (first | rfl | simp [endpointDepth,portDepth,boundaryDepthAt,Int.natCast_add,Int.natCast_one])
    · exact nomatch w

def lambdaUnused_balance (n : Nat) (body : Term) (unused : ¬free body 0) :
    LevelBalance (lambdaUnused n body unused) (Sum.elim (boundaryDepthAt n) (boundaryDepthAt n)) where
  nodes := fun _ => (n : Int)+1
  vertices := Empty.elim
  wiring := by
    rintro (⟨u | v,p⟩ | (((u | x) | (v | ⟨k,h⟩)) | ⟨w,d⟩))
    · cases p with | inl u => (first | rfl | simp [endpointDepth,portDepth,boundaryDepthAt,Int.natCast_add,Int.natCast_one]) | inr p => cases p <;> (first | rfl | simp [endpointDepth,portDepth,boundaryDepthAt,Int.natCast_add,Int.natCast_one])
    · (first | rfl | simp [endpointDepth,portDepth,boundaryDepthAt,Int.natCast_add,Int.natCast_one])
    · (first | rfl | simp [endpointDepth,portDepth,boundaryDepthAt,Int.natCast_add,Int.natCast_one])
    · (first | rfl | simp [endpointDepth,portDepth,boundaryDepthAt,Int.natCast_add,Int.natCast_one])
    · (first | rfl | simp [endpointDepth,portDepth,boundaryDepthAt,Int.natCast_add,Int.natCast_one])
    · cases k with | zero => exact False.elim (unused h) | succ k => (first | rfl | simp [endpointDepth,portDepth,boundaryDepthAt,Int.natCast_add,Int.natCast_one])
    · exact nomatch w

def appPatch_balance (n : Nat) (f arg : Term) :
    LevelBalance (appPatch n f arg) (Sum.elim (boundaryDepthAt n)
      (Sum.elim (boundaryDepthAt n) (boundaryDepthAt (n+1)))) where
  nodes := fun _ => (n : Int)+1
  vertices := Empty.elim
  wiring := by
    rintro (⟨u | (x | x),p⟩ | (((u | x) | ((v | x) | (z | x))) | ⟨w,d⟩))
    · cases p with | inl u => (first | rfl | simp [endpointDepth,portDepth,boundaryDepthAt,Int.natCast_add,Int.natCast_one]) | inr p => cases p <;> (first | rfl | simp [endpointDepth,portDepth,boundaryDepthAt,Int.natCast_add,Int.natCast_one])
    · cases p with
      | inl u => dsimp only [appPatch,appMate]; split <;> (first | rfl | simp [endpointDepth,portDepth,boundaryDepthAt,Int.natCast_add,Int.natCast_one])
      | inr u => (first | rfl | simp [endpointDepth,portDepth,boundaryDepthAt,Int.natCast_add,Int.natCast_one])
    · cases p with | inl u => (first | rfl | simp [endpointDepth,portDepth,boundaryDepthAt,Int.natCast_add,Int.natCast_one]) | inr p => cases p <;> (first | rfl | simp [endpointDepth,portDepth,boundaryDepthAt,Int.natCast_add,Int.natCast_one])
    · (first | rfl | simp [endpointDepth,portDepth,boundaryDepthAt,Int.natCast_add,Int.natCast_one])
    · dsimp only [appPatch,appMate]; split <;> (try split) <;> (first | rfl | simp [endpointDepth,portDepth,boundaryDepthAt,Int.natCast_add,Int.natCast_one])
    · (first | rfl | simp [endpointDepth,portDepth,boundaryDepthAt,Int.natCast_add,Int.natCast_one])
    · dsimp only [appPatch,appMate]; split <;> (first | rfl | simp [endpointDepth,portDepth,boundaryDepthAt,Int.natCast_add,Int.natCast_one])
    · (first | rfl | simp [endpointDepth,portDepth,boundaryDepthAt,Int.natCast_add,Int.natCast_one])
    · (first | rfl | simp [endpointDepth,portDepth,boundaryDepthAt,Int.natCast_add,Int.natCast_one])
    · exact nomatch w

/-- Full integer balance is constructed from actual patches, including
unused-lambda garbage and all free-variable frontiers. No SND is assumed. -/
theorem encode_balance (t : Term) (n : Nat) : Nonempty (LevelBalance (encode n t).net (boundaryDepthAt n)) := by
  induction t generalizing n with
  | var k => exact ⟨varNet_balance n k⟩
  | lam body ih =>
    obtain ⟨child⟩ := ih n
    dsimp only [encode]
    by_cases used : free body 0
    · rw [dif_pos used]
      exact ⟨LevelBalance.plug (lambdaUsed n body used) (encode n body).net _ _
        (lambdaUsed_balance n body used) child⟩
    · rw [dif_neg used]
      exact ⟨LevelBalance.plug (lambdaUnused n body used) (encode n body).net _ _
        (lambdaUnused_balance n body used) child⟩
  | app f arg hf ha =>
    obtain ⟨left⟩ := hf n
    obtain ⟨right⟩ := ha (n+1)
    exact ⟨LevelBalance.plug (appPatch n f arg) (unionNet (encode n f).net (encode (n+1) arg).net) _ _
      (appPatch_balance n f arg)
      (LevelBalance.union (encode n f).net (encode (n+1) arg).net _ _ left right)⟩
end Lamping.AG
