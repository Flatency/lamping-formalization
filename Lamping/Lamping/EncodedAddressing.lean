import Lamping.Lamping.CompositionalAddressing
namespace Lamping.AG
open Graph Lambda
def boundaryAddressAt (pre : Path) {t : Term} : Boundary t → Option Path
  | .inl _ => some pre
  | .inr _ => none
private theorem boundaryAddressAt_map {t : Term} (pre : Path) :
    (fun b : Boundary t => (boundaryAddressAt [] b).map (pre++·))=boundaryAddressAt pre := by
  funext b
  cases b <;> simp only [boundaryAddressAt,Option.map_some,Option.map_none,List.append_nil]

def varNet_addressing (n k : Nat) : Addressing (varNet n k) (boundaryAddressAt []) where
  nodes _ := []
  vertices := Empty.elim
  wiring := by
    rintro (⟨u,p⟩ | ((u | x) | ⟨w,d⟩))
    · cases p <;> rfl
    · rfl
    · rfl
    · exact nomatch w

def lambdaUsed_addressing (n : Nat) (body : Term) (used : free body 0) :
    Addressing (lambdaUsed n body used) (Sum.elim (boundaryAddressAt []) (boundaryAddressAt [.body])) where
  nodes _ := []
  vertices := Empty.elim
  wiring := by
    rintro (⟨u,p⟩ | (((u | x) | (v | ⟨k,h⟩)) | ⟨w,d⟩))
    · cases p with | inl u => rfl | inr p => cases p <;> rfl
    · rfl
    · rfl
    · rfl
    · cases k <;> rfl
    · exact nomatch w

def lambdaUnused_addressing (n : Nat) (body : Term) (unused : ¬free body 0) :
    Addressing (lambdaUnused n body unused) (Sum.elim (boundaryAddressAt []) (boundaryAddressAt [.body])) where
  nodes _ := []
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

def appPatch_addressing (n : Nat) (f arg : Term) :
    Addressing (appPatch n f arg) (Sum.elim (boundaryAddressAt [])
      (Sum.elim (boundaryAddressAt [.fn]) (boundaryAddressAt [.arg]))) where
  nodes _ := []
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

/-- The actual recursively glued translation admits explicit finite syntax
addresses on all wires, including both orientations of every seam vertex. -/
theorem encode_addressing (t : Term) (n : Nat) : Nonempty (Addressing (encode n t).net (boundaryAddressAt [])) := by
  induction t generalizing n with
  | var k => exact ⟨varNet_addressing n k⟩
  | lam body ih =>
    obtain ⟨child⟩ := ih n
    have prefixed := child.prefix (encode n body).net (boundaryAddressAt []) [.body]
    rw [boundaryAddressAt_map] at prefixed
    dsimp only [encode]
    by_cases used : free body 0
    · rw [dif_pos used]
      exact ⟨Addressing.plug (lambdaUsed n body used) (encode n body).net _ _
        (lambdaUsed_addressing n body used) prefixed⟩
    · rw [dif_neg used]
      exact ⟨Addressing.plug (lambdaUnused n body used) (encode n body).net _ _
        (lambdaUnused_addressing n body used) prefixed⟩
  | app f arg hf ha =>
    obtain ⟨left⟩ := hf n
    obtain ⟨right⟩ := ha (n+1)
    have leftPrefixed := left.prefix (encode n f).net (boundaryAddressAt []) [.fn]
    have rightPrefixed := right.prefix (encode (n+1) arg).net (boundaryAddressAt []) [.arg]
    rw [boundaryAddressAt_map] at leftPrefixed rightPrefixed
    exact ⟨Addressing.plug (appPatch n f arg) (unionNet (encode n f).net (encode (n+1) arg).net) _ _
      (appPatch_addressing n f arg)
      (Addressing.union (encode n f).net (encode (n+1) arg).net _ _ leftPrefixed rightPrefixed)⟩
end Lamping.AG
