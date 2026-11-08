import Lamping.Lamping.Encoding

namespace Lamping.AG.Readback
open Graph Lambda

/-- Equality is constructed recursively from the actual encoding carriers.
The finite enumeration alone is not used as an equality oracle. -/
def encodedCarrierEquality (n : Nat) : (term : Term) →
    DecidableEq (encode n term).N × DecidableEq (encode n term).W
  | .var _ => ⟨inferInstanceAs (DecidableEq Unit),inferInstanceAs (DecidableEq Empty)⟩
  | .lam body => by
    simp only [encode]
    split
    · letI := (encodedCarrierEquality n body).1
      letI := (encodedCarrierEquality n body).2
      exact ⟨inferInstance,inferInstance⟩
    · letI := (encodedCarrierEquality n body).1
      letI := (encodedCarrierEquality n body).2
      exact ⟨inferInstance,inferInstance⟩
  | .app fn arg => by
    letI := (encodedCarrierEquality n fn).1
    letI := (encodedCarrierEquality n fn).2
    letI := (encodedCarrierEquality (n+1) arg).1
    letI := (encodedCarrierEquality (n+1) arg).2
    change DecidableEq (AppNodes fn arg ⊕ ((encode n fn).N ⊕ (encode (n+1) arg).N)) ×
      DecidableEq ((Empty ⊕ ((encode n fn).W ⊕ (encode (n+1) arg).W)) ⊕ (Boundary fn ⊕ Boundary arg))
    exact ⟨inferInstance,inferInstance⟩

instance encodedNodeEquality (n : Nat) (term : Term) : DecidableEq (encode n term).N :=
  (encodedCarrierEquality n term).1

instance encodedWireEquality (n : Nat) (term : Term) : DecidableEq (encode n term).W :=
  (encodedCarrierEquality n term).2

end Lamping.AG.Readback
