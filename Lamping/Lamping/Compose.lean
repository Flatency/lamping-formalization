import Lamping.Lamping.System
namespace Lamping.AG
open Graph

variable {S : Signature} {N M B C W V : Type}

/-- Explicit disjoint union; named boundaries are never identified implicitly. -/
def unionEnd (l : N → Label S) (r : M → Label S) :
    Bij (End S N B W l ⊕ End S M C V r)
      (End S (N ⊕ M) (B ⊕ C) (W ⊕ V) (Sum.elim l r)) where
  toFun
    | .inl (.inl ⟨n,p⟩) => .inl ⟨.inl n,p⟩
    | .inr (.inl ⟨m,p⟩) => .inl ⟨.inr m,p⟩
    | .inl (.inr (.inl b)) => .inr (.inl (.inl b))
    | .inr (.inr (.inl c)) => .inr (.inl (.inr c))
    | .inl (.inr (.inr (w,d))) => .inr (.inr (.inl w,d))
    | .inr (.inr (.inr (v,d))) => .inr (.inr (.inr v,d))
  invFun
    | .inl ⟨.inl n,p⟩ => .inl (.inl ⟨n,p⟩)
    | .inl ⟨.inr m,p⟩ => .inr (.inl ⟨m,p⟩)
    | .inr (.inl (.inl b)) => .inl (.inr (.inl b))
    | .inr (.inl (.inr c)) => .inr (.inr (.inl c))
    | .inr (.inr (.inl w,d)) => .inl (.inr (.inr (w,d)))
    | .inr (.inr (.inr v,d)) => .inr (.inr (.inr (v,d)))
  left_inv := by rintro ((⟨n,p⟩ | (b | ⟨w,d⟩)) | (⟨m,p⟩ | (c | ⟨v,d⟩))) <;> rfl
  right_inv := by rintro (⟨n | m,p⟩ | ((b | c) | ⟨w | v,d⟩)) <;> rfl

variable [FiniteNames N] [FiniteNames M] [FiniteNames B] [FiniteNames C]
  [FiniteNames W] [FiniteNames V]

def unionNet (g : Net S N B W) (h : Net S M C V) :
    Net S (N ⊕ M) (B ⊕ C) (W ⊕ V) where
  label := Sum.elim g.label h.label
  wire := (g.wire.sum h.wire).rename (unionEnd g.label h.label)

theorem union_left (g : Net S N B W) (h : Net S M C V) (e : End S N B W g.label) :
    (unionNet g h).wire (unionEnd g.label h.label (.inl e)) =
      unionEnd g.label h.label (.inl (g.wire e)) :=
  Pairing.rename_apply _ _ _

theorem union_right (g : Net S N B W) (h : Net S M C V) (e : End S M C V h.label) :
    (unionNet g h).wire (unionEnd g.label h.label (.inr e)) =
      unionEnd g.label h.label (.inr (h.wire e)) :=
  Pairing.rename_apply _ _ _

end Lamping.AG
