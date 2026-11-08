import Lamping.Lamping.System
namespace Lamping.AG
open Graph
/-- Connectivity of the internal fragment using segments and transparent vertex crossings.
All internal ends must lie in the one principal-to-principal component; thus no closed
wire-only component may accidentally be deleted as part of a rule match. -/
inductive InternalReach {V : Type} (p : Pairing (Bool ⊕ (V × Bool))) :
    (Bool ⊕ (V × Bool)) → (Bool ⊕ (V × Bool)) → Prop
  | refl (x) : InternalReach p x x
  | segment (x) : InternalReach p x (p x)
  | vertex (v : V) (d : Bool) : InternalReach p (.inr (v,d)) (.inr (v,!d))
  | trans {x y z} : InternalReach p x y → InternalReach p y z → InternalReach p x z

/-- Exactly the two source nodes and a connected subdivided principal wire. -/
def pathPartition (s : Schema) (V : Type) :
    Bij (NodePort signature (Unit ⊕ Unit) s.left.label ⊕ (V × Bool))
      (s.Frontier ⊕ (Bool ⊕ (V × Bool))) where
  toFun
    | .inl ⟨.inl _,.inl _⟩ => .inr (.inl false)
    | .inl ⟨.inr _,.inl _⟩ => .inr (.inl true)
    | .inl ⟨.inl _,.inr a⟩ => .inl (.inl a)
    | .inl ⟨.inr _,.inr a⟩ => .inl (.inr a)
    | .inr vd => .inr (.inr vd)
  invFun
    | .inr (.inl false) => .inl ⟨.inl (),.inl ()⟩
    | .inr (.inl true) => .inl ⟨.inr (),.inl ()⟩
    | .inl (.inl a) => .inl ⟨.inl (),.inr a⟩
    | .inl (.inr a) => .inl ⟨.inr (),.inr a⟩
    | .inr (.inr vd) => .inr vd
  left_inv := by
    rintro (⟨u | u,p⟩ | vd)
    · cases u; cases p with | inl u => cases u; rfl | inr a => rfl
    · cases u; cases p with | inl u => cases u; rfl | inr a => rfl
    · rfl
  right_inv := by rintro ((a | a) | (b | vd)); rfl; rfl; cases b <;> rfl; rfl

section
variable (s : Schema) {K B W V : Type}
variable [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable (kept : K → Label signature)
/-- Source matching certificates describe only the cut fragment. No assertion about
rewrite correctness or target pairing is an input. -/
structure PathSite where
  wire : Pairing (End signature (K ⊕ (Unit ⊕ Unit)) B (W ⊕ V) (ambientLabel s kept))
  internal : Pairing (Bool ⊕ (V × Bool))
  connected : ∀ x, InternalReach internal (.inl false) x
  wiring : ∀ i, wire.rename (fragmentEnd (ambientLabel s kept) (pathPartition s V)) (.inr i) = .inr (internal i)

def PathSite.net (a : PathSite s kept (B := B) (W := W) (V := V)) :
    Net signature (K ⊕ (Unit ⊕ Unit)) B (W ⊕ V) := ⟨ambientLabel s kept,a.wire⟩

theorem PathSite.closed (a : PathSite s kept (B := B) (W := W) (V := V)) : ∀ e i,
    a.net.wire.rename (fragmentEnd a.net.label (pathPartition s V)) (.inl e) ≠ .inr i := by
  intro e i h
  have hh := congrArg (a.wire.rename (fragmentEnd a.net.label (pathPartition s V))) h
  change a.wire.rename (fragmentEnd (ambientLabel s kept) (pathPartition s V)) (a.wire.rename (fragmentEnd (ambientLabel s kept) (pathPartition s V)) (.inl e)) = a.wire.rename (fragmentEnd (ambientLabel s kept) (pathPartition s V)) (.inr i) at hh
  rw [Pairing.involutive,a.wiring] at hh
  cases hh

def PathSite.reduce (a : PathSite s kept (B := B) (W := W) (V := V)) :=
  replace a.net (pathPartition s V) a.closed s.right.net

theorem PathSite.reduce_pairing (a : PathSite s kept (B := B) (W := W) (V := V)) (e) :
    a.reduce.wire (a.reduce.wire e) = e := a.reduce.wire.involutive e

theorem PathSite.reduce_boundary [DecidableEq B] (a : PathSite s kept (B := B) (W := W) (V := V)) :
    a.reduce.boundaryOrder = a.net.boundaryOrder := rfl
end
end Lamping.AG

