import Lamping.Lamping.GlobalPathInvariants
namespace Lamping.AG
open Graph

/-- Geometric edge potential. Control bases are independent of their rewrite
indices; negative potentials are allowed after control commutations. -/
def portDepth (index : Nat) (kind : Kind) (base : Int) : Port kind → Int :=
  match kind with
  | .op .app => fun p => match p with | .inr true => (index : Int)+1 | _ => index
  | .op .lam => fun p => match p with | .inr false => (index : Int)+1 | _ => index
  | .op .fan => fun _ => base
  | .op .cro => fun p => match p with | .inl _ => base+1 | .inr _ => base
  | .op .bra => fun p => match p with | .inl _ => base | .inr _ => base+1
  | .garbage => fun _ => base

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable (g : Net signature N B W)

def endpointDepth (nodes : N → Int) (boundary : B → Int) (vertices : W → Int) : Endpoint g → Int
  | .inl ⟨node,p⟩ => portDepth (g.label node).index (g.label node).sort (nodes node) p
  | .inr (.inl b) => boundary b
  | .inr (.inr (w,_)) => vertices w

/-- A wiring invariant with explicit potential witnesses, not a correctness
certificate. Garbage ports carry their own unconstrained node base. -/
structure LevelBalance (boundary : B → Int) where
  nodes : N → Int
  vertices : W → Int
  wiring : ∀ e,endpointDepth g nodes boundary vertices (g.wire e)=endpointDepth g nodes boundary vertices e
end

private theorem proper_principal_depth (actual : Label signature) (op : Op) (index : Nat) (base : Int)
    (p : Port actual.sort) (lab : actual=label op index) (proper : op=.app ∨op=.lam)
    (principal : HEq p (Sum.inl () : Port (.op op))) :
    portDepth actual.index actual.sort base p=(index : Int) := by
  subst actual
  have equal : p=.inl () := eq_of_heq principal
  subst p
  rcases proper with same | same <;> subst op <;> rfl

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {boundary : B → Int}

/-- Different-index proper principal ports cannot be directly wired in a
balanced graph. Reachable preservation of balance is a separate theorem. -/
theorem LevelBalance.proper_principal_indices (balance : LevelBalance g boundary)
    (left right : N) (p : Port (g.label left).sort) (q : Port (g.label right).sort)
    (lop rop : Op) (li ri : Nat) (leftLabel : g.label left=label lop li) (rightLabel : g.label right=label rop ri)
    (leftProper : lop=.app ∨lop=.lam) (rightProper : rop=.app ∨rop=.lam)
    (leftPrincipal : HEq p (Sum.inl () : Port (.op lop))) (rightPrincipal : HEq q (Sum.inl () : Port (.op rop)))
    (wired : g.wire (.inl ⟨left,p⟩)=.inl ⟨right,q⟩) : li=ri := by
  have equal := balance.wiring (.inl ⟨left,p⟩)
  rw [wired] at equal
  change portDepth _ _ (balance.nodes right) q=portDepth _ _ (balance.nodes left) p at equal
  rw [proper_principal_depth _ rop ri _ q rightLabel rightProper rightPrincipal,
    proper_principal_depth _ lop li _ p leftLabel leftProper leftPrincipal] at equal
  omega
end
end Lamping.AG
