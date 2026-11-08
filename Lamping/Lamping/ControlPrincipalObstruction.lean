import Lamping.Lamping.GlobalPathInvariants
namespace Lamping.AG
open Graph

def controlRejectingLevel : Op → Level
  | .cro => .o .empty
  | _ => .empty

private theorem principal_rejects {i : Nat} {kind : Kind} {p q : Port kind} {a b : Context}
    (op : Op) (control : op=.fan ∨op=.cro ∨op=.bra) (sort : kind=.op op)
    (principal : HEq p (Sum.inl () : Port (.op op)))
    (rule : Traversal i kind p q a b) (bad : a.get i=controlRejectingLevel op) : False := by
  cases rule with
  | direct rule =>
    cases rule <;> cases op <;> simp_all [controlRejectingLevel,fanO,fanStar]
  | inverse rule =>
    cases rule <;> cases op <;> simp_all [controlRejectingLevel,Context.replace]

private theorem label_principal_rejects (actual : Label signature) (op : Op) (index : Nat)
    (p q : Port actual.sort) (lab : actual=label op index)
    (control : op=.fan ∨op=.cro ∨op=.bra) (principal : HEq p (Sum.inl () : Port (.op op)))
    (rule : Traversal actual.index actual.sort p q a b) (bad : a.get index=controlRejectingLevel op) : False := by
  subst actual
  exact principal_rejects op control rfl principal rule bad

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}
private theorem node_principal_rejects (node : N) (p : Port (g.label node).sort) (f : Endpoint g)
    (op : Op) (index : Nat) (lab : g.label node=label op index)
    (control : op=.fan ∨op=.cro ∨op=.bra) (principal : HEq p (Sum.inl () : Port (.op op)))
    (turn : LabelledTurn g (.inl ⟨node,p⟩) f a b) (bad : a.get index=controlRejectingLevel op) : False := by
  cases turn with
  | node n p q rule => exact label_principal_rejects _ op index p q lab control principal rule bad

/-- AG3.5.24(i)'s local obstruction at a given complete typed path. The
arbitrary-input premise comes from actual Independence of that full path,
never from a claim that every partial path admits arbitrary input. -/
theorem Independence.no_high_control_principal {root : B} (indep : Independence g root)
    (e f z : Endpoint g) (tail : List (Endpoint g)) (sr tr : ProperRole) (n terminal : Nat)
    (source : AtProperRole g root e sr n) (outgoing : sr.outgoing)
    (target : AtProperRole g root z tr terminal) (incoming : tr.incoming)
    (last : (e::f::tail).getLast?=some (g.wire z)) (fw : Forward g (e::f::tail))
    (labels : Labelling g (e::f::tail) a b)
    (node : N) (port : Port (g.label node).sort) (op : Op) (index : Nat)
    (lab : g.label node=label op index) (control : op=.fan ∨op=.cro ∨op=.bra)
    (principal : HEq port (Sum.inl () : Port (.op op))) (arrives : g.wire e=.inl ⟨node,port⟩)
    (high : n≤index) : False := by
  let chosen := Context.empty.replace (index-n) (Context.empty.cons (controlRejectingLevel op))
  have rejected : (a.replace n chosen).get index=controlRejectingLevel op := by
    rw [Context.replace_high _ _ high]
    change (Context.empty.replace (index-n) (Context.empty.cons (controlRejectingLevel op))).get (index-n)=_
    simp only [Context.replace_high _ _ (Nat.le_refl _),Nat.sub_self,Context.cons_zero]
  obtain ⟨output,changed⟩ := (indep (e::f::tail) e z sr tr n terminal a b rfl last
    source outgoing target incoming fw labels).1 chosen
  cases changed with
  | cons turn after =>
    rw [arrives] at turn
    exact node_principal_rejects node port f op index lab control principal turn rejected
end
end Lamping.AG
