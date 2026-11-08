import Lamping.Lamping.ControlPrincipalObstruction
import Lamping.Lamping.PathSitePrincipalRoutes
import Lamping.Lamping.PathLabelDeterminism
namespace Lamping.AG
open Graph
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

private theorem strip_prefix {pre : List (Endpoint g)} {e : Endpoint g} {tail : List (Endpoint g)}
    {a b : Context} (labels : Labelling g (pre++e::tail) a b) :
    ∃ middle,Labelling g (e::tail) middle b := by
  induction pre generalizing a with
  | nil => exact ⟨a,labels⟩
  | cons x xs ih =>
    cases xs with
    | nil =>
      cases labels with
      | cons turn rest => exact ⟨_,rest⟩
    | cons y xs =>
      cases labels with
      | cons turn rest => exact ih rest

private theorem reversed_traversal {i k p q a b} (rule : Traversal i k p q a b) :
    Traversal i k q p b a := by
  cases rule with
  | direct rule => exact .inverse rule
  | inverse rule => exact .direct rule

private theorem node_exit_rejects (node : N) (p q : Port (g.label node).sort)
    (op : Op) (index : Nat) (lab : g.label node=label op index)
    (control : op=.fan ∨op=.cro ∨op=.bra)
    (principal : HEq q (Sum.inl () : Port (.op op)))
    {a b : Context} (turn : LabelledTurn g (.inl ⟨node,p⟩) (.inl ⟨node,q⟩) a b)
    (bad : b.get index=controlRejectingLevel op) : False := by
  cases turn with
  | node node p q rule =>
    exact label_principal_rejects _ op index q p lab control principal (reversed_traversal rule) bad

/-- An existing labelled path cannot finish with a control-principal writer
whose emitted value is rejected, followed only by actual transparent W turns. -/
theorem Labelling.no_rejected_control_suffix (pre : List (Endpoint g)) (e f : Endpoint g)
    (tail : List (Endpoint g)) {a b : Context}
    (labels : Labelling g (pre++e::f::tail) a b)
    (transparent : ∀ x y,(x,y)∈(f::tail).zip (f::tail).tail →
      ∃ w d,g.wire x=.inr (.inr (w,d)) ∧y=.inr (.inr (w,!d)))
    (node : N) (p q : Port (g.label node).sort) (op : Op) (index : Nat)
    (lab : g.label node=label op index) (control : op=.fan ∨op=.cro ∨op=.bra)
    (principal : HEq q (Sum.inl () : Port (.op op)))
    (arrives : g.wire e=.inl ⟨node,p⟩) (leaves : f=.inl ⟨node,q⟩)
    (bad : b.get index=controlRejectingLevel op) : False := by
  obtain ⟨middle,rest⟩ := strip_prefix labels
  cases rest with
  | @cons _ _ _ _ output _ turn suffix =>
    have identity := transparent_route_labelling g (f::tail) (by simp) transparent output
    have equal := identity.output_unique suffix
    subst output
    rw [arrives,leaves] at turn
    exact node_exit_rejects node p q op index lab control principal turn bad

/-- The terminal synchronization clause of actual ordinary Independence
excludes a high control-principal immediately before the final proper port,
allowing arbitrary W subdivisions. The final lambda context is not falsely
used as an outgoing source. -/
theorem Independence.no_high_control_terminal {root : B} (indep : Independence g root)
    (pre : List (Endpoint g)) (e f : Endpoint g) (tail : List (Endpoint g))
    (start terminal : Endpoint g) (sr tr : ProperRole) (m n : Nat) (a b : Context)
    (first : (pre++e::f::tail).head?=some start)
    (finish : (pre++e::f::tail).getLast?=some (g.wire terminal))
    (source : AtProperRole g root start sr m) (outgoing : sr.outgoing)
    (target : AtProperRole g root terminal tr n) (incoming : tr.incoming)
    (forward : Forward g (pre++e::f::tail)) (labels : Labelling g (pre++e::f::tail) a b)
    (transparent : ∀ x y,(x,y)∈(f::tail).zip (f::tail).tail →
      ∃ w d,g.wire x=.inr (.inr (w,d)) ∧y=.inr (.inr (w,!d)))
    (node : N) (p q : Port (g.label node).sort) (op : Op) (index : Nat)
    (lab : g.label node=label op index) (control : op=.fan ∨op=.cro ∨op=.bra)
    (principal : HEq q (Sum.inl () : Port (.op op)))
    (arrives : g.wire e=.inl ⟨node,p⟩) (leaves : f=.inl ⟨node,q⟩)
    (high : tr.terminalWidth n≤index) : False := by
  obtain ⟨_,width,_lower,_strict,_fixed,sync⟩ := indep (pre++e::f::tail) start terminal sr tr m n a b
    first finish source outgoing target incoming forward labels
  let chosen := Context.empty.replace (index-tr.terminalWidth n)
    (Context.empty.cons (controlRejectingLevel op))
  have bad : (b.replace (tr.terminalWidth n) chosen).get index=controlRejectingLevel op := by
    rw [Context.replace_high _ _ high]
    change (Context.empty.replace (index-tr.terminalWidth n)
      (Context.empty.cons (controlRejectingLevel op))).get (index-tr.terminalWidth n)=_
    simp only [Context.replace_high _ _ (Nat.le_refl _),Nat.sub_self,Context.cons_zero]
  exact (sync chosen).no_rejected_control_suffix pre e f tail transparent node p q op index lab
    control principal arrives leaves bad
end
end Lamping.AG
