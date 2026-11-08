import Lamping.Lamping.ControlTerminalObstruction
import Lamping.Lamping.ExpandedIndependence
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

private theorem labelled_rejects (actual : Label signature) (op : Op) (index : Nat)
    (p q : Port actual.sort) (lab : actual=label op index)
    (control : op=.fan ∨op=.cro ∨op=.bra) (principal : HEq p (Sum.inl () : Port (.op op)))
    (rule : Traversal actual.index actual.sort p q a b)
    (bad : a.get index=controlRejectingLevel op) : False := by
  subst actual
  exact principal_rejects op control rfl principal rule bad

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

/-- A supplied finite W prefix preserves the original input at its chosen
control occurrence. No continuation of a partial path is constructed. -/
theorem Labelling.no_rejected_control_prefix (pre : List (Endpoint g)) (e f : Endpoint g)
    (tail : List (Endpoint g)) {a b : Context}
    (labels : Labelling g (pre++e::f::tail) a b)
    (transparent : ∀ x y,(x,y)∈(pre++[e]).zip (pre++[e]).tail →
      ∃ w d,g.wire x=.inr (.inr (w,d)) ∧y=.inr (.inr (w,!d)))
    (node : N) (p q : Port (g.label node).sort) (op : Op) (index : Nat)
    (lab : g.label node=label op index) (control : op=.fan ∨op=.cro ∨op=.bra)
    (principal : HEq p (Sum.inl () : Port (.op op)))
    (arrives : g.wire e=.inl ⟨node,p⟩) (leaves : f=.inl ⟨node,q⟩)
    (bad : a.get index=controlRejectingLevel op) : False := by
  obtain ⟨middle,before,after⟩ := labels.split_segment
  have identity := transparent_route_labelling g (pre++[e]) (by simp) transparent a
  have equal : middle=a := before.output_unique identity
  subst middle
  cases after with
  | cons turn rest =>
    rw [arrives,leaves] at turn
    cases turn with
    | node node p q rule => exact labelled_rejects _ op index p q lab control principal rule bad

/-- The first control reader on an actual complete proper path must be
strictly below its source index, even with arbitrarily many supplied W turns.
Only whole-path ordinary Independence supplies arbitrary input. -/
theorem Independence.no_high_control_initial {root : B} (indep : Independence g root)
    (pre : List (Endpoint g)) (e f : Endpoint g) (tail : List (Endpoint g))
    (start terminal : Endpoint g) (sr tr : ProperRole) (m n : Nat) (a b : Context)
    (first : (pre++e::f::tail).head?=some start)
    (finish : (pre++e::f::tail).getLast?=some (g.wire terminal))
    (source : AtProperRole g root start sr m) (outgoing : sr.outgoing)
    (target : AtProperRole g root terminal tr n) (incoming : tr.incoming)
    (forward : Forward g (pre++e::f::tail)) (labels : Labelling g (pre++e::f::tail) a b)
    (transparent : ∀ x y,(x,y)∈(pre++[e]).zip (pre++[e]).tail →
      ∃ w d,g.wire x=.inr (.inr (w,d)) ∧y=.inr (.inr (w,!d)))
    (node : N) (p q : Port (g.label node).sort) (op : Op) (index : Nat)
    (lab : g.label node=label op index) (control : op=.fan ∨op=.cro ∨op=.bra)
    (principal : HEq p (Sum.inl () : Port (.op op)))
    (arrives : g.wire e=.inl ⟨node,p⟩) (leaves : f=.inl ⟨node,q⟩)
    (high : m≤index) : False := by
  let chosen := Context.empty.replace (index-m) (Context.empty.cons (controlRejectingLevel op))
  have bad : (a.replace m chosen).get index=controlRejectingLevel op := by
    rw [Context.replace_high _ _ high]
    change (Context.empty.replace (index-m) (Context.empty.cons (controlRejectingLevel op))).get (index-m)=_
    simp only [Context.replace_high _ _ (Nat.le_refl _),Nat.sub_self,Context.cons_zero]
  obtain ⟨output,changed⟩ := (indep (pre++e::f::tail) start terminal sr tr m n a b
    first finish source outgoing target incoming forward labels).1 chosen
  exact changed.no_rejected_control_prefix pre e f tail transparent node p q op index lab
    control principal arrives leaves bad
end
end Lamping.AG
