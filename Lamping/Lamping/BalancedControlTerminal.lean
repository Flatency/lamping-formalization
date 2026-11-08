import Lamping.Lamping.ControlTerminalObstruction
import Lamping.Lamping.HighTailTransport
namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

/-- The actual indexed structural balance already supplies the terminal-tail
synchronization needed to exclude the last high control. Full Independence
and Matches are not required by this theorem. -/
theorem IndexedLevelBalance.no_high_control_terminal {root : B} {boundary : B → Int}
    (balance : IndexedLevelBalance g boundary) (rootDepth : boundary root=0)
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
  obtain ⟨width,_lower,_strict,_fixed,sync⟩ := balance.independence_tail root rootDepth
    (pre++e::f::tail) start terminal sr tr m n a b first finish source outgoing target incoming forward labels
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
