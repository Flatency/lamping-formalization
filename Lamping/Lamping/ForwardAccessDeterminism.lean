import Lamping.Lamping.BackwardPathDeterminism
import Lamping.Lamping.InitialAccessPrefix
namespace Lamping.AG
open Graph Lambda

private def emitted : (kind : Kind) → Port kind → Path
  | .op .app,.inl () => [.fn]
  | .op .app,.inr true => [.arg]
  | .op .lam,.inr true => [.body]
  | _,_ => []

private theorem control_departure_unique (op : Op) (control : op=.fan ∨op=.cro ∨op=.bra)
    {index : Nat} {p q r : Port (.op op)} {a b c : Context}
    (first : Traversal index (.op op) p q a b)
    (second : Traversal index (.op op) p r a c) : q=r := by
  cases p with
  | inl u =>
    cases u
    cases q with
    | inl u => cases u; exact False.elim (first.distinct rfl)
    | inr left =>
      cases r with
      | inl u => cases u; exact False.elim (second.distinct rfl)
      | inr right => exact congrArg Sum.inr (first.control_auxiliary_unique control second)
  | inr auxiliary =>
    rcases control with same | same | same <;> subst op
    all_goals exact first.control_aux.trans second.control_aux.symm

private theorem departure_unique {index : Nat} {kind : Kind} {p q r : Port kind} {a b c : Context}
    (first : Traversal index kind p q a b) (firstForward : ForwardPorts kind p q)
    (second : Traversal index kind p r a c) (secondForward : ForwardPorts kind p r)
    (ps qs : Path) (word : emitted kind q++ps=emitted kind r++qs) : q=r := by
  cases kind with
  | garbage => exact False.elim firstForward
  | op op =>
    cases op with
    | app =>
      rcases firstForward.2 with same | same <;> rw [same] at word ⊢
      all_goals rcases secondForward.2 with same | same <;> rw [same] at word ⊢
      all_goals first | rfl | cases word
    | lam => exact firstForward.2.trans secondForward.2.symm
    | fan => exact control_departure_unique .fan (Or.inl rfl) first second
    | cro => exact control_departure_unique .cro (Or.inr (Or.inl rfl)) first second
    | bra => exact control_departure_unique .bra (Or.inr (Or.inr rfl)) first second

private theorem traversal_terminal_word {index : Nat} {kind : Kind} {p q : Port kind} {a b : Context}
    (rule : Traversal index kind p q a b) (forward : ForwardPorts kind p q)
    (observation : AccessKind) (terminal : portKind kind p=some observation) : emitted kind q≠[] := by
  cases rule with
  | direct passage => cases passage <;> simp_all [emitted,portKind,appCtx,appArg,lamBody]
  | inverse passage => cases passage <;> simp_all [portKind,appArg,lamBody]

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

theorem ForwardLabelledTurn.departure_word_unique {x y z : Endpoint g} {a b c : Context}
    (first : ForwardLabelledTurn g x y a b) (second : ForwardLabelledTurn g x z a c)
    (ps qs : Path) (word : arrivalWord g y++ps=arrivalWord g z++qs) : y=z ∧b=c := by
  cases first with
  | node node p q rule direction =>
    cases second with
    | node node p r other otherDirection =>
      have ports := departure_unique rule direction other otherDirection ps qs word
      subst r
      exact ⟨rfl,rule.output_unique other⟩
  | transparent vertex direction a => cases second; exact ⟨rfl,rfl⟩

theorem ForwardLabelledTurn.terminal_word {x y : Endpoint g} {a b : Context}
    (turn : ForwardLabelledTurn g x y a b) (kind : AccessKind)
    (terminal : endpointKind x=some kind) (ps : Path) : arrivalWord g y++ps≠[] := by
  cases turn with
  | node node p q rule direction =>
    have nonempty := traversal_terminal_word rule direction kind terminal
    intro empty
    exact nonempty (List.append_eq_nil_iff.mp empty).1
  | transparent vertex direction a => cases terminal

theorem LabelledTurn.forward_turn {e f : Endpoint g} {es : List (Endpoint g)} {a b : Context}
    (turn : LabelledTurn g (g.wire e) f a b) (forward : Forward g (e::f::es)) :
    ForwardLabelledTurn g (g.wire e) f a b := by
  cases forward with
  | node node p q arrives leaves direction rest =>
    rw [arrives,leaves] at turn ⊢
    cases turn with
    | node node p q actual => exact .node node p q actual direction
  | transparent vertex direction arrives leaves rest =>
    rw [arrives,leaves] at turn ⊢
    cases turn
    exact .transparent vertex direction _

/-- With a common initial context, syntax words determine actual forward
proper-ended paths in arbitrary nets, including inverse control passages. -/
theorem Labelling.forward_access_word_unique {es fs : List (Endpoint g)} {a b c : Context}
    (first : Labelling g es a b) (firstForward : Forward g es)
    (second : Labelling g fs a c) (secondForward : Forward g fs)
    (start : es.head?=fs.head?) (word : accessWord g es=accessWord g fs)
    (firstTerminal : ∃ k,accessKind g es=some k) (secondTerminal : ∃ k,accessKind g fs=some k) : es=fs := by
  induction first generalizing fs c with
  | single e a =>
    cases second with
    | single f a => have same := Option.some.inj start; subst f; rfl
    | @cons f z rest a mid c turn after =>
      have same := Option.some.inj start
      subst f
      obtain ⟨kind,terminal⟩ := firstTerminal
      have impossible := (turn.forward_turn secondForward).terminal_word kind
        (by simpa only [accessKind,endpointKind,List.getLast?_cons,List.getLast?_nil,Option.bind_some,Option.getD_none] using terminal)
        (rest.flatMap (arrivalWord g))
      exact False.elim (impossible word.symm)
  | @cons e f rest a middle b turn after ih =>
    cases second with
    | single z a =>
      have same := Option.some.inj start
      subst z
      obtain ⟨kind,terminal⟩ := secondTerminal
      have impossible := (turn.forward_turn firstForward).terminal_word kind
        (by simpa only [accessKind,endpointKind,List.getLast?_cons,List.getLast?_nil,Option.bind_some,Option.getD_none] using terminal)
        (rest.flatMap (arrivalWord g))
      exact False.elim (impossible word)
    | @cons z w other a next c second remaining =>
      have same := Option.some.inj start
      subst z
      obtain ⟨departures,contexts⟩ := (turn.forward_turn firstForward).departure_word_unique
        (second.forward_turn secondForward) (rest.flatMap (arrivalWord g)) (other.flatMap (arrivalWord g)) word
      subst w
      subst next
      have tailWord : accessWord g (f::rest)=accessWord g (f::other) := by
        change arrivalWord g f++rest.flatMap (arrivalWord g)=arrivalWord g f++other.flatMap (arrivalWord g) at word
        exact List.append_cancel_left word
      have tailForward : Forward g (f::rest) := by cases firstForward <;> assumption
      have otherForward : Forward g (f::other) := by cases secondForward <;> assumption
      have terminalFirst : ∃ k,accessKind g (f::rest)=some k := by
        simpa only [accessKind,List.getLast?_cons_cons] using firstTerminal
      have terminalSecond : ∃ k,accessKind g (f::other)=some k := by
        simpa only [accessKind,List.getLast?_cons_cons] using secondTerminal
      exact congrArg (e::·) (ih tailForward remaining otherForward rfl tailWord terminalFirst terminalSecond)

/-- Uniform root-input labellability removes the common-context restriction.
No matching, reachability, or new path-existence assertion is introduced. -/
theorem Independence.accessWord_injective (indep : Independence g root) :
    Function.Injective (fun path : RootAccess g root => accessWord g path.val) := by
  intro first second word
  obtain ⟨b,left⟩ := first.inputs indep Context.empty
  obtain ⟨c,right⟩ := second.inputs indep Context.empty
  apply Subtype.ext
  exact left.forward_access_word_unique first.property.1.2 right second.property.1.2
    (first.property.2.1.trans second.property.2.1.symm) word first.property.2.2 second.property.2.2
end
end Lamping.AG


