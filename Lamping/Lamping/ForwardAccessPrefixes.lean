import Lamping.Lamping.ForwardAccessDeterminism
namespace Lamping.AG
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

/-- A syntax-word prefix between two existing, common-input ordinary forward
proper-ended paths is a literal physical prefix. No path is extended. -/
theorem Labelling.forward_access_prefix {short long : List (Endpoint g)}
    (first : Labelling g short a b) (firstForward : Forward g short)
    (second : Labelling g long a d) (secondForward : Forward g long)
    (head : short.head?=long.head?) (suffix : Path)
    (word : accessWord g long=accessWord g short++suffix)
    (firstTerminal : ∃ k,accessKind g short=some k)
    (secondTerminal : ∃ k,accessKind g long=some k) :
    ∃ tail,long=short++tail := by
  induction first generalizing long d with
  | single e a =>
    cases second with
    | single f a =>
      have same : e=f := Option.some.inj head
      cases same
      exact ⟨[],rfl⟩
    | @cons f z rest a mid d turn after =>
      have same : e=f := Option.some.inj head
      cases same
      exact ⟨z::rest,rfl⟩
  | @cons e f rest a mid b turn after ih =>
    cases second with
    | single z a =>
      have same : e=z := Option.some.inj head
      cases same
      obtain ⟨kind,terminal⟩ := secondTerminal
      have impossible := (turn.forward_turn firstForward).terminal_word kind
        (by simpa only [accessKind,endpointKind,List.getLast?_cons,List.getLast?_nil,Option.bind_some,Option.getD_none] using terminal)
        (rest.flatMap (arrivalWord g)++suffix)
      exact False.elim (impossible (by simpa only [accessWord,List.flatMap_cons,List.flatMap_nil,List.append_assoc] using word.symm))
    | @cons z w other a next d right remaining =>
      have same : e=z := Option.some.inj head
      cases same
      obtain ⟨equal,contexts⟩ := (turn.forward_turn firstForward).departure_word_unique (right.forward_turn secondForward)
        (rest.flatMap (arrivalWord g)++suffix) (other.flatMap (arrivalWord g))
        (by simpa only [accessWord,List.flatMap_cons,List.append_assoc] using word.symm)
      cases equal
      subst next
      have tailWord : accessWord g (f::other)=accessWord g (f::rest)++suffix := by
        change arrivalWord g f++other.flatMap (arrivalWord g)=
          (arrivalWord g f++rest.flatMap (arrivalWord g))++suffix at word
        rw [List.append_assoc] at word
        exact List.append_cancel_left word
      have terminalFirst : ∃ k,accessKind g (f::rest)=some k := by
        simpa only [accessKind,List.getLast?_cons_cons] using firstTerminal
      have terminalSecond : ∃ k,accessKind g (f::other)=some k := by
        simpa only [accessKind,List.getLast?_cons_cons] using secondTerminal
      have tailForward : Forward g (f::rest) := by cases firstForward <;> assumption
      have otherForward : Forward g (f::other) := by cases secondForward <;> assumption
      obtain ⟨tail,eq⟩ := ih tailForward remaining otherForward rfl tailWord terminalFirst terminalSecond
      exact ⟨tail,congrArg (e::·) eq⟩

/-- The root-input clause of Independence supplies the common assignment
needed for prefix reflection between two already existing root accesses. -/
theorem Independence.accessWord_prefix (indep : Independence g root)
    (short long : RootAccess g root) (suffix : Path)
    (word : accessWord g long.val=accessWord g short.val++suffix) :
    ∃ tail,long.val=short.val++tail := by
  obtain ⟨b,left⟩ := short.inputs indep Context.empty
  obtain ⟨d,right⟩ := long.inputs indep Context.empty
  exact left.forward_access_prefix short.property.1.2 right long.property.1.2
    (short.property.2.1.trans long.property.2.1.symm) suffix word short.property.2.2 long.property.2.2
end
end Lamping.AG

