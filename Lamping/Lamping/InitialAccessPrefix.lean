import Lamping.Lamping.InitialAccessDeterminism
import Lamping.Lamping.InitialBoundAccess
namespace Lamping.AG
open Graph Lambda

def AccessKind.allows : AccessKind → Step → Prop
  | .app,.fn | .app,.arg | .lam,.body => True
  | _,_ => False
private def emitted : (k : Kind) → Port k → Path
  | .op .app,.inl () => [.fn]
  | .op .app,.inr true => [.arg]
  | .op .lam,.inr true => [.body]
  | _,_ => []
private theorem passage_terminal_token {i : Nat} {k : Kind} {p q : Port k}
    (rule : Passage i k p q a b) (kind : AccessKind) (terminal : portKind k p=some kind) :
    ∃ s,emitted k q=[s] ∧kind.allows s := by
  cases rule <;> cases kind <;> simp_all [portKind,emitted,AccessKind.allows,appCtx,appArg,lamBody]

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}
def endpointKind (e : Endpoint g) : Option AccessKind :=
  match e with
  | .inl ⟨n,p⟩ => portKind (g.label n).sort p
  | _ => none

theorem InitialTurn.terminal_token {x y : Endpoint g}
    (turn : InitialTurn (g:=g) x y a b) (kind : AccessKind)
    (terminal : endpointKind x=some kind) : ∃ s,arrivalWord g y=[s] ∧kind.allows s := by
  cases turn with
  | node n p q rule => exact passage_terminal_token rule kind terminal
  | transparent w d a => cases terminal

/-- Syntax-address prefixes between genuine proper-ended initial accesses
reflect to literal prefixes of the physical segment lists. -/
theorem InitialLabelling.access_prefix {short long : List (Endpoint g)}
    (first : InitialLabelling (g:=g) short a b) (second : InitialLabelling (g:=g) long c d)
    (head : short.head?=long.head?) (suffix : Path)
    (word : accessWord g long=accessWord g short++suffix)
    (firstTerminal : ∃ k,accessKind g short=some k)
    (secondTerminal : ∃ k,accessKind g long=some k) :
    ∃ tail,long=short++tail := by
  induction first generalizing long c d with
  | single e a =>
    cases second with
    | single f c =>
      have same : e=f := Option.some.inj head
      cases same
      exact ⟨[],rfl⟩
    | @cons f z rest c mid d turn after =>
      have same : e=f := Option.some.inj head
      cases same
      exact ⟨z::rest,rfl⟩
  | @cons e f rest a mid b turn after ih =>
    cases second with
    | single z c =>
      have same : e=z := Option.some.inj head
      cases same
      obtain ⟨kind,terminal⟩ := secondTerminal
      obtain ⟨s,token,_⟩ := turn.terminal_token kind (by simpa only [accessKind,endpointKind] using terminal)
      change []=(arrivalWord g f++rest.flatMap (arrivalWord g))++suffix at word
      rw [token] at word
      cases word
    | @cons z w other c next d right remaining =>
      have same : e=z := Option.some.inj head
      cases same
      have equal : f=w := turn.departure_word_unique right
        (rest.flatMap (arrivalWord g)++suffix) (other.flatMap (arrivalWord g))
        (by simpa only [accessWord,List.flatMap_cons,List.append_assoc] using word.symm)
      cases equal
      have tailWord : accessWord g (f::other)=accessWord g (f::rest)++suffix := by
        change arrivalWord g f++other.flatMap (arrivalWord g)=
          (arrivalWord g f++rest.flatMap (arrivalWord g))++suffix at word
        rw [List.append_assoc] at word
        exact List.append_cancel_left word
      have terminalFirst : ∃ k,accessKind g (f::rest)=some k := by
        simpa only [accessKind,List.getLast?_cons_cons] using firstTerminal
      have terminalSecond : ∃ k,accessKind g (f::other)=some k := by
        simpa only [accessKind,List.getLast?_cons_cons] using secondTerminal
      obtain ⟨tail,eq⟩ := ih remaining rfl tailWord terminalFirst terminalSecond
      exact ⟨tail,congrArg (e::·) eq⟩
end

theorem encode_accessWord_prefix (t : Term) (n : Nat)
    (short long : RootAccess (encode n t).net (.inl ())) (suffix : Path)
    (word : accessWord (encode n t).net long.val=accessWord (encode n t).net short.val++suffix) :
    ∃ tail,long.val=short.val++tail := by
  obtain ⟨a,b,first⟩ := short.property.1.1
  obtain ⟨c,d,second⟩ := long.property.1.1
  exact (encode_root_initial t n short.val short.property.2.1 first).access_prefix
    (encode_root_initial t n long.val long.property.2.1 second)
    (short.property.2.1.trans long.property.2.1.symm) suffix word short.property.2.2 long.property.2.2
end Lamping.AG

namespace Lamping.AG
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}
theorem InitialLabelling.append_turn (pre : List (Endpoint g)) (f : Endpoint g)
    (tail : List (Endpoint g)) (e : Endpoint g) (last : pre.getLast?=some e)
    (labels : InitialLabelling (g:=g) (pre++f::tail) a b) :
    ∃ c d,InitialTurn (g:=g) (g.wire e) f c d := by
  induction pre generalizing a b with
  | nil => cases last
  | cons first rest ih =>
    cases rest with
    | nil =>
      have same : first=e := Option.some.inj last
      cases same
      cases labels with
      | cons turn after => exact ⟨_,_,turn⟩
    | cons next rest =>
      cases labels with
      | cons turn after =>
        exact ih (by simpa only [List.getLast?_cons_cons] using last) after

/-- If one initial root access has a strictly longer address than another,
the first added syntax token is allowed by the shorter access's actual kind. -/
theorem encode_access_extension_token (t : Term) (n : Nat)
    (short long : RootAccess (encode n t).net (.inl ())) (s : Step) (rest : Path)
    (word : accessWord (encode n t).net long.val=accessWord (encode n t).net short.val++s::rest)
    (kind : AccessKind) (terminal : accessKind (encode n t).net short.val=some kind) :
    kind.allows s := by
  obtain ⟨physical,eq⟩ := encode_accessWord_prefix t n short long (s::rest) word
  have shortNonempty : short.val≠[] := by
    intro empty
    have root := short.property.2.1
    rw [empty] at root
    cases root
  cases physical with
  | nil =>
    rw [List.append_nil] at eq
    rw [eq] at word
    have lengths := congrArg List.length word
    simp only [List.length_append,List.length_cons] at lengths
    omega
  | cons f tail =>
    obtain ⟨a,b,labels⟩ := long.property.1.1
    have initial := encode_root_initial t n long.val long.property.2.1 labels
    rw [eq] at initial
    cases last : short.val.getLast? with
    | none => exact False.elim (shortNonempty (List.getLast?_eq_none_iff.mp last))
    | some e =>
      obtain ⟨c,d,turn⟩ := initial.append_turn short.val f tail e last
      have incoming : endpointKind ((encode n t).net.wire e)=some kind := by
        simpa only [accessKind,last,Option.bind_some,endpointKind] using terminal
      obtain ⟨token,tokenEq,allowed⟩ := turn.terminal_token kind incoming
      rw [eq,accessWord_append _ _ _ shortNonempty] at word
      have tailWord : (f::tail).flatMap (arrivalWord (encode n t).net)=s::rest :=
        List.append_cancel_left word
      rw [List.flatMap_cons,tokenEq] at tailWord
      have same : token=s := by exact List.head_eq_of_cons_eq tailWord
      cases same
      exact allowed
end
end Lamping.AG
