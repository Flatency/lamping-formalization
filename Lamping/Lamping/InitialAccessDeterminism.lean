import Lamping.Lamping.InitialAccessWords
namespace Lamping.AG
open Graph Lambda
private def departureWord : (k : Kind) → Port k → Path
  | .op .app,.inl () => [.fn]
  | .op .app,.inr true => [.arg]
  | .op .lam,.inr true => [.body]
  | _,_ => []
private theorem passage_departure_unique {i j : Nat} {k : Kind} {p q r : Port k}
    (left : Passage i k p q a b) (right : Passage j k p r c d) (ps qs : Path)
    (same : departureWord k q++ps=departureWord k r++qs) : q=r := by
  cases left <;> cases right <;> first | rfl | cases same
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

theorem InitialTurn.departure_word_unique {x y z : Endpoint g} {a b c d : Context}
    (left : InitialTurn (g:=g) x y a b) (right : InitialTurn (g:=g) x z c d)
    (ps qs : Path) (same : arrivalWord g y++ps=arrivalWord g z++qs) : y=z := by
  cases left with
  | node n p q rule =>
    cases right with
    | node n p r other =>
      have equal : q=r := passage_departure_unique rule other ps qs same
      cases equal; rfl
  | transparent w dir a =>
    cases right
    rfl
end
end Lamping.AG

namespace Lamping.AG
open Graph Lambda
private theorem passage_terminal_word {i : Nat} {k : Kind} {p q : Port k}
    (rule : Passage i k p q a b) (kind : AccessKind) (terminal : portKind k p=some kind) :
    departureWord k q≠[] := by
  cases rule <;> simp_all [portKind,departureWord,appCtx,appArg,lamBody]
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}
private def incomingKind (g : Net signature N B W) (x : Endpoint g) : Option AccessKind :=
  match x with
  | .inl ⟨n,p⟩ => portKind (g.label n).sort p
  | _ => none
private theorem terminal_turn_word {x y : Endpoint g} (turn : InitialTurn (g:=g) x y a b)
    (kind : AccessKind) (terminal : incomingKind g x=some kind) (ps : Path) :
    arrivalWord g y++ps≠[] := by
  cases turn with
  | node n p q rule =>
    have nonempty := passage_terminal_word rule kind terminal
    intro same
    exact nonempty (List.append_eq_nil_iff.mp same).1
  | transparent w d a => cases terminal

/-- For initial-direction paths, the syntax word and starting segment
uniquely determine a proper-ended access, independently of its labels. -/
theorem InitialLabelling.access_word_unique {es fs : List (Endpoint g)}
    (left : InitialLabelling (g:=g) es a b) (right : InitialLabelling (g:=g) fs c d)
    (start : es.head?=fs.head?) (word : accessWord g es=accessWord g fs)
    (leftTerminal : ∃ k, accessKind g es=some k) (rightTerminal : ∃ k, accessKind g fs=some k) : es=fs := by
  induction left generalizing fs c d with
  | single e a =>
    cases right with
    | single f c =>
      have same : e=f := Option.some.inj start
      cases same; rfl
    | @cons f z rest c mid d turn tail =>
      have same : e=f := Option.some.inj start
      cases same
      obtain ⟨kind,terminal⟩ := leftTerminal
      have impossible := terminal_turn_word turn kind (by simpa [accessKind,incomingKind] using terminal) (rest.flatMap (arrivalWord g))
      exact False.elim (impossible word.symm)
  | @cons e f rest a mid b turn tail ih =>
    cases right with
    | single z c =>
      have same : e=z := Option.some.inj start
      cases same
      obtain ⟨kind,terminal⟩ := rightTerminal
      have impossible := terminal_turn_word turn kind (by simpa [accessKind,incomingKind] using terminal) (rest.flatMap (arrivalWord g))
      exact False.elim (impossible word)
    | @cons z w other c next d second remaining =>
      have same : e=z := Option.some.inj start
      cases same
      have equal : f=w := turn.departure_word_unique second
        (rest.flatMap (arrivalWord g)) (other.flatMap (arrivalWord g)) word
      cases equal
      have after : accessWord g (f::rest)=accessWord g (f::other) := by
        change arrivalWord g f++rest.flatMap (arrivalWord g)=arrivalWord g f++other.flatMap (arrivalWord g) at word
        exact List.append_cancel_left word
      have finalLeft : ∃ k, accessKind g (f::rest)=some k := by
        simpa only [accessKind,List.getLast?_cons_cons] using leftTerminal
      have finalRight : ∃ k, accessKind g (f::other)=some k := by
        simpa only [accessKind,List.getLast?_cons_cons] using rightTerminal
      exact congrArg (e::·) (ih remaining rfl after finalLeft finalRight)
end
end Lamping.AG

namespace Lamping.AG
open Graph Lambda
/-- The actual initial encoding cannot have two different proper-ended root
paths with the same syntax word. No source or target matching is assumed. -/
theorem encode_accessWord_injective (t : Term) (n : Nat) :
    Function.Injective (fun es : RootAccess (encode n t).net (.inl ()) => accessWord (encode n t).net es.val) := by
  intro es fs word
  obtain ⟨a,b,left⟩ := es.property.1.1
  obtain ⟨c,d,right⟩ := fs.property.1.1
  apply Subtype.ext
  exact (encode_root_initial t n es.val es.property.2.1 left).access_word_unique
    (encode_root_initial t n fs.val fs.property.2.1 right)
    (es.property.2.1.trans fs.property.2.1.symm) word es.property.2.2 fs.property.2.2
end Lamping.AG
