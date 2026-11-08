import Lamping.Lamping.MatchingDefinitions
namespace Lamping.AG.Readback
open Graph

/-- Executable context notation. Trailing empties are semantically invisible;
all generated contexts remain finite data, rather than chosen functions. -/
abbrev ContextData := List Level
namespace ContextData

def get (a : ContextData) (i : Nat) : Level := a[i]?.getD .empty

def lowPrefix : Nat → ContextData → ContextData
  | 0,_ => []
  | n+1,[] => .empty::lowPrefix n []
  | n+1,x::xs => x::lowPrefix n xs

def replaceTail (a : ContextData) (i : Nat) (tail : ContextData) : ContextData :=
  Context.normalise (lowPrefix i a++tail)

def put (a : ContextData) (i : Nat) (x : Level) : ContextData :=
  replaceTail a i (x::a.drop (i+1))
end ContextData

/-- One deterministic partial CONTROL traversal. The actual incoming port
and level data select the outgoing port; there is no semantic choice.
Proper-node turns are handled separately by syntax reconstruction. -/
def executeControl (i : Nat) : (kind : Kind) → Port kind → ContextData →
    Option ((Port kind)×ContextData)
  | .op .fan,.inr false,a => some (.inl (),a.put i (.o (a.get i)))
  | .op .fan,.inr true,a => some (.inl (),a.put i (.star (a.get i)))
  | .op .fan,.inl (),a => match a.get i with
      | .o child => some (fanO,a.put i child)
      | .star child => some (fanStar,a.put i child)
      | _ => none
  | .op .cro,.inr (),a => some (.inl (),a.replaceTail i (.empty::a.drop i))
  | .op .cro,.inl (),a => match a.get i with
      | .empty => some (.inr (),a.replaceTail i (a.drop (i+1)))
      | _ => none
  | .op .bra,.inr (),a =>
      some (.inl (),a.replaceTail i (.pair (a.get (i+1)) (a.get i)::a.drop (i+2)))
  | .op .bra,.inl (),a => match a.get i with
      | .pair left right => some (.inr (),a.replaceTail i (right::left::a.drop (i+1)))
      | _ => none
  | _,_,_ => none

inductive ScanFailure where
  | boundary | noControlRule
  deriving DecidableEq,Repr

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
/-- A scan records the literal actual terminal node/port. It does not yet
claim a syntax tree or a binding occurrence from node identity. -/
inductive ScanResult (g : Net signature N B W) where
  | next (departure : Endpoint g) (context : ContextData)
  | terminal (arrival : NodePort signature N g.label) (kind : AccessKind) (context : ContextData)
  | failed (reason : ScanFailure)

/-- Cross exactly one actual wire and, for a control, one actual vertex.
This function is executable even on malformed semantic inputs. -/
def scanOne (g : Net signature N B W) (departure : Endpoint g) (context : ContextData) : ScanResult g :=
  match g.wire departure with
  | .inr (.inl _) => .failed .boundary
  | .inr (.inr (vertex,direction)) => .next (.inr (.inr (vertex,!direction))) context
  | .inl ⟨node,port⟩ =>
      match portKind (g.label node).sort port with
      | some kind => .terminal ⟨node,port⟩ kind context
      | none => match executeControl (g.label node).index (g.label node).sort port context with
          | some (out,after) => .next (.inl ⟨node,out⟩) after
          | none => .failed .noControlRule

inductive ScanRun (g : Net signature N B W) where
  | exhausted (departure : Endpoint g) (context : ContextData)
  | stopped (result : ScanResult g)

/-- Bounded executable scan only. Termination of unbounded readback will be
proved on the semantic domain, not inferred from the finite graph carrier. -/
def scanFuel (g : Net signature N B W) : Nat → Endpoint g → ContextData → ScanRun g
  | 0,departure,context => .exhausted departure context
  | fuel+1,departure,context => match scanOne g departure context with
      | .next next after => scanFuel g fuel next after
      | .terminal port kind after => .stopped (.terminal port kind after)
      | .failed reason => .stopped (.failed reason)
end
end Lamping.AG.Readback
