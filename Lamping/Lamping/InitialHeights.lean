import Lamping.Lamping.InitialNodeAccess
namespace Lamping.AG
open Graph Lambda
/-- Surviving syntax-phase level at an initial port. Entering an argument
raises the level, while Cro ends the syntax phase. -/
def syntaxPortHeight (level : Nat) (kind : Kind) (p : Port kind) : Option Nat :=
  match kind,p with
  | .op .app,.inr true => some (level+1)
  | .op .app,_ => some level
  | .op .lam,.inl () => some level
  | .op .lam,.inr true => some level
  | .op .cro,.inr () => some level
  | _,_ => none

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable (g : Net signature N B W)
def endpointHeight (boundary : B → Option Nat) (vertices : W → Option Nat) : Endpoint g → Option Nat
  | .inl ⟨n,p⟩ => syntaxPortHeight (g.label n).index (g.label n).sort p
  | .inr (.inl b) => boundary b
  | .inr (.inr (w,_)) => vertices w
/-- Explicit wire levels, with no path bound or Independence conclusion. -/
structure Heighting (boundary : B → Option Nat) where
  vertices : W → Option Nat
  wiring : ∀ e,endpointHeight g boundary vertices (g.wire e)=endpointHeight g boundary vertices e

def endpointEvents : Endpoint g → List InitialOffsets.Event
  | .inl ⟨n,p⟩ => (InitialOffsets.eventOfPort (g.label n).index (g.label n).sort p).toList
  | _ => []
end
private theorem passage_height {i : Nat} {kind : Kind} {p q : Port kind}
    (rule : Passage i kind p q a b) (lower : Nat)
    (source : syntaxPortHeight i kind p=some lower) :
    (∃ upper,syntaxPortHeight i kind q=some upper ∧lower≤upper ∧
      InitialOffsets.eventOfPort i kind p=none) ∨
      (lower=i ∧InitialOffsets.eventOfPort i kind p=some (.cro i)) := by
  cases rule <;> simp_all [syntaxPortHeight,InitialOffsets.eventOfPort,appCtx,appArg,lamBody]

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable (g : Net signature N B W)
private theorem InitialTurn.height_step (boundary : B → Option Nat) (vertices : W → Option Nat)
    {x y : Endpoint g} (turn : InitialTurn (g:=g) x y a b) (lower : Nat)
    (source : endpointHeight g boundary vertices x=some lower) :
    (∃ upper,endpointHeight g boundary vertices y=some upper ∧lower≤upper ∧endpointEvents g x=[]) ∨
      endpointEvents g x=[.cro lower] := by
  cases turn with
  | node n p q rule =>
    rcases passage_height rule lower source with ⟨upper,output,bound,noEvent⟩ | ⟨equal,event⟩
    · exact Or.inl ⟨upper,output,bound,by change (InitialOffsets.eventOfPort _ _ _).toList=[]; rw [noEvent]; rfl⟩
    · subst lower
      exact Or.inr (by change (InitialOffsets.eventOfPort _ _ _).toList=[_]; rw [event]; rfl)
  | transparent w d a => exact Or.inl ⟨lower,source,Nat.le_refl _,rfl⟩

theorem Heighting.turn_step {boundary : B → Option Nat} (height : Heighting g boundary)
    {e f : Endpoint g} (turn : InitialTurn (g:=g) (g.wire e) f a b) (lower : Nat)
    (source : endpointHeight g boundary height.vertices e=some lower) :
    (∃ upper,endpointHeight g boundary height.vertices f=some upper ∧lower≤upper ∧
      InitialOffsets.arrivalEvents g e=[]) ∨InitialOffsets.arrivalEvents g e=[.cro lower] := by
  have incoming : endpointHeight g boundary height.vertices (g.wire e)=some lower :=
    (height.wiring e).trans source
  exact turn.height_step g boundary height.vertices lower incoming

/-- Before the first actual Cro event, a syntax-phase path cannot decrease
its level. This is a bound extracted from real passages and wire geometry. -/
theorem Heighting.first_cro_lower {boundary : B → Option Nat} (height : Heighting g boundary)
    {es : List (Endpoint g)} (labels : InitialLabelling (g:=g) es a b) (e : Endpoint g)
    (head : es.head?=some e) (lower leaf : Nat)
    (source : endpointHeight g boundary height.vertices e=some lower)
    (first : (InitialOffsets.eventsOfEdges g es).head?=some (.cro leaf)) : lower≤leaf := by
  induction labels generalizing e lower with
  | single x a => cases first
  | @cons x y tail a middle b turn after ih =>
    have same : x=e := Option.some.inj head
    subst e
    rcases height.turn_step g turn lower source with ⟨upper,output,bound,noEvent⟩ | event
    · have next : (InitialOffsets.eventsOfEdges g (y::tail)).head?=some (.cro leaf) := by
        change (InitialOffsets.arrivalEvents g x++InitialOffsets.eventsOfEdges g (y::tail)).head?=_ at first
        simpa only [noEvent,List.nil_append] using first
      exact Nat.le_trans bound (ih y rfl upper output next)
    · have sameLevel : lower=leaf := by
        change (InitialOffsets.arrivalEvents g x++InitialOffsets.eventsOfEdges g (y::tail)).head?=_ at first
        rw [event] at first
        exact InitialOffsets.Event.cro.inj (Option.some.inj first)
      exact Nat.le_of_eq sameLevel
end
end Lamping.AG

namespace Lamping.AG
open Graph Lambda
private theorem passage_height_back {i : Nat} {kind : Kind} {p q : Port kind}
    (rule : Passage i kind p q a b) (upper : Nat)
    (target : syntaxPortHeight i kind q=some upper) :
    ∃ lower,syntaxPortHeight i kind p=some lower ∧lower≤upper := by
  cases rule <;> simp_all [syntaxPortHeight,appCtx,appArg,lamBody] <;> omega
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable (g : Net signature N B W)
private theorem InitialTurn.height_predecessor (boundary : B → Option Nat) (vertices : W → Option Nat)
    {x y : Endpoint g} (turn : InitialTurn (g:=g) x y a b) (upper : Nat)
    (target : endpointHeight g boundary vertices y=some upper) :
    ∃ lower,endpointHeight g boundary vertices x=some lower ∧lower≤upper := by
  cases turn with
  | node n p q rule => exact passage_height_back rule upper target
  | transparent w d a => exact ⟨upper,target,Nat.le_refl _⟩

/-- A path whose endpoint still lies in the syntax phase starts in that
phase at a no-greater level. No hidden finite-path or source-bound premise. -/
theorem Heighting.path_height {boundary : B → Option Nat} (height : Heighting g boundary)
    {es : List (Endpoint g)} (labels : InitialLabelling (g:=g) es a b)
    (e f : Endpoint g) (head : es.head?=some e) (last : es.getLast?=some f)
    (upper : Nat) (target : endpointHeight g boundary height.vertices f=some upper) :
    ∃ lower,endpointHeight g boundary height.vertices e=some lower ∧lower≤upper := by
  induction labels generalizing e f upper with
  | single x a =>
    have sameE : x=e := Option.some.inj head
    have sameF : x=f := Option.some.inj last
    subst e; subst f
    exact ⟨upper,target,Nat.le_refl _⟩
  | @cons x y tail a middle b turn after ih =>
    have sameE : x=e := Option.some.inj head
    subst e
    obtain ⟨middleHeight,source,bound⟩ := ih y f rfl
      (by simpa only [List.getLast?_cons_cons] using last) upper target
    obtain ⟨lower,incoming,lowerBound⟩ := turn.height_predecessor g boundary height.vertices middleHeight source
    exact ⟨lower,(height.wiring x).symm.trans incoming,Nat.le_trans lowerBound bound⟩
end
end Lamping.AG
