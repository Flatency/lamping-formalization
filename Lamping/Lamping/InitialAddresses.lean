import Lamping.Lamping.InitialTransparency
namespace Lamping.AG
open Graph Lambda
/-- Optional syntax phase at a port of an initial graph. Cro consumes the
variable-address phase; Fan/Bra and binding ports cannot recreate that phase. -/
def syntaxPortAddress (kind : Kind) (p : Port kind) (address : Path) : Option Path :=
  match kind,p with
  | .op .app,.inl () => some (address++[.fn])
  | .op .app,.inr false => some address
  | .op .app,.inr true => some (address++[.arg])
  | .op .lam,.inl () => some address
  | .op .lam,.inr true => some (address++[.body])
  | .op .cro,.inr () => some address
  | _,_ => none

def syntaxDepartureWord : (kind : Kind) → Port kind → Path
  | .op .app,.inl () => [.fn]
  | .op .app,.inr true => [.arg]
  | .op .lam,.inr true => [.body]
  | _,_ => []

private theorem passage_address {i : Nat} {kind : Kind} {p q : Port kind}
    (rule : Passage i kind p q a b) (address result : Path)
    (output : syntaxPortAddress kind q address=some result) :
    ∃ before,syntaxPortAddress kind p address=some before ∧result=before++syntaxDepartureWord kind q := by
  cases rule <;> simp_all [syntaxPortAddress,syntaxDepartureWord,appCtx,appArg,lamBody]

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable (g : Net signature N B W)
def endpointAddress (nodes : N → Path) (boundary : B → Option Path) (vertices : W → Option Path) :
    Endpoint g → Option Path
  | .inl ⟨n,p⟩ => syntaxPortAddress (g.label n).sort p (nodes n)
  | .inr (.inl b) => boundary b
  | .inr (.inr (w,_)) => vertices w

/-- Explicit finite geometry: wire endpoints have the same optional syntax
phase. This does not contain any path correctness or nesting conclusion. -/
structure Addressing (boundary : B → Option Path) where
  nodes : N → Path
  vertices : W → Option Path
  wiring : ∀ e,endpointAddress g nodes boundary vertices (g.wire e)=
    endpointAddress g nodes boundary vertices e

private theorem InitialTurn.address_predecessor (nodes : N → Path)
    (boundary : B → Option Path) (vertices : W → Option Path) {x f : Endpoint g}
    (turn : InitialTurn (g:=g) x f a b) (word : Path)
    (atExit : endpointAddress g nodes boundary vertices f=some word) :
    ∃ before,endpointAddress g nodes boundary vertices x=some before ∧
      word=before++arrivalWord g f := by
  cases turn with
  | node n p q rule => exact passage_address rule _ _ atExit
  | transparent w d a => exact ⟨word,atExit,(List.append_nil word).symm⟩

theorem Addressing.turn_predecessor {boundary : B → Option Path} (addr : Addressing g boundary)
    {e f : Endpoint g} (turn : InitialTurn (g:=g) (g.wire e) f a b) (word : Path)
    (atExit : endpointAddress g addr.nodes boundary addr.vertices f=some word) :
    ∃ before,endpointAddress g addr.nodes boundary addr.vertices e=some before ∧
      word=before++arrivalWord g f := by
  have step := turn.address_predecessor g addr.nodes boundary addr.vertices word atExit
  rw [addr.wiring] at step
  exact step

/-- On the surviving syntax phase, a real labelled path records exactly the
source phase followed by all emitted syntax tokens. No existential path is
inferred from this conditional backward reflection. -/
theorem Addressing.path_predecessor {boundary : B → Option Path} (addr : Addressing g boundary)
    {es : List (Endpoint g)} (labels : InitialLabelling (g:=g) es a b) (e f : Endpoint g)
    (head : es.head?=some e) (last : es.getLast?=some f) (word : Path)
    (atExit : endpointAddress g addr.nodes boundary addr.vertices f=some word) :
    ∃ before,endpointAddress g addr.nodes boundary addr.vertices e=some before ∧
      word=before++accessWord g es := by
  induction labels generalizing e f word with
  | single x a =>
    have sameE : x=e := Option.some.inj head
    have sameF : x=f := Option.some.inj last
    subst e; subst f
    exact ⟨word,atExit,(List.append_nil word).symm⟩
  | @cons x y tail a middle b turn after ih =>
    have sameE : x=e := Option.some.inj head
    subst e
    obtain ⟨beforeTail,tailAddress,tailWord⟩ := ih y f rfl
      (by simpa only [List.getLast?_cons_cons] using last) word atExit
    obtain ⟨before,source,step⟩ := addr.turn_predecessor g turn beforeTail tailAddress
    refine ⟨before,source,?_⟩
    rw [tailWord,step,List.append_assoc]
    rfl
end
end Lamping.AG

namespace Lamping.AG
open Graph Lambda
private theorem passage_address_context {i : Nat} {kind : Kind} {p q : Port kind}
    (rule : Passage i kind p q a b) (address result : Path)
    (output : syntaxPortAddress kind q address=some result) : a=b := by
  cases rule <;> first | rfl | cases output
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable (g : Net signature N B W)
private theorem InitialTurn.address_context (nodes : N → Path) (boundary : B → Option Path)
    (vertices : W → Option Path) {x y : Endpoint g} (turn : InitialTurn (g:=g) x y a b)
    (word : Path) (atExit : endpointAddress g nodes boundary vertices y=some word) : a=b := by
  cases turn with
  | node n p q rule => exact passage_address_context rule _ _ atExit
  | transparent => rfl

/-- While the syntax-address phase survives, a real initial path changes no
contexts. In particular a path reaching a proper context contains no variable
control effects; controls cannot restore a phase lost earlier. -/
theorem Addressing.path_context {boundary : B → Option Path} (addr : Addressing g boundary)
    {es : List (Endpoint g)} (labels : InitialLabelling (g:=g) es a b)
    (f : Endpoint g) (last : es.getLast?=some f) (word : Path)
    (atExit : endpointAddress g addr.nodes boundary addr.vertices f=some word) : a=b := by
  induction labels generalizing f word with
  | single e a => rfl
  | @cons e y tail a middle b turn after ih =>
    have final : (y::tail).getLast?=some f := by
      simpa only [List.getLast?_cons_cons] using last
    obtain ⟨before,state,_⟩ := addr.path_predecessor g after y f rfl final word atExit
    have first := turn.address_context g addr.nodes boundary addr.vertices before state
    exact first.trans (ih f final word atExit)
end
end Lamping.AG
