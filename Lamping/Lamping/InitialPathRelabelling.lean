import Lamping.Lamping.InitialAccessDeterminism
namespace Lamping.AG
open Graph Lambda
/-- Direct initial passages accept every new input context. This assertion
is intentionally not made for arbitrary inverse control traversals. -/
theorem Passage.relabel_input {i k p q a b} (passage : Passage i k p q a b) (c : Context) :
    ∃ d, Passage i k p q c d := by
  cases passage with
  | fanO => exact ⟨_,InitialOffsets.Event.apply_rel (.fan i false) c⟩
  | fanStar => exact ⟨_,InitialOffsets.Event.apply_rel (.fan i true) c⟩
  | cro => exact ⟨_,InitialOffsets.Event.apply_rel (.cro i) c⟩
  | bra => exact ⟨_,InitialOffsets.Event.apply_rel (.bra i) c⟩
  | appFun => exact ⟨c,.appFun c⟩
  | appArg => exact ⟨c,.appArg c⟩
  | lamBody => exact ⟨c,.lamBody c⟩
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

theorem InitialTurn.relabel_input {x y : Endpoint g} {a b : Context}
    (turn : InitialTurn (g:=g) x y a b) (c : Context) : ∃ d,InitialTurn (g:=g) x y c d := by
  cases turn with
  | node n p q rule =>
    obtain ⟨d,newRule⟩ := rule.relabel_input c
    exact ⟨d,.node n p q newRule⟩
  | transparent w dir a => exact ⟨c,.transparent w dir c⟩

theorem InitialLabelling.relabel_input {es : List (Endpoint g)} {a b : Context}
    (labels : InitialLabelling (g:=g) es a b) (c : Context) :
    ∃ d,InitialLabelling (g:=g) es c d := by
  induction labels generalizing c with
  | single e a => exact ⟨c,.single e c⟩
  | cons turn tail ih =>
    obtain ⟨next,newTurn⟩ := turn.relabel_input c
    obtain ⟨last,newTail⟩ := ih next
    exact ⟨last,.cons newTurn newTail⟩

theorem InitialTurn.labelled {x y : Endpoint g} {a b : Context}
    (turn : InitialTurn (g:=g) x y a b) : LabelledTurn g x y a b := by
  cases turn with
  | node n p q rule => exact .node n p q (.direct rule)
  | transparent w dir a => exact .transparent w dir a

theorem InitialLabelling.labelling {es : List (Endpoint g)} {a b : Context}
    (labels : InitialLabelling (g:=g) es a b) : Labelling g es a b := by
  induction labels with
  | single => exact .single _ _
  | cons turn tail ih => exact .cons turn.labelled ih
end

/-- An initial rooted path admits any input context, with its physical
segments fixed. This proves the first, re-labelling part of independence. -/
theorem encode_root_relabel_input (t : Term) (n : Nat)
    (es : List (Endpoint (encode n t).net)) (rooted : es.head?=some (.inr (.inl (.inl ()))))
    (proper : ProperPath (encode n t).net es) (c : Context) :
    ∃ d,Labelling (encode n t).net es c d := by
  obtain ⟨a,b,labels⟩ := proper
  obtain ⟨d,newLabels⟩ := (encode_root_initial t n es rooted labels).relabel_input c
  exact ⟨d,newLabels.labelling⟩
end Lamping.AG
