import Lamping.Lamping.ControlOnlyConnections
namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

/-- Every adjacent pair is an actual transparent W turn. -/
def TransparentTurns (es : List (Endpoint g)) : Prop :=
  ∀ x y,(x,y)∈es.zip es.tail →
    ∃ w d,g.wire x=.inr (.inr (w,d)) ∧y=.inr (.inr (w,!d))

/-- The first actual node turn of an existing labelled path. The prefix and
suffix are literal occurrence lists; its traversal starts in the original
input since every earlier turn is transparent. -/
structure FirstNodeTurn (es : List (Endpoint g)) (a b : Context) where
  before : List (Endpoint g)
  entry : Endpoint g
  exit : Endpoint g
  after : List (Endpoint g)
  node : N
  incoming : Port (g.label node).sort
  outgoing : Port (g.label node).sort
  middle : Context
  split : es=before++entry::exit::after
  transparent : TransparentTurns (g:=g) (before++[entry])
  arrives : g.wire entry=.inl ⟨node,incoming⟩
  leaves : exit=.inl ⟨node,outgoing⟩
  rule : Traversal (g.label node).index (g.label node).sort incoming outgoing a middle
  suffix : Labelling g (exit::after) middle b

private theorem prepend_transparent (e f : Endpoint g) (tail before : List (Endpoint g))
    (selected next : Endpoint g) (after : List (Endpoint g))
    (split : f::tail=before++selected::next::after)
    (turn : ∃ w d,g.wire e=.inr (.inr (w,d)) ∧f=.inr (.inr (w,!d)))
    (remaining : TransparentTurns (g:=g) (before++[selected])) :
    TransparentTurns (g:=g) ((e::before)++[selected]) := by
  cases before with
  | nil =>
    have equal : f=selected := List.cons.inj split |>.1
    subst selected
    intro x y pair
    have equal : (x,y)=(e,f) := List.mem_singleton.mp pair
    cases equal
    exact turn
  | cons head before =>
    have equal : f=head := List.cons.inj split |>.1
    subst head
    intro x y pair
    rcases List.mem_cons.mp pair with equal |rest
    · cases equal
      exact turn
    · exact remaining x y rest

/-- Finite decomposition, not an assertion that a partial path can be
extended. No finiteness or reachability premise is needed. -/
theorem Labelling.first_node {es : List (Endpoint g)} {a b : Context}
    (labels : Labelling g es a b) :
    TransparentTurns (g:=g) es ∨Nonempty (FirstNodeTurn (g:=g) es a b) := by
  induction labels with
  | single e a => exact Or.inl (by intro x y pair; simp at pair)
  | @cons e f tail a middle b turn rest ih =>
    generalize arrives : g.wire e=arrival at turn
    cases turn with
    | node node p q rule =>
      exact Or.inr ⟨{
        before := [],entry := e,exit := .inl ⟨node,q⟩,after := tail,
        node := node,incoming := p,outgoing := q,middle := middle,
        split := rfl,transparent := by intro x y pair; simp at pair,
        arrives := arrives,leaves := rfl,rule := rule,suffix := rest }⟩
    | transparent w d a =>
      have crossing : ∃ w' d',g.wire e=.inr (.inr (w',d')) ∧
          (.inr (.inr (w,!d)) : Endpoint g)=.inr (.inr (w',!d')) := ⟨w,d,arrives,rfl⟩
      rcases ih with transparent |existsPiece
      · exact Or.inl (by
          intro x y pair
          rcases List.mem_cons.mp pair with equal |rest
          · cases equal; exact crossing
          · exact transparent x y rest)
      · obtain ⟨piece⟩ := existsPiece
        exact Or.inr ⟨{
          before := e::piece.before,entry := piece.entry,exit := piece.exit,after := piece.after,
          node := piece.node,incoming := piece.incoming,outgoing := piece.outgoing,
          middle := piece.middle,split := congrArg (List.cons e) piece.split,
          transparent := prepend_transparent e _ tail piece.before piece.entry piece.exit
            piece.after piece.split crossing piece.transparent,
          arrives := piece.arrives,leaves := piece.leaves,rule := piece.rule,suffix := piece.suffix }⟩
end
end Lamping.AG
