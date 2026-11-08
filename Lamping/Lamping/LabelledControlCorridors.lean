import Lamping.Lamping.PhysicalInteractionExistence
namespace Lamping.AG
open Graph

private theorem canonical_writer (actual : Label signature) (op : Op) (index : Nat)
    (p q : Port actual.sort) (lab : actual=label op index)
    (principal : HEq q (Sum.inl () : Port (.op op)))
    {a b : Context} (rule : Traversal actual.index actual.sort p q a b) :
    ∃ input : Port (.op op),Traversal index (.op op) input (.inl ()) a b := by
  subst actual
  have equal : q=.inl () := eq_of_heq principal
  subst q
  exact ⟨p,rule⟩

private theorem canonical_reader (actual : Label signature) (op : Op) (index : Nat)
    (p q : Port actual.sort) (lab : actual=label op index)
    (principal : HEq p (Sum.inl () : Port (.op op)))
    {a b : Context} (rule : Traversal actual.index actual.sort p q a b) :
    ∃ output : Port (.op op),Traversal index (.op op) (.inl ()) output a b := by
  subst actual
  have equal : p=.inl () := eq_of_heq principal
  subst p
  exact ⟨q,rule⟩

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

/-- Strip an existing finite transparent prefix while retaining its original
context at the one actual exit turn. The given list already includes that
turn; no continuation is postulated. -/
theorem Labelling.transparent_exit_turn (route : List (Endpoint g)) (next : Endpoint g)
    (terminal : Endpoint g) {a b : Context}
    (labels : Labelling g (route++[next]) a b)
    (finish : route.getLast?=some terminal)
    (transparent : ∀ e f,(e,f)∈route.zip route.tail →
      ∃ w d,g.wire e=.inr (.inr (w,d)) ∧f=.inr (.inr (w,!d))) :
    LabelledTurn g (g.wire terminal) next a b := by
  induction route generalizing a with
  | nil => cases finish
  | cons e route ih =>
    cases route with
    | nil =>
      have equal : e=terminal := Option.some.inj finish
      subst e
      cases labels with
      | cons turn rest => cases rest; exact turn
    | cons f route =>
      obtain ⟨w,d,arrives,leaves⟩ := transparent e f (by simp)
      cases labels with
      | cons turn rest =>
        rw [arrives,leaves] at turn
        cases turn
        exact ih rest (by simpa only [List.getLast?_cons_cons] using finish)
          (by intro x y pair; exact transparent x y (List.mem_cons_of_mem _ pair))

/-- Marker compatibility for the schema comes from this whole physical
labelling, not from separately chosen control traversals with a free seam. -/
theorem labelled_control_corridor_graph_step {left right : Op} {i j : Nat}
    (leftControl : left=.fan ∨left=.cro ∨left=.bra)
    (rightControl : right=.fan ∨right=.cro ∨right=.bra)
    {boundary : B → Bool} (flow : FlowBalance g boundary)
    (route : TransparentCorridor g) (ln rn : N)
    (ll : g.label ln=label left i) (rl : g.label rn=label right j)
    (lp la : Port (g.label ln).sort) (rp ra : Port (g.label rn).sort)
    (lh : HEq lp (Sum.inl () : Port (.op left)))
    (rh : HEq rp (Sum.inl () : Port (.op right)))
    (first : route.first=⟨ln,lp⟩) (last : route.last=⟨rn,rp⟩)
    (entry exit : Endpoint g) (arrives : g.wire entry=.inl ⟨ln,la⟩)
    (leaves : exit=.inl ⟨rn,ra⟩) {a b : Context}
    (labels : Labelling g (entry::(route.edges++[exit])) a b) :
    ∃ schema target,GraphStep schema (ActualNet.ofNet g) target := by
  cases shape : route.edges with
  | nil => have impossible := route.start; rw [shape] at impossible; cases impossible
  | cons head rest =>
    have headEqual : head=.inl ⟨ln,lp⟩ := Option.some.inj (by simpa only [shape,first] using route.start)
    rw [shape,headEqual] at labels
    cases labels with
    | @cons _ _ _ _ middle _ writer suffix =>
      rw [arrives] at writer
      cases writer with
      | node node p q rule =>
        obtain ⟨input,leftTurn⟩ := canonical_writer _ left i la lp ll lh rule
        have suffixLabels : Labelling g (route.edges++[exit]) middle b := by
          simpa only [shape,headEqual] using suffix
        have reader := suffixLabels.transparent_exit_turn route.edges exit
          (g.wire (.inl route.last)) route.finish route.transparent
        rw [Pairing.involutive,last,leaves] at reader
        cases reader with
        | node node p q rule =>
          obtain ⟨output,rightTurn⟩ := canonical_reader _ right j rp ra rl rh rule
          exact control_corridor_graph_step leftControl rightControl leftTurn rightTurn flow route
            ln rn ll rl lp rp lh rh first last
end
end Lamping.AG
