import Lamping.Lamping.InitialFreeAccess
namespace Lamping.AG
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}
theorem Labelling.append_seam {xs ys : List (Endpoint g)}
    (first : Labelling g xs a b) (second : Labelling g ys c d)
    (seam : ∀ e f,xs.getLast?=some e →ys.head?=some f →LabelledTurn g (g.wire e) f b c) :
    Labelling g (xs++ys) a d := by
  induction first with
  | single e a =>
    cases ys with
    | nil => cases second
    | cons f rest => exact .cons (seam e f rfl rfl) second
  | cons turn tail ih =>
    exact .cons turn (ih (fun e f last head =>
      seam e f (by simpa only [List.getLast?_cons_cons] using last) head))
end
private theorem last_append_nonempty {T : Type} (pre tail : List T) (nonempty : tail≠[]) :
    (pre++tail).getLast?=tail.getLast? := by
  rw [List.getLast?_append]
  cases h : tail.getLast? with
  | none => exact False.elim (nonempty (List.getLast?_eq_none_iff.mp h))
  | some => rfl
section
variable {K R B F W V : Type} [FiniteNames K] [FiniteNames R] [FiniteNames B]
  [FiniteNames F] [FiniteNames W] [FiniteNames V]
variable (c : Net signature K (B⊕F) W) (r : Net signature R F V)

def LocalPath.plugThree {x y : B} {entry exit : F}
    (first : LocalPath c (.inl x) (.inr entry) a b)
    (middle : LocalPath r entry exit b d)
    (last : LocalPath c (.inr exit) (.inl y) d e) : LocalPath (plug c r) x y a e where
  edges := first.edges.map (plugLeft c r)++middle.edges.map (plugRight c r)++last.edges.map (plugLeft c r)
  start := by simp only [List.head?_append,List.head?_map,first.start,Option.map_some]; rfl
  finish := by
    have nonempty : last.edges.map (plugLeft c r)≠[] := by
      intro same
      have heads := congrArg List.head? same
      rw [List.head?_map,last.start] at heads
      cases heads
    rw [last_append_nonempty _ _ nonempty,List.getLast?_map,last.finish]
    simp only [Option.map_some]
    exact congrArg some (plugLeft_wire c r _).symm
  labeling := by
    have firstLabels := first.labeling.plugLeft c r
    have middleLabels := middle.labeling.plugRight c
    have lastLabels := last.labeling.plugLeft c r
    have middleNonempty : middle.edges.map (plugRight c r)≠[] := by
      intro same
      have heads := congrArg List.head? same
      rw [List.head?_map,middle.start] at heads
      cases heads
    have joined : Labelling (plug c r)
        (first.edges.map (plugLeft c r)++middle.edges.map (plugRight c r)) a d := by
      apply firstLabels.append_seam middleLabels
      intro left right leftEnd rightStart
      have leftEq : left=plugLeft c r (c.wire (.inr (.inl (.inr entry)))) := by
        have original : (first.edges.map (plugLeft c r)).getLast?=
            some (plugLeft c r (c.wire (.inr (.inl (.inr entry))))) := by
          rw [List.getLast?_map,first.finish]; rfl
        exact Option.some.inj (leftEnd.symm.trans original)
      have rightEq : right=plugRight c r (.inr (.inl entry)) := by
        have original : (middle.edges.map (plugRight c r)).head?=
            some (plugRight c r (.inr (.inl entry))) := by rw [List.head?_map,middle.start]; rfl
        exact Option.some.inj (rightStart.symm.trans original)
      rw [leftEq,rightEq,←plugLeft_wire,Pairing.involutive]
      exact LabelledTurn.transparent (g:=plug c r) (Sum.inr entry) false b
    apply joined.append_seam lastLabels
    intro left right leftEnd rightStart
    have leftEq : left=plugRight c r (r.wire (.inr (.inl exit))) := by
      have original : (first.edges.map (plugLeft c r)++middle.edges.map (plugRight c r)).getLast?=
          some (plugRight c r (r.wire (.inr (.inl exit)))) := by
        rw [last_append_nonempty _ _ middleNonempty,List.getLast?_map,middle.finish]; rfl
      exact Option.some.inj (leftEnd.symm.trans original)
    have rightEq : right=plugLeft c r (.inr (.inl (.inr exit))) := by
      have original : (last.edges.map (plugLeft c r)).head?=
          some (plugLeft c r (.inr (.inl (.inr exit)))) := by rw [List.head?_map,last.start]; rfl
      exact Option.some.inj (rightStart.symm.trans original)
    rw [leftEq,rightEq,←plugRight_wire,Pairing.involutive]
    exact LabelledTurn.transparent (g:=plug c r) (Sum.inr exit) true d
end
end Lamping.AG

namespace Lamping.AG
open Graph Lambda
section
variable {N M B C W V : Type} [FiniteNames N] [FiniteNames M] [FiniteNames B]
  [FiniteNames C] [FiniteNames W] [FiniteNames V]
variable (g : Net signature N B W) (h : Net signature M C V)
theorem LabelledTurn.unionLeft {x y : Endpoint g} (turn : LabelledTurn g x y a b) :
    LabelledTurn (unionNet g h) (InitialOffsets.unionL g h x) (InitialOffsets.unionL g h y) a b := by
  cases turn with
  | node n p q rule => exact LabelledTurn.node (g:=unionNet g h) (Sum.inl n) p q rule
  | transparent w dir _ => exact LabelledTurn.transparent (g:=unionNet g h) (Sum.inl w) dir _

theorem LabelledTurn.unionRight {x y : Endpoint h} (turn : LabelledTurn h x y a b) :
    LabelledTurn (unionNet g h) (InitialOffsets.unionR g h x) (InitialOffsets.unionR g h y) a b := by
  cases turn with
  | node n p q rule => exact LabelledTurn.node (g:=unionNet g h) (Sum.inr n) p q rule
  | transparent w dir _ => exact LabelledTurn.transparent (g:=unionNet g h) (Sum.inr w) dir _

theorem Labelling.unionLeft {es : List (Endpoint g)} (labels : Labelling g es a b) :
    Labelling (unionNet g h) (es.map (InitialOffsets.unionL g h)) a b := by
  induction labels with
  | single => exact .single _ _
  | cons turn tail ih =>
    apply Labelling.cons
    · simp only [InitialOffsets.unionL,union_left]
      exact turn.unionLeft g h
    · exact ih

theorem Labelling.unionRight {es : List (Endpoint h)} (labels : Labelling h es a b) :
    Labelling (unionNet g h) (es.map (InitialOffsets.unionR g h)) a b := by
  induction labels with
  | single => exact .single _ _
  | cons turn tail ih =>
    apply Labelling.cons
    · simp only [InitialOffsets.unionR,union_right]
      exact turn.unionRight g h
    · exact ih

def LocalPath.unionLeft {x y : B} (p : LocalPath g x y a b) :
    LocalPath (unionNet g h) (.inl x) (.inl y) a b where
  edges := p.edges.map (InitialOffsets.unionL g h)
  start := by rw [List.head?_map,p.start]; rfl
  finish := by
    rw [List.getLast?_map,p.finish]
    exact congrArg some (union_left g h (.inr (.inl y))).symm
  labeling := p.labeling.unionLeft g h

def LocalPath.unionRight {x y : C} (p : LocalPath h x y a b) :
    LocalPath (unionNet g h) (.inr x) (.inr y) a b where
  edges := p.edges.map (InitialOffsets.unionR g h)
  start := by rw [List.head?_map,p.start]; rfl
  finish := by
    rw [List.getLast?_map,p.finish]
    exact congrArg some (union_right g h (.inr (.inl y))).symm
  labeling := p.labeling.unionRight g h
end
end Lamping.AG
