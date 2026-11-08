import Lamping.Lamping.PlugExcursionBlocks
import Lamping.Lamping.LocalTransport
namespace Lamping.AG
open Graph
section
variable {K R B F W V : Type} [FiniteNames K] [FiniteNames R] [FiniteNames B]
  [FiniteNames F] [FiniteNames W] [FiniteNames V]
variable (c : Net signature K (B⊕F) W) (r : Net signature R F V)

theorem PlugLabelling.of_right {es : List (Endpoint r)} (labels : Labelling r es a b) :
    PlugLabelling c r (es.map Sum.inr) a b := by
  induction labels with
  | single => exact .single _ _
  | cons turn tail ih => exact .cons (.right turn) ih

theorem PlugLabelling.splice {xs ys : List (PlugSegment c r)} (first : PlugLabelling c r xs a b)
    (second : PlugLabelling c r ys d e) (x y : PlugSegment c r)
    (last : xs.getLast?=some x) (head : ys.head?=some y)
    (seam : PlugTurn c r (plugSegmentWire c r x) y b d) : PlugLabelling c r (xs++ys) a e := by
  induction first with
  | single z a =>
    have same : z=x := Option.some.inj last
    subst z
    cases ys with
    | nil => cases head
    | cons z tail =>
      have same : z=y := Option.some.inj head
      subst z
      exact .cons seam second
  | cons turn tail ih =>
    exact .cons turn (ih (by simpa only [List.getLast?_cons_cons] using last) seam)

/-- General whole-path blocks for an arbitrary RHS, including actual
internal nodes, transparent vertices, repeated ports, and repeated visits. -/
inductive PlugExcursions : List (PlugSegment c r) → Context → Context → Prop where
  | single (e : Endpoint c) (a : Context) : PlugExcursions [.inl e] a a
  | outside {e f : Endpoint c} {tail : List (PlugSegment c r)} {a b d : Context}
      (turn : LabelledTurn c (c.wire e) f a b) (rest : PlugExcursions (.inl f::tail) b d) :
      PlugExcursions (.inl e::.inl f::tail) a d
  | through {e : Endpoint c} {enter exit : F} {tail : List (PlugSegment c r)} {a middle b : Context}
      (inside : LocalPath r enter exit a middle) (arrival : c.wire e=.inr (.inl (.inr enter)))
      (rest : PlugExcursions (.inl (.inr (.inl (.inr exit)))::tail) middle b) :
      PlugExcursions (.inl e::(inside.edges.map Sum.inr ++ .inl (.inr (.inl (.inr exit)))::tail)) a b

theorem PlugExcursions.labelling {es : List (PlugSegment c r)} (path : PlugExcursions c r es a b) :
    PlugLabelling c r es a b := by
  induction path with
  | single => exact .single _ _
  | outside turn rest ih => exact .cons (.left turn) ih
  | @through e enter exit tail a middle b inside arrival rest ih =>
    have right := PlugLabelling.of_right c r inside.labeling
    have rightLast : (inside.edges.map (Sum.inr : Endpoint r → PlugSegment c r)).getLast?=
        some (.inr (r.wire (.inr (.inl exit)))) := by rw [List.getLast?_map,inside.finish]; rfl
    have leave : PlugTurn c r (plugSegmentWire c r (.inr (r.wire (.inr (.inl exit)))))
        (.inl (.inr (.inl (.inr exit)))) middle middle := by
      change PlugTurn c r (.inr (r.wire (r.wire (.inr (.inl exit))))) _ _ _
      rw [Pairing.involutive]
      exact .leave exit middle
    have joined := right.splice c r ih _ _ rightLast rfl leave
    have joinedHead : (inside.edges.map (Sum.inr : Endpoint r → PlugSegment c r) ++ .inl (.inr (.inl (.inr exit)))::tail).head?=
        some (.inr (.inr (.inl enter)) : PlugSegment c r) := by
      rw [List.head?_append,List.head?_map,inside.start]
      rfl
    have entry : PlugTurn c r (plugSegmentWire c r (.inl e)) (.inr (.inr (.inl enter))) a a := by
      change PlugTurn c r (.inl (c.wire e)) _ _ _
      rw [arrival]
      exact .enter enter a
    exact (PlugLabelling.single (c:=c) (r:=r) (.inl e) a).splice c r joined _ _ rfl joinedHead entry

private theorem last_append {T : Type} (xs ys : List T) (nonempty : ys≠[]) :
    (xs++ys).getLast?=ys.getLast? := by
  rw [List.getLast?_append]
  cases same : ys.getLast? with
  | none => exact False.elim (nonempty (List.getLast?_eq_none_iff.mp same))
  | some => rfl

private theorem complete {es : List (PlugSegment c r)} (labels : PlugLabelling c r es a b)
    (first last : Endpoint c) (head : es.head?=some (.inl first)) (finish : es.getLast?=some (.inl last)) :
    PlugExcursions c r es a b := by
  cases labels with
  | single e a =>
    have same : e=.inl first := Option.some.inj head
    subst e
    exact .single _ _
  | @cons e next tail a middle b turn after =>
    have same : e=.inl first := Option.some.inj head
    subst e
    rcases turn.left_cases c r with ⟨nextLeft,same,localTurn⟩ | ⟨enter,arrival,nextEq,contexts⟩
    · subst next
      exact .outside localTurn (complete after nextLeft last rfl
        (by simpa only [List.getLast?_cons_cons] using finish))
    · subst next
      subst contexts
      rcases after.right_first c r with ⟨xs,stays,inside⟩ | ⟨xs,exit,rest,middle,split,inside,lastInside,afterExit⟩
      · rw [stays] at finish
        obtain ⟨endR,lastR⟩ : ∃ ending,(.inr (.inl enter)::xs).getLast?=some ending := by
          cases got : (.inr (.inl enter)::xs).getLast? with
          | none => have empty := List.getLast?_eq_none_iff.mp got; cases empty
          | some ending => exact ⟨ending,rfl⟩
        have impossible : (Sum.inl first::Sum.inr (.inr (.inl enter))::xs.map Sum.inr).getLast?=
            some (.inr endR : PlugSegment c r) := by
          rw [List.getLast?_cons_cons]
          change ((.inr (.inl enter)::xs).map (Sum.inr : Endpoint r → PlugSegment c r)).getLast?=_
          rw [List.getLast?_map,lastR]
          rfl
        rw [impossible] at finish
        cases finish
      · let child : LocalPath r enter exit _ middle := ⟨.inr (.inl enter)::xs,rfl,lastInside,inside⟩
        have lastRest : (.inl (.inr (.inl (.inr exit)))::rest).getLast?=some (.inl last) := by
          rw [split] at finish
          change ((.inl first:: .inr (.inr (.inl enter))::xs.map Sum.inr)++
            (.inl (.inr (.inl (.inr exit)))::rest)).getLast?=some (.inl last) at finish
          rw [last_append _ _ (by simp)] at finish
          exact finish
        rw [split]
        exact .through child arrival (complete afterExit _ last rfl lastRest)
termination_by es.length
decreasing_by all_goals simp_wf; simp_all only [List.length_cons,List.length_append,List.length_map]; omega

theorem PlugLabelling.local_excursions {es : List (PlugSegment c r)} (labels : PlugLabelling c r es a b)
    (first last : Endpoint c) (head : es.head?=some (.inl first)) (finish : es.getLast?=some (.inl last)) :
    PlugExcursions c r es a b := complete c r labels first last head finish

theorem Labelling.local_excursions {es : List (Endpoint (plug c r))}
    (labels : Labelling (plug c r) es a b) (first last : Endpoint c)
    (head : es.head?=some (AG.plugLeft c r first)) (finish : es.getLast?=some (AG.plugLeft c r last)) :
    PlugExcursions c r (es.map (plugEnd c.label r.label).invFun) a b := by
  apply (labels.plug_decomposition c r).local_excursions c r first last
  · rw [List.head?_map,head]
    exact congrArg some ((plugEnd c.label r.label).left_inv (.inl first))
  · rw [List.getLast?_map,finish]
    exact congrArg some ((plugEnd c.label r.label).left_inv (.inl last))
end
end Lamping.AG
