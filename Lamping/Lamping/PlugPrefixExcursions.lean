import Lamping.Lamping.PlugLocalExcursions
namespace Lamping.AG
open Graph
section
variable {K R B F W V : Type} [FiniteNames K] [FiniteNames R] [FiniteNames B]
  [FiniteNames F] [FiniteNames W] [FiniteNames V]
variable (c : Net signature K (B⊕F) W) (r : Net signature R F V)

/-- Actual finite paths with an optional final, genuinely truncated RHS
block. No extension or complete-outside-end condition is required. -/
inductive PlugPrefixExcursions : List (PlugSegment c r) → Context → Context → Prop
  | single (e : Endpoint c) (a : Context) : PlugPrefixExcursions [.inl e] a a
  | outside {e f : Endpoint c} {tail} {a middle b : Context}
      (turn : LabelledTurn c (c.wire e) f a middle)
      (rest : PlugPrefixExcursions (.inl f::tail) middle b) :
      PlugPrefixExcursions (.inl e::.inl f::tail) a b
  | through {e : Endpoint c} {enter exit : F} {tail} {a middle b : Context}
      (inside : LocalPath r enter exit a middle) (arrival : c.wire e=.inr (.inl (.inr enter)))
      (rest : PlugPrefixExcursions (.inl (.inr (.inl (.inr exit)))::tail) middle b) :
      PlugPrefixExcursions (.inl e::(inside.edges.map Sum.inr++ .inl (.inr (.inl (.inr exit)))::tail)) a b
  | pending {e : Endpoint c} {enter : F} (xs : List (Endpoint r)) {a b : Context}
      (arrival : c.wire e=.inr (.inl (.inr enter)))
      (inside : Labelling r (.inr (.inl enter)::xs) a b) :
      PlugPrefixExcursions (.inl e::.inr (.inr (.inl enter))::xs.map Sum.inr) a b

theorem PlugPrefixExcursions.labelling {es : List (PlugSegment c r)}
    {a b : Context} (path : PlugPrefixExcursions c r es a b) : PlugLabelling c r es a b := by
  induction path with
  | single e a => exact .single _ _
  | outside turn rest ih => exact .cons (.left turn) ih
  | @pending e enter xs a b arrival inside =>
    have rhs := PlugLabelling.of_right c r inside
    apply PlugLabelling.cons
    · change PlugTurn c r (.inl (c.wire e)) (.inr (.inr (.inl enter))) a a
      rw [arrival]
      exact .enter _ _
    · exact rhs
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

private theorem decompose {es : List (PlugSegment c r)} {a b : Context}
    (labels : PlugLabelling c r es a b) (first : Endpoint c)
    (head : es.head?=some (.inl first)) : PlugPrefixExcursions c r es a b := by
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
      exact .outside localTurn (decompose after nextLeft rfl)
    · subst next
      subst contexts
      rcases after.right_first c r with ⟨xs,stays,inside⟩ |⟨xs,exit,rest,middle,split,inside,lastInside,afterExit⟩
      · rw [stays]
        exact .pending xs arrival inside
      · let child : LocalPath r enter exit _ middle := ⟨.inr (.inl enter)::xs,rfl,lastInside,inside⟩
        rw [split]
        exact .through child arrival (decompose afterExit _ rfl)
termination_by es.length
decreasing_by all_goals simp_wf; simp_all only [List.length_cons,List.length_append,List.length_map]; omega

theorem PlugLabelling.prefix_excursions {es : List (PlugSegment c r)} {a b : Context}
    (labels : PlugLabelling c r es a b) (first : Endpoint c)
    (head : es.head?=some (.inl first)) : PlugPrefixExcursions c r es a b := decompose c r labels first head

theorem Labelling.prefix_excursions {es : List (Endpoint (plug c r))} {a b : Context}
    (labels : Labelling (plug c r) es a b) (first : Endpoint c)
    (head : es.head?=some (AG.plugLeft c r first)) :
    PlugPrefixExcursions c r (es.map (plugEnd c.label r.label).invFun) a b := by
  apply (labels.plug_decomposition c r).prefix_excursions c r first
  rw [List.head?_map,head]
  exact congrArg some ((plugEnd c.label r.label).left_inv (.inl first))
end
end Lamping.AG

