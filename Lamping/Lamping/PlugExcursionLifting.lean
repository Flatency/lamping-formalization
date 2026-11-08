import Lamping.Lamping.PlugLocalExcursions
namespace Lamping.AG
open Graph
section
variable {K R B F W U N D V : Type} [FiniteNames K] [FiniteNames R] [FiniteNames B]
  [FiniteNames F] [FiniteNames W] [FiniteNames U] [FiniteNames N] [FiniteNames D] [FiniteNames V]
variable (c : Net signature K (B⊕F) W) (r : Net signature R F U)
variable (g : Net signature N D V) (embed : Endpoint c → Endpoint g)

private theorem last_append {T : Type} (pre tail : List T) (nonempty : tail≠[]) :
    (pre++tail).getLast?=tail.getLast? := by
  cases result : tail.getLast? with
  | none => exact False.elim (nonempty (List.getLast?_eq_none_iff.mp result))
  | some x => simp only [List.getLast?_append,result,Option.some_or]

/-- The raw RHS blocks and all ordered outside occurrences are retained;
each finite source block shares its last segment with the remaining path. -/
inductive LocalBlockResidual : List (PlugSegment c r) → List (Endpoint g) → Prop
  | single (e : Endpoint c) : LocalBlockResidual [.inl e] [embed e]
  | outside {e f : Endpoint c} {tail old}
      (rest : LocalBlockResidual (.inl f::tail) old) :
      LocalBlockResidual (.inl e::.inl f::tail) (embed e::old)
  | through {e : Endpoint c} {exit : F} {tail old}
      (inside : List (Endpoint r)) (front : List (Endpoint g))
      (start : (front++[embed (.inr (.inl (.inr exit)))]).head?=some (embed e))
      (rest : LocalBlockResidual (.inl (.inr (.inl (.inr exit)))::tail) old) :
      LocalBlockResidual (.inl e::(inside.map Sum.inr++ .inl (.inr (.inl (.inr exit)))::tail)) (front++old)

/-- Finite assembly preserves the given assignment. Its local-path premise
is explicit; actual action sites discharge it using proved inverse routes. -/
theorem PlugExcursions.lift_routes
    (wiring : ∀ e,g.wire (embed e)=embed (c.wire e))
    (turns : ∀ {x y a b},LabelledTurn c x y a b → LabelledTurn g (embed x) (embed y) a b)
    (routes : ∀ entry exit a b,LocalPath r entry exit a b →∃ path : List (Endpoint g),
      path.head?=some (g.wire (embed (.inr (.inl (.inr entry))))) ∧
      path.getLast?=some (embed (.inr (.inl (.inr exit)))) ∧Labelling g path a b)
    {es : List (PlugSegment c r)} {a b : Context} (path : PlugExcursions c r es a b)
    (first last : Endpoint c) (head : es.head?=some (.inl first))
    (finish : es.getLast?=some (.inl last)) :
    ∃ old,LocalBlockResidual c r g embed es old ∧Labelling g old a b ∧
      old.head?=some (embed first) ∧old.getLast?=some (embed last) := by
  induction path generalizing first last with
  | single e a =>
    have firstEq : e=first := Sum.inl.inj (Option.some.inj head)
    have lastEq : e=last := Sum.inl.inj (Option.some.inj finish)
    subst first; subst last
    exact ⟨[embed e],.single e,.single _ _,rfl,rfl⟩
  | @outside e f tail a middle b turn rest ih =>
    have firstEq : e=first := Sum.inl.inj (Option.some.inj head)
    subst first
    obtain ⟨old,residual,labels,oldHead,oldLast⟩ := ih f last rfl
      (by simpa only [List.getLast?_cons_cons] using finish)
    obtain ⟨post,split⟩ := List.head?_eq_some_iff.mp oldHead
    have actual := turns turn
    rw [←wiring] at actual
    refine ⟨embed e::old,.outside residual,?_,rfl,?_⟩
    · rw [split] at labels ⊢
      exact .cons actual labels
    · rw [split,List.getLast?_cons_cons]
      simpa only [split] using oldLast
  | @through e entry exit tail a middle b inside arrival rest ih =>
    have firstEq : e=first := Sum.inl.inj (Option.some.inj head)
    subst first
    have lastTail : (.inl (.inr (.inl (.inr exit)))::tail : List (PlugSegment c r)).getLast?=some (.inl last) := by
      have lastEq := last_append ([.inl e]++inside.edges.map (Sum.inr : Endpoint r → PlugSegment c r))
        (.inl (.inr (.inl (.inr exit)))::tail) (by simp)
      rw [←lastEq]
      exact finish
    obtain ⟨old,residual,labels,oldHead,oldLast⟩ := ih _ last rfl lastTail
    obtain ⟨route,routeHead,routeLast,routeLabels⟩ := routes entry exit a middle inside
    have start : route.head?=some (embed e) := by
      have comes : g.wire (embed e)=embed (.inr (.inl (.inr entry))) := by rw [wiring,arrival]
      rw [←comes,Pairing.involutive] at routeHead
      exact routeHead
    obtain ⟨front,routeSplit⟩ := List.getLast?_eq_some_iff.mp routeLast
    obtain ⟨post,oldSplit⟩ := List.head?_eq_some_iff.mp oldHead
    refine ⟨front++old,.through inside.edges front (by simpa only [routeSplit] using start) residual,?_,?_,?_⟩
    · rw [routeSplit] at routeLabels
      rw [oldSplit] at labels ⊢
      exact routeLabels.join labels
    · cases front with
      | nil =>
        have same : embed (.inr (.inl (.inr exit)))=embed e :=
          Option.some.inj (by simpa only [routeSplit,List.nil_append,List.head?_cons] using start)
        simpa only [List.nil_append,same] using oldHead
      | cons x front => simpa only [routeSplit,List.cons_append,List.head?_cons] using start
    · rw [List.getLast?_append,oldLast,Option.some_or]
end
end Lamping.AG

