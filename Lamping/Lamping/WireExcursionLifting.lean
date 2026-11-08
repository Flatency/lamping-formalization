import Lamping.Lamping.WireRhsExcursions
import Lamping.Lamping.PathSplicing
namespace Lamping.AG
open Graph
section
variable {K B F W N D V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames F]
  [FiniteNames W] [FiniteNames N] [FiniteNames D] [FiniteNames V]
variable (c : Net signature K (B⊕F) W) (r : Net signature Empty F Empty)
variable (g : Net signature N D V) (embed : Endpoint c → Endpoint g)

/-- Literal ordered outside occurrences and finite replacement blocks. This
relation makes no claim about labels, generation, or invariant preservation. -/
inductive WireBlockResidual : List (PlugSegment c r) → List (Endpoint g) → Prop
  | single (e : Endpoint c) : WireBlockResidual [.inl e] [embed e]
  | outside {e f : Endpoint c} {tail old}
      (rest : WireBlockResidual (.inl f::tail) old) :
      WireBlockResidual (.inl e::.inl f::tail) (embed e::old)
  | through {e : Endpoint c} {f : F} {tail old} (front : List (Endpoint g))
      (start : (front++[embed (.inr (.inl (.inr (wireBoundaryMate r f))))]).head?=some (embed e))
      (rest : WireBlockResidual (.inl (.inr (.inl (.inr (wireBoundaryMate r f))))::tail) old) :
      WireBlockResidual (.inl e::.inr (.inr (.inl f))::
        .inl (.inr (.inl (.inr (wireBoundaryMate r f))))::tail) (front++old)

/-- Compose independently proved local source routes along the actual finite
wire-RHS decomposition. The whole target path's supplied A/B is retained. -/
theorem WireExcursions.lift_routes
    (wiring : ∀ e,g.wire (embed e)=embed (c.wire e))
    (turns : ∀ {x y a b},LabelledTurn c x y a b → LabelledTurn g (embed x) (embed y) a b)
    (routes : ∀ f a,∃ path : List (Endpoint g),
      path.head?=some (g.wire (embed (.inr (.inl (.inr f))))) ∧
      path.getLast?=some (embed (.inr (.inl (.inr (wireBoundaryMate r f))))) ∧Labelling g path a a)
    {es : List (PlugSegment c r)} {a b : Context} (path : WireExcursions c r es a b)
    (first last : Endpoint c) (head : es.head?=some (.inl first))
    (finish : es.getLast?=some (.inl last)) :
    ∃ old,WireBlockResidual c r g embed es old ∧Labelling g old a b ∧
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
  | @through e f tail a b arrival rest ih =>
    have firstEq : e=first := Sum.inl.inj (Option.some.inj head)
    subst first
    obtain ⟨old,residual,labels,oldHead,oldLast⟩ := ih _ last rfl
      (by simpa only [List.getLast?_cons_cons] using finish)
    obtain ⟨route,routeHead,routeLast,routeLabels⟩ := routes f a
    have start : route.head?=some (embed e) := by
      have comes : g.wire (embed e)=embed (.inr (.inl (.inr f))) := by rw [wiring,arrival]
      rw [←comes,Pairing.involutive] at routeHead
      exact routeHead
    obtain ⟨front,routeSplit⟩ := List.getLast?_eq_some_iff.mp routeLast
    obtain ⟨post,oldSplit⟩ := List.head?_eq_some_iff.mp oldHead
    refine ⟨front++old,.through front (by simpa only [routeSplit] using start) residual,?_,?_,?_⟩
    · rw [routeSplit] at routeLabels
      rw [oldSplit] at labels ⊢
      exact routeLabels.join labels
    · cases front with
      | nil =>
        have same : embed (.inr (.inl (.inr (wireBoundaryMate r f))))=embed e :=
          Option.some.inj (by simpa only [routeSplit,List.nil_append,List.head?_cons] using start)
        simpa only [List.nil_append,same] using oldHead
      | cons x front => simpa only [routeSplit,List.cons_append,List.head?_cons] using start
    · rw [List.getLast?_append,oldLast,Option.some_or]
end
end Lamping.AG

