import Lamping.Lamping.WireExcursionLifting
import Lamping.Lamping.PathLabelDeterminism
namespace Lamping.AG
open Graph
section
variable {K B F W N D V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames F]
  [FiniteNames W] [FiniteNames N] [FiniteNames D] [FiniteNames V]
variable (c : Net signature K (B⊕F) W) (r : Net signature Empty F Empty)
variable (g : Net signature N D V) (embed : Endpoint c → Endpoint g)

/-- A new finite residual which records the chosen constant-context local
routes. The old WireBlockResidual allows arbitrary fronts and is unchanged. -/
inductive UniformWireResidual : List (PlugSegment c r) → List (Endpoint g) → Prop where
  | single (e : Endpoint c) : UniformWireResidual [.inl e] [embed e]
  | outside {e f : Endpoint c} {tail old}
      (rest : UniformWireResidual (.inl f::tail) old) :
      UniformWireResidual (.inl e::.inl f::tail) (embed e::old)
  | through {e : Endpoint c} {f : F} {tail old} (front : List (Endpoint g))
      (start : (front++[embed (.inr (.inl (.inr (wireBoundaryMate r f))))]).head?=some (embed e))
      (identity : ∀ a,Labelling g (front++[embed (.inr (.inl (.inr (wireBoundaryMate r f))))]) a a)
      (rest : UniformWireResidual (.inl (.inr (.inl (.inr (wireBoundaryMate r f))))::tail) old) :
      UniformWireResidual (.inl e::.inr (.inr (.inl f))::
        .inl (.inr (.inl (.inr (wireBoundaryMate r f))))::tail) (front++old)

theorem UniformWireResidual.erase {raw old} (relation : UniformWireResidual c r g embed raw old) :
    WireBlockResidual c r g embed raw old := by
  induction relation with
  | single e => exact .single e
  | outside rest ih => exact .outside ih
  | through front start identity rest ih => exact .through front start ih

theorem UniformWireResidual.head {raw old} (relation : UniformWireResidual c r g embed raw old)
    {e : Endpoint c} (first : raw.head?=some (.inl e)) : old.head?=some (embed e) := by
  induction relation generalizing e with
  | single f => have same := Sum.inl.inj (Option.some.inj first); subst f; rfl
  | @outside f h tail old rest ih =>
    have same := Sum.inl.inj (Option.some.inj first)
    subst f
    rfl
  | @through f h tail old front start identity rest ih =>
    have same := Sum.inl.inj (Option.some.inj first)
    subst f
    cases front with
    | nil =>
      have endpoint : embed (.inr (.inl (.inr (wireBoundaryMate r h))))=embed e := Option.some.inj start
      simpa only [List.nil_append,endpoint] using ih rfl
    | cons x front => simpa only [List.cons_append,List.head?_cons] using start

/-- Contract any new assignment on the fixed chosen ancestor. Only the
original outside turn shapes are reused, and local constants are proved per
recorded physical block. This is finite composition, not a graph invariant. -/
theorem UniformWireResidual.contract
    (wiring : ∀ e,g.wire (embed e)=embed (c.wire e))
    (reflectTurn : ∀ {x y originalA originalB a b},LabelledTurn c x y originalA originalB →
      LabelledTurn g (embed x) (embed y) a b → LabelledTurn c x y a b)
    {raw old} (relation : UniformWireResidual c r g embed raw old)
    {originalA originalB a b : Context} (shape : WireExcursions c r raw originalA originalB)
    (labels : Labelling g old a b) : WireExcursions c r raw a b := by
  induction relation generalizing originalA originalB a b with
  | single e => cases labels; exact .single _ _
  | @outside e f raw old rest ih =>
    cases shape with
    | outside turn after =>
      have oldHead := rest.head c r g embed rfl
      obtain ⟨post,split⟩ := List.head?_eq_some_iff.mp oldHead
      rw [split] at labels
      cases labels with
      | cons newTurn remaining =>
        rw [wiring] at newTurn
        exact .outside (reflectTurn turn newTurn) (ih after (by simpa only [split] using remaining))
  | @through e f raw old front start identity rest ih =>
    cases shape with
    | through arrival after =>
      have oldHead := rest.head c r g embed rfl
      obtain ⟨post,split⟩ := List.head?_eq_some_iff.mp oldHead
      rw [split] at labels
      obtain ⟨middle,before,remaining⟩ := labels.split_segment
      have same := before.output_unique (identity a)
      rw [same] at remaining
      exact .through arrival (ih after (by simpa only [split] using remaining))
theorem WireExcursions.uniform_lift_routes
    (wiring : ∀ e,g.wire (embed e)=embed (c.wire e))
    (turns : ∀ {x y a b},LabelledTurn c x y a b → LabelledTurn g (embed x) (embed y) a b)
    (routes : ∀ f,∃ path : List (Endpoint g),
      path.head?=some (g.wire (embed (.inr (.inl (.inr f))))) ∧
      path.getLast?=some (embed (.inr (.inl (.inr (wireBoundaryMate r f))))) ∧∀ a,Labelling g path a a)
    {es : List (PlugSegment c r)} {a b : Context} (path : WireExcursions c r es a b)
    (first last : Endpoint c) (head : es.head?=some (.inl first))
    (finish : es.getLast?=some (.inl last)) :
    ∃ old,UniformWireResidual c r g embed es old ∧Labelling g old a b ∧
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
    obtain ⟨route,routeHead,routeLast,routeUniform⟩ := routes f
    have routeLabels := routeUniform a
    have start : route.head?=some (embed e) := by
      have comes : g.wire (embed e)=embed (.inr (.inl (.inr f))) := by rw [wiring,arrival]
      rw [←comes,Pairing.involutive] at routeHead
      exact routeHead
    obtain ⟨front,routeSplit⟩ := List.getLast?_eq_some_iff.mp routeLast
    obtain ⟨post,oldSplit⟩ := List.head?_eq_some_iff.mp oldHead
    refine ⟨front++old,.through front (by simpa only [routeSplit] using start) (by intro newInput; simpa only [routeSplit] using routeUniform newInput) residual,?_,?_,?_⟩
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
theorem Labelling.uniform_wire_ancestor
    (wiring : ∀ e,g.wire (embed e)=embed (c.wire e))
    (turns : ∀ {x y a b},LabelledTurn c x y a b → LabelledTurn g (embed x) (embed y) a b)
    (reflectTurn : ∀ {x y originalA originalB a b},LabelledTurn c x y originalA originalB →
      LabelledTurn g (embed x) (embed y) a b → LabelledTurn c x y a b)
    (routes : ∀ f,∃ path : List (Endpoint g),
      path.head?=some (g.wire (embed (.inr (.inl (.inr f))))) ∧
      path.getLast?=some (embed (.inr (.inl (.inr (wireBoundaryMate r f))))) ∧∀ a,Labelling g path a a)
    {es : List (Endpoint (plug c r))} {a b : Context} (labels : Labelling (plug c r) es a b)
    (first last : Endpoint c) (head : es.head?=some (AG.plugLeft c r first))
    (finish : es.getLast?=some (AG.plugLeft c r last)) :
    ∃ old,UniformWireResidual c r g embed (es.map (plugEnd _ _).invFun) old ∧
      Labelling g old a b ∧old.head?=some (embed first) ∧old.getLast?=some (embed last) ∧
      ∀ input output,Labelling g old input output → Labelling (plug c r) es input output := by
  have shape := labels.wire_excursions c r first last head finish
  obtain ⟨old,residual,oldLabels,oldHead,oldLast⟩ := shape.uniform_lift_routes c r g embed wiring turns routes
    first last (by rw [List.head?_map,head]; exact congrArg some ((plugEnd _ _).left_inv (.inl first)))
    (by rw [List.getLast?_map,finish]; exact congrArg some ((plugEnd _ _).left_inv (.inl last)))
  refine ⟨old,residual,oldLabels,oldHead,oldLast,?_⟩
  intro input output changed
  have contracted := (residual.contract c r g embed wiring reflectTurn shape changed).labelling c r
  have physical := contracted.actual c r
  simpa only [plug_decomposition_flatten] using physical
end
end Lamping.AG


