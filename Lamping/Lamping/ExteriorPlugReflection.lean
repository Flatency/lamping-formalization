import Lamping.Lamping.PlugPathDecomposition
namespace Lamping.AG
open Graph
section
variable {K R B F W V : Type} [FiniteNames K] [FiniteNames R] [FiniteNames B]
  [FiniteNames F] [FiniteNames W] [FiniteNames V]
variable (c : Net signature K (B⊕F) W) (r : Net signature R F V)

private theorem turn_left {x y : Endpoint c} {a b : Context}
    (turn : PlugTurn c r (.inl x) (.inl y) a b) : LabelledTurn c x y a b := by
  cases turn with
  | left actual => exact actual

private theorem all_left {es : List (Endpoint c)} {a b : Context}
    (labels : PlugLabelling c r (es.map Sum.inl) a b) : Labelling c es a b := by
  induction es generalizing a with
  | nil => cases labels
  | cons e es ih =>
    cases es with
    | nil => cases labels with | single => exact .single e _
    | cons f tail =>
      cases labels with
      | cons turn rest =>
        change PlugTurn c r (.inl (c.wire e)) (.inl f) a _ at turn
        exact .cons (turn_left c r turn) (ih rest)

/-- A labelled physical path consisting literally of left exterior segments
reflects with the same assignments. Glue crossings cannot disappear here. -/
theorem Labelling.plugLeft_reflect {es : List (Endpoint c)} {a b : Context}
    (labels : Labelling (plug c r) (es.map (AG.plugLeft c r)) a b) : Labelling c es a b := by
  have raw := labels.plug_decomposition c r
  rw [List.map_map] at raw
  have decoder : ((plugEnd c.label r.label).invFun ∘ AG.plugLeft c r)=Sum.inl :=
    funext (fun e => (plugEnd c.label r.label).left_inv (.inl e))
  rw [decoder] at raw
  exact all_left c r raw
end
end Lamping.AG

