import Lamping.Lamping.UniformWireResidual
import Lamping.Lamping.CancellationUniformRoutes
import Lamping.Lamping.CancellationAncestor
namespace Lamping.AG
open Graph
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))

private theorem reflect_outside {x y : Endpoint (cutFragment site.net (pathPartition s V) site.closed)}
    {originalA originalB a b : Context}
    (shape : LabelledTurn (cutFragment site.net (pathPartition s V) site.closed) x y originalA originalB)
    (turn : LabelledTurn site.net (site.outsideEnd x) (site.outsideEnd y) a b) :
    LabelledTurn (cutFragment site.net (pathPartition s V) site.closed) x y a b := by
  cases shape with
  | node node p q rule =>
    change LabelledTurn site.net (.inl ⟨.inl node,p⟩) (.inl ⟨.inl node,q⟩) a b at turn
    cases turn with
    | node node p q actual => exact .node _ _ _ actual
  | transparent vertex direction context =>
    change LabelledTurn site.net (.inr (.inr (.inl vertex,direction)))
      (.inr (.inr (.inl vertex,!direction))) a b at turn
    cases turn
    exact .transparent vertex direction a

/-- Choose the actual old cancellation ancestor once, then replay EVERY new
assignment on that same physical ancestor onto the original reduced path.
The strengthened finite residual is constructed from actual uniform routes;
the old arbitrary-front residual alone is not used to justify contraction. -/
theorem PathSite.cancellation_relabelling_ancestor (cancel : IsCancellation s)
    {es : List (Endpoint site.reduce)} {a b : Context}
    (labels : Labelling site.reduce es a b)
    (first last : Endpoint (cutFragment site.net (pathPartition s V) site.closed))
    (head : es.head?=some (AG.plugLeft _ s.right.net first))
    (finish : es.getLast?=some (AG.plugLeft _ s.right.net last)) :
    ∃ old,CancellationResidual site es old ∧Labelling site.net old a b ∧
      old.head?=some (site.outsideEnd first) ∧old.getLast?=some (site.outsideEnd last) ∧
      ∀ input output,Labelling site.net old input output → Labelling site.reduce es input output := by
  cases cancel with
  | fan i =>
    obtain ⟨old,residual,oldLabels,oldHead,oldLast,replay⟩ := labels.uniform_wire_ancestor _ _ site.net
      site.outsideEnd site.outsideEnd_wire (fun turn => turn.outsideEnd site)
      (fun shape turn => reflect_outside site shape turn)
      (fun f => by have actual := site.cancellation_uniform_route (.fan i) f; cases f <;> exact actual)
      first last head finish
    exact ⟨old,residual.erase _ _ _ _,oldLabels,oldHead,oldLast,replay⟩
  | cro i =>
    obtain ⟨old,residual,oldLabels,oldHead,oldLast,replay⟩ := labels.uniform_wire_ancestor _ _ site.net
      site.outsideEnd site.outsideEnd_wire (fun turn => turn.outsideEnd site)
      (fun shape turn => reflect_outside site shape turn)
      (fun f => by have actual := site.cancellation_uniform_route (.cro i) f; cases f <;> exact actual)
      first last head finish
    exact ⟨old,residual.erase _ _ _ _,oldLabels,oldHead,oldLast,replay⟩
  | bra i =>
    obtain ⟨old,residual,oldLabels,oldHead,oldLast,replay⟩ := labels.uniform_wire_ancestor _ _ site.net
      site.outsideEnd site.outsideEnd_wire (fun turn => turn.outsideEnd site)
      (fun shape turn => reflect_outside site shape turn)
      (fun f => by have actual := site.cancellation_uniform_route (.bra i) f; cases f <;> exact actual)
      first last head finish
    exact ⟨old,residual.erase _ _ _ _,oldLabels,oldHead,oldLast,replay⟩
end
end Lamping.AG
