import Lamping.Lamping.CancellationRoutes
import Lamping.Lamping.WireExcursionLifting
namespace Lamping.AG
open Graph
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature}

/-- The actual cut/plug inverse and the same literal outside occurrences are
retained in the finite cancellation block replacement. -/
def CancellationResidual
    (site : PathSite s kept (B:=B) (W:=W) (V:=V))
    (es : List (Endpoint site.reduce)) (old : List (Endpoint site.net)) : Prop := by
  cases s with
  | fanCancel i =>
    exact WireBlockResidual (cutFragment site.net (pathPartition (Schema.fanCancel i) V) site.closed)
      (Schema.fanCancel i).right.net site.net
      site.outsideEnd (es.map (plugEnd _ _).invFun) old
  | croCancel i =>
    exact WireBlockResidual (cutFragment site.net (pathPartition (Schema.croCancel i) V) site.closed)
      (Schema.croCancel i).right.net site.net
      site.outsideEnd (es.map (plugEnd _ _).invFun) old
  | braCancel i =>
    exact WireBlockResidual (cutFragment site.net (pathPartition (Schema.braCancel i) V) site.closed)
      (Schema.braCancel i).right.net site.net
      site.outsideEnd (es.map (plugEnd _ _).invFun) old
  | beta => exact False
  | fanAction => exact False
  | croAction => exact False
  | braAction => exact False

/-- Every actual complete outside-ended path after a standard cancellation
has a same-assignment ordinary source ancestor, with finite ordered residual.
This is a local path theorem, not SND or Matches preservation. -/
theorem PathSite.cancellation_ancestor (cancel : IsCancellation s)
    (site : PathSite s kept (B:=B) (W:=W) (V:=V))
    {es : List (Endpoint site.reduce)} {a b : Context}
    (labels : Labelling site.reduce es a b)
    (first last : Endpoint (cutFragment site.net (pathPartition s V) site.closed))
    (head : es.head?=some (AG.plugLeft _ s.right.net first))
    (finish : es.getLast?=some (AG.plugLeft _ s.right.net last)) :
    ∃ old,CancellationResidual site es old ∧Labelling site.net old a b ∧
      old.head?=some (site.outsideEnd first) ∧old.getLast?=some (site.outsideEnd last) := by
  cases cancel with
  | fan i =>
    have raw := labels.wire_excursions _ _ first last head finish
    exact raw.lift_routes _ (Schema.fanCancel i).right.net site.net site.outsideEnd site.outsideEnd_wire
      (fun turn => turn.outsideEnd site) (fun f a => by
        have actual := site.cancellation_route (.fan i) f a
        cases f <;> exact actual)
      first last (by rw [List.head?_map,head]; exact congrArg some ((plugEnd _ _).left_inv (.inl first))) (by rw [List.getLast?_map,finish]; exact congrArg some ((plugEnd _ _).left_inv (.inl last)))
  | cro i =>
    have raw := labels.wire_excursions _ _ first last head finish
    exact raw.lift_routes _ (Schema.croCancel i).right.net site.net site.outsideEnd site.outsideEnd_wire
      (fun turn => turn.outsideEnd site) (fun f a => by
        have actual := site.cancellation_route (.cro i) f a
        cases f <;> exact actual)
      first last (by rw [List.head?_map,head]; exact congrArg some ((plugEnd _ _).left_inv (.inl first))) (by rw [List.getLast?_map,finish]; exact congrArg some ((plugEnd _ _).left_inv (.inl last)))
  | bra i =>
    have raw := labels.wire_excursions _ _ first last head finish
    exact raw.lift_routes _ (Schema.braCancel i).right.net site.net site.outsideEnd site.outsideEnd_wire
      (fun turn => turn.outsideEnd site) (fun f a => by
        have actual := site.cancellation_route (.bra i) f a
        cases f <;> exact actual)
      first last (by rw [List.head?_map,head]; exact congrArg some ((plugEnd _ _).left_inv (.inl first))) (by rw [List.getLast?_map,finish]; exact congrArg some ((plugEnd _ _).left_inv (.inl last)))
end
end Lamping.AG



