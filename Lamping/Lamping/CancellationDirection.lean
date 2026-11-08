import Lamping.Lamping.CancellationAncestor
import Lamping.Lamping.FlowRootPaths
namespace Lamping.AG
open Graph
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature}

/-- Structural source flow supplies ordinary direction to the same labelled
cancellation ancestor, with its original assignment and boundary root. -/
theorem PathSite.cancellation_root_ancestor (cancel : IsCancellation s)
    (site : PathSite s kept (B:=B) (W:=W) (V:=V))
    {boundary : B → Bool} (flow : FlowBalance site.net boundary)
    (root : B) (rootPolarity : boundary root=true)
    {es : List (Endpoint site.reduce)} {a b : Context}
    (labels : Labelling site.reduce es a b)
    (rooted : es.head?=some (.inr (.inl root)))
    (last : Endpoint (cutFragment site.net (pathPartition s V) site.closed))
    (finish : es.getLast?=some (AG.plugLeft _ s.right.net last)) :
    ∃ old,CancellationResidual site es old ∧Labelling site.net old a b ∧Forward site.net old ∧
      old.head?=some (.inr (.inl root)) ∧old.getLast?=some (site.outsideEnd last) := by
  let first : Endpoint (cutFragment site.net (pathPartition s V) site.closed) := .inr (.inl (.inl root))
  have head : es.head?=some (AG.plugLeft _ s.right.net first) := rooted
  obtain ⟨old,residual,oldLabels,oldHead,oldLast⟩ := site.cancellation_ancestor cancel labels first last head finish
  have oldRoot : old.head?=some (.inr (.inl root)) := oldHead
  exact ⟨old,residual,oldLabels,oldLabels.root_forward_of_flow flow root oldRoot rootPolarity,oldRoot,oldLast⟩
end
end Lamping.AG
