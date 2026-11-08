import Lamping.Lambda.TargetHistoryPreimages
import Lamping.Lamping.UniformOldChainIncidencePreimages
import Lamping.Lamping.SuccessfulEndpointIso
namespace Lamping.AG
open Lambda Lambda.Labelled SyntaxIncidence

private theorem reflect_endpoint_chain
    {F ps : List Path} {m n : Marked} {d : Path →Option Label}
    {source target : LTerm} {degree : Label} {labels : History ps source target}
    {vertex : Vertex target} {oldVertex : Vertex source} {edges : List Path}
    (old : Marked.RelativeOldHistory F ps m n)
    (sourceClosed : Closed source.erase) (targetClosed : Closed target.erase)
    (aligned : DegreeAligned d m source)
    (selected : ∀path∈F,d path=some degree)
    (trace : BetaVertexHistoryPreimage labels vertex oldVertex)
    (chain : EndpointChain target vertex edges)
    (safe : ∀edge∈edges,∀node,target.subterm edge=some node →
      node.label.OuterBarsSafe (fun payload=>payload≠degree)) :
    ∃oldEdges,EndpointChain source oldVertex oldEdges ∧
      ChainIncidenceIsomorphic (chainSyntaxIncidence target targetClosed edges)
        (chainSyntaxIncidence source sourceClosed oldEdges) := by
  cases trace with
  | boundary => exact False.elim chain
  | @proper current original nodeTrace =>
    obtain ⟨oldStart,oldEdges,oldChain,startTrace,_,_,_,iso⟩ :=
      old.marker_free_chain_incidence_preimages sourceClosed targetClosed aligned labels selected chain safe
    have equal := startTrace.unique nodeTrace
    subst oldStart
    exact ⟨oldEdges,oldChain,iso⟩

/-- Target endpoint isomorphism reflects only when the two supplied successful
chains read marker-free incoming labels. The edge's own incoming may be marked. -/
theorem safe_read_old_target_endpoint_iso
    {F ps : List Path} {m n : Marked} {d : Path →Option Label}
    {source target : LTerm} {degree : Label} {labels : History ps source target}
    {leftEdge rightEdge oldLeftEdge oldRightEdge : Path}
    {left right : Vertex target} {leftEdges rightEdges : List Path}
    (old : Marked.RelativeOldHistory F ps m n)
    (sourceClosed : Closed source.erase) (targetClosed : Closed target.erase)
    (aligned : DegreeAligned d m source)
    (selected : ∀path∈F,d path=some degree)
    (leftTrace : BetaNodeHistoryPreimage labels leftEdge oldLeftEdge)
    (rightTrace : BetaNodeHistoryPreimage labels rightEdge oldRightEdge)
    (leftTarget : Target target leftEdge left) (rightTarget : Target target rightEdge right)
    (leftChain : EndpointChain target left leftEdges)
    (rightChain : EndpointChain target right rightEdges)
    (currentIso : ChainIncidenceIsomorphic (chainSyntaxIncidence target targetClosed leftEdges)
      (chainSyntaxIncidence target targetClosed rightEdges))
    (leftSafe : ∀edge∈leftEdges,∀node,target.subterm edge=some node →
      node.label.OuterBarsSafe (fun payload=>payload≠degree))
    (rightSafe : ∀edge∈rightEdges,∀node,target.subterm edge=some node →
      node.label.OuterBarsSafe (fun payload=>payload≠degree)) :
    ∃oldLeft oldRight,Target source oldLeftEdge oldLeft ∧Target source oldRightEdge oldRight ∧
      BetaVertexHistoryPreimage labels left oldLeft ∧
      BetaVertexHistoryPreimage labels right oldRight ∧
      SuccessfulEndpointIso source sourceClosed oldLeft oldRight := by
  obtain ⟨oldLeft,leftSpec,leftVertexTrace⟩ := leftTrace.target_history leftTarget
  obtain ⟨oldRight,rightSpec,rightVertexTrace⟩ := rightTrace.target_history rightTarget
  obtain ⟨oldLeftEdges,oldLeftChain,⟨leftIso⟩⟩ :=
    reflect_endpoint_chain old sourceClosed targetClosed aligned selected leftVertexTrace leftChain leftSafe
  obtain ⟨oldRightEdges,oldRightChain,⟨rightIso⟩⟩ :=
    reflect_endpoint_chain old sourceClosed targetClosed aligned selected rightVertexTrace rightChain rightSafe
  obtain ⟨currentIso⟩ := currentIso
  exact ⟨oldLeft,oldRight,leftSpec,rightSpec,leftVertexTrace,rightVertexTrace,
    oldLeftEdges,oldRightEdges,oldLeftChain,oldRightChain,
    ⟨leftIso.symm.trans (currentIso.trans rightIso)⟩⟩
end Lamping.AG
