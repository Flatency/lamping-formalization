import Lamping.Lamping.SafeReadTargetEndpointIso
import Lamping.Lambda.SafeIncomingHistory
namespace Lamping.AG
open Lambda Lambda.Labelled SyntaxIncidence

/-- Reflect a supplied successful, marker-free pair along its actual vertex
histories. Proper vertices are their own incoming TARGET; no private helper
or completion principle is needed. -/
theorem safe_read_old_vertex_endpoint_iso
    {F ps : List Path} {m n : Marked} {d : Path → Option Label}
    {source target : LTerm} {degree : Label} {labels : History ps source target}
    {left right : Vertex target} {oldLeft oldRight : Vertex source}
    {leftEdges rightEdges : List Path}
    (old : Marked.RelativeOldHistory F ps m n)
    (sourceClosed : Closed source.erase) (targetClosed : Closed target.erase)
    (aligned : DegreeAligned d m source) (selected : ∀p∈F,d p=some degree)
    (leftTrace : BetaVertexHistoryPreimage labels left oldLeft)
    (rightTrace : BetaVertexHistoryPreimage labels right oldRight)
    (leftChain : EndpointChain target left leftEdges)
    (rightChain : EndpointChain target right rightEdges)
    (currentIso : ChainIncidenceIsomorphic (chainSyntaxIncidence target targetClosed leftEdges)
      (chainSyntaxIncidence target targetClosed rightEdges))
    (leftSafe : ∀edge∈leftEdges,∀node,target.subterm edge=some node →
      node.label.OuterBarsSafe (fun x=>x≠degree))
    (rightSafe : ∀edge∈rightEdges,∀node,target.subterm edge=some node →
      node.label.OuterBarsSafe (fun x=>x≠degree)) :
    SuccessfulEndpointIso source sourceClosed oldLeft oldRight := by
  cases leftTrace with
  | boundary => exact False.elim leftChain
  | @proper left oldLeft leftTrace =>
    cases rightTrace with
    | boundary => exact False.elim rightChain
    | @proper right oldRight rightTrace =>
      obtain ⟨a,b,ha,hb,_,_,iso⟩ := safe_read_old_target_endpoint_iso old
        sourceClosed targetClosed aligned selected leftTrace rightTrace
        (show Target target left.val (some left) from Or.inl rfl)
        (show Target target right.val (some right) from Or.inl rfl) leftChain rightChain currentIso leftSafe rightSafe
      have ea := Target.unique ha (show Target source oldLeft.val (some oldLeft) from Or.inl rfl)
      have eb := Target.unique hb (show Target source oldRight.val (some oldRight) from Or.inl rfl)
      exact ea ▸ eb ▸ iso

/-- An uncreated incoming supplies actual SOURCE ancestry. Chain-wide READ
safety remains an independent hypothesis, even when that incoming is safe. -/
theorem safe_read_uncreated_old_source_endpoint_iso
    {F ps : List Path} {m n : Marked} {d : Path → Option Label}
    {source target leftNode rightNode : LTerm} {degree : Label}
    {labels : History ps source target} {p q oldP oldQ : Path}
    {left right : Vertex target} {leftEdges rightEdges : List Path}
    (old : Marked.RelativeOldHistory F ps m n)
    (sourceClosed : Closed source.erase) (targetClosed : Closed target.erase)
    (aligned : DegreeAligned d m source) (selected : ∀p∈F,d p=some degree)
    (leftTrace : UncreatedNodeHistoryPreimage labels p oldP)
    (rightTrace : UncreatedNodeHistoryPreimage labels q oldQ)
    (leftLookup : target.subterm p=some leftNode) (rightLookup : target.subterm q=some rightNode)
    (leftSource : Source target p left) (rightSource : Source target q right)
    (leftChain : EndpointChain target left leftEdges) (rightChain : EndpointChain target right rightEdges)
    (currentIso : ChainIncidenceIsomorphic (chainSyntaxIncidence target targetClosed leftEdges)
      (chainSyntaxIncidence target targetClosed rightEdges))
    (leftSafe : ∀edge∈leftEdges,∀node,target.subterm edge=some node →
      node.label.OuterBarsSafe (fun x=>x≠degree))
    (rightSafe : ∀edge∈rightEdges,∀node,target.subterm edge=some node →
      node.label.OuterBarsSafe (fun x=>x≠degree)) :
    ∃oldLeft oldRight,Source source oldP oldLeft ∧Source source oldQ oldRight ∧
      BetaVertexHistoryPreimage labels left oldLeft ∧BetaVertexHistoryPreimage labels right oldRight ∧
      SuccessfulEndpointIso source sourceClosed oldLeft oldRight := by
  obtain ⟨_,a,_,_,ha,ta⟩ := leftTrace.source_history leftLookup leftSource
  obtain ⟨_,b,_,_,hb,tb⟩ := rightTrace.source_history rightLookup rightSource
  exact ⟨a,b,ha,hb,ta,tb,safe_read_old_vertex_endpoint_iso old sourceClosed targetClosed
    aligned selected ta tb leftChain rightChain currentIso leftSafe rightSafe⟩

/-- Safe incoming labels exclude creation on THIS lineage; successful chain
reflection additionally requires the separately supplied READ-safety. -/
theorem safe_incoming_safe_read_old_source_endpoint_iso
    {F ps : List Path} {m n : Marked} {d : Path → Option Label}
    {source target leftNode rightNode : LTerm} {degree : Label}
    {labels : History ps source target} {p q oldP oldQ : Path}
    {left right : Vertex target} {leftEdges rightEdges : List Path}
    (old : Marked.RelativeOldHistory F ps m n)
    (sourceClosed : Closed source.erase) (targetClosed : Closed target.erase)
    (aligned : DegreeAligned d m source) (selected : ∀p∈F,d p=some degree)
    (leftTrace : BetaNodeHistoryPreimage labels p oldP)
    (rightTrace : BetaNodeHistoryPreimage labels q oldQ)
    (leftLookup : target.subterm p=some leftNode) (rightLookup : target.subterm q=some rightNode)
    (leftIncomingSafe : leftNode.label.OuterBarsSafe (fun x=>x≠degree))
    (rightIncomingSafe : rightNode.label.OuterBarsSafe (fun x=>x≠degree))
    (leftSource : Source target p left) (rightSource : Source target q right)
    (leftChain : EndpointChain target left leftEdges) (rightChain : EndpointChain target right rightEdges)
    (currentIso : ChainIncidenceIsomorphic (chainSyntaxIncidence target targetClosed leftEdges)
      (chainSyntaxIncidence target targetClosed rightEdges))
    (leftSafe : ∀edge∈leftEdges,∀node,target.subterm edge=some node →
      node.label.OuterBarsSafe (fun x=>x≠degree))
    (rightSafe : ∀edge∈rightEdges,∀node,target.subterm edge=some node →
      node.label.OuterBarsSafe (fun x=>x≠degree)) :
    ∃oldLeft oldRight,Source source oldP oldLeft ∧Source source oldQ oldRight ∧
      BetaVertexHistoryPreimage labels left oldLeft ∧BetaVertexHistoryPreimage labels right oldRight ∧
      SuccessfulEndpointIso source sourceClosed oldLeft oldRight := by
  exact safe_read_uncreated_old_source_endpoint_iso old sourceClosed targetClosed aligned selected
    (old.safe_incoming_uncreated aligned selected leftTrace leftLookup leftIncomingSafe)
    (old.safe_incoming_uncreated aligned selected rightTrace rightLookup rightIncomingSafe)
    leftLookup rightLookup leftSource rightSource leftChain rightChain currentIso leftSafe rightSafe

#print axioms safe_read_old_vertex_endpoint_iso
#print axioms safe_read_uncreated_old_source_endpoint_iso
#print axioms safe_incoming_safe_read_old_source_endpoint_iso
end Lamping.AG
