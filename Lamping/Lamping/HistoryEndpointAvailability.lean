import Lamping.Lamping.AuxiliaryEndpointAvailability
namespace Lamping.AG
open Lambda Lambda.Labelled SyntaxIncidence
/-- Backward availability through the SAME actual finite node history.
The two old endpoint chains may change at created roots; there is no claimed
source-vertex history map, list equality, chain isomorphism or representation. -/
theorem history_edge_endpoint_availability
    {ps : List Path} {source target current : LTerm} {labels : History ps source target}
    {edge oldEdge : Path} {fromVertex toVertex : Vertex target}
    {sourceEdges targetEdges : List Path}
    (trace : BetaNodeHistoryPreimage labels edge oldEdge)
    (lookup : target.subterm edge=some current)
    (fromSpec : Source target edge fromVertex) (toSpec : Target target edge toVertex)
    (fromChain : EndpointChain target fromVertex sourceEdges)
    (toChain : EndpointChain target toVertex targetEdges) :
    ∃original oldFrom oldTo oldSourceEdges oldTargetEdges,
      source.subterm oldEdge=some original ∧
      Source source oldEdge oldFrom ∧Target source oldEdge oldTo ∧
      EndpointChain source oldFrom oldSourceEdges ∧EndpointChain source oldTo oldTargetEdges := by
  induction trace generalizing current sourceEdges targetEdges with
  | nil => exact ⟨current,fromVertex,toVertex,sourceEdges,targetEdges,lookup,fromSpec,toSpec,fromChain,toChain⟩
  | @one site ps source middle target body argument beta alpha edge mid oldEdge step remaining redex origin tail ih =>
    obtain ⟨midNode,midFrom,midTo,midSourceEdges,midTargetEdges,midLookup,
        midFromSpec,midToSpec,midFromChain,midToChain⟩ := ih lookup fromSpec toSpec fromChain toChain
    obtain ⟨original,oldLookup,_⟩ := step.preimage_node_constructor redex origin midLookup
    obtain ⟨oldFrom,oldTo,oldSourceEdges,oldTargetEdges,oldFromSpec,oldToSpec,oldFromChain,oldToChain⟩ :=
      old_edge_endpoint_availability step redex origin midLookup midFromSpec midToSpec midFromChain midToChain
    exact ⟨original,oldFrom,oldTo,oldSourceEdges,oldTargetEdges,oldLookup,
      oldFromSpec,oldToSpec,oldFromChain,oldToChain⟩
#print axioms history_edge_endpoint_availability
end Lamping.AG
