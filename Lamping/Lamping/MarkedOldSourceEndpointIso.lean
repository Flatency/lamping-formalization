import Lamping.Lamping.SelectedNodeSourceOrigins
import Lamping.Lamping.RedexChainDegrees
import Lamping.Lamping.SuccessfulEndpointIso
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
/-- Two marked incoming lineages in the SAME actual uniform OLD history have
successful isomorphic original SOURCE chains. Actual source specs fix the
vertices; neither an endpoint iso nor a chosen original name is a premise. -/
theorem marked_old_source_endpoint_iso
    {F ps : List Path} {n : Lambda.Marked} {source target leftCurrent rightCurrent : LTerm}
    {labels : History ps source target} {p q oldP oldQ : Path} {alpha : Label}
    {leftSource rightSource : SyntaxIncidence.Vertex source}
    (closed : Closed source.erase)
    (old : Marked.RelativeOldHistory F ps (Marked.mark F source.erase) n)
    (selected : ∀name∈F,source.degreeAt name=some alpha)
    (leftTrace : BetaNodeHistoryPreimage labels p oldP)
    (rightTrace : BetaNodeHistoryPreimage labels q oldQ)
    (leftLookup : target.subterm p=some leftCurrent)
    (rightLookup : target.subterm q=some rightCurrent)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠alpha))
    (leftMarked : ¬leftCurrent.label.OuterBarsSafe (fun x=>x≠alpha))
    (rightMarked : ¬rightCurrent.label.OuterBarsSafe (fun x=>x≠alpha))
    (leftSpec : SyntaxIncidence.Source source oldP leftSource)
    (rightSpec : SyntaxIncidence.Source source oldQ rightSource) :
    SuccessfulEndpointIso source closed leftSource rightSource := by
  obtain ⟨leftName,leftChosen,leftBeta,leftBody,leftArg,leftRedex,
      leftNode,leftVertex,_leftAt,leftIncidence,_leftPosition,leftChain⟩ :=
    marked_node_source_selected old selected leftTrace leftLookup sourceSafe leftMarked
  obtain ⟨rightName,rightChosen,rightBeta,rightBody,rightArg,rightRedex,
      rightNode,rightVertex,_rightAt,rightIncidence,_rightPosition,rightChain⟩ :=
    marked_node_source_selected old selected rightTrace rightLookup sourceSafe rightMarked
  have leftEndpoint:=SyntaxIncidence.Source.unique leftIncidence leftSpec
  have rightEndpoint:=SyntaxIncidence.Source.unique rightIncidence rightSpec
  rw [←leftEndpoint,←rightEndpoint]
  refine ⟨[leftName++[.fn]],[rightName++[.fn]],leftChain,rightChain,?_⟩
  exact (redex_chain_iso_iff_degree closed leftRedex rightRedex).mpr
    ((selected leftName leftChosen).trans (selected rightName rightChosen).symm)
#print axioms marked_old_source_endpoint_iso
end Lamping.AG
