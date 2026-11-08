import Lamping.Lamping.EndpointPrerequisites
import Lamping.Lambda.BetaIncidencePreimages
import Lamping.Lambda.BetaChainExistenceReflection
namespace Lamping.Lambda.Labelled
/-- A created incoming root's actual old edge is BODY or ARG. This is only
an occurrence classification, not a source-endpoint homomorphism. -/
theorem created_old_edge_root
    (origin : BetaNodePreimage body argument site p oldEdge)
    (created : BetaCreatedIncoming body site p) :
    oldEdge=site++[.fn,.body] ∨oldEdge=site++[.arg] := by
  rcases origin.coordinates with ⟨same,outside⟩ |
      ⟨relative,node,currentEq,oldEq,lookup,nonselected⟩ |
      ⟨q,relative,node,occurs,currentEq,oldEq,lookup⟩
  · rcases betaCreatedIncoming_iff.mp created with result |⟨chosen,selected,copy⟩
    · exact False.elim (outside ⟨[],by simpa using result⟩)
    · exact False.elim (outside ⟨chosen,copy⟩)
  · rcases betaCreatedIncoming_iff.mp created with result |⟨chosen,selected,copy⟩
    · have empty : relative=[] := by
        have sizes := congrArg List.length (currentEq.symm.trans result)
        simp only [List.length_append] at sizes
        exact List.length_eq_zero_iff.mp (by omega)
      exact Or.inl (by simpa [empty] using oldEq)
    · have equal : relative=chosen := List.append_cancel_left (currentEq.symm.trans copy)
      subst chosen
      change subtermAt body.erase relative=some (.var (binderDepth relative)) at selected
      rw [←LTerm.erase_subterm,lookup,Option.map_some] at selected
      cases node with
      | var stamp index =>
        have same : index=binderDepth relative := Term.var.inj (Option.some.inj selected)
        exact False.elim (nonselected stamp (by rw [same]))
      | lam => cases selected
      | app => cases selected
  · rcases betaCreatedIncoming_iff.mp created with result |⟨chosen,selected,copy⟩
    · have empty : relative=[] := by
        have sizes := congrArg List.length (currentEq.symm.trans result)
        simp only [List.length_append] at sizes
        exact List.length_eq_zero_iff.mp (by omega)
      exact Or.inr (by simpa [empty] using oldEq)
    · have word : q++relative=chosen++[] := by
        apply List.append_cancel_left (as:=site)
        simpa only [List.append_assoc,List.append_nil] using currentEq.symm.trans copy
      have empty := (contract_argument_origin_unique occurs selected word).2
      exact Or.inr (by simpa [empty] using oldEq)
end Lamping.Lambda.Labelled

namespace Lamping.AG
open Lambda Lambda.Labelled
open SyntaxIncidence
/-- Reflect a GIVEN successful endpoint chain through THIS actual vertex
preimage. External none remains impossible, never a successful empty chain. -/
theorem endpoint_available_at_beta_preimage
    {source target body argument : LTerm} {site : Path} {beta alpha : Label}
    {vertex : Vertex target} {oldVertex : Vertex source} {edges : List Path}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (origin : BetaVertexPreimage body argument site source target vertex oldVertex)
    (chain : EndpointChain target vertex edges) :
    ∃oldEdges,EndpointChain source oldVertex oldEdges := by
  cases origin with
  | boundary => exact False.elim chain
  | proper origin => exact step.chain_reflect_at_preimage redex origin chain

/-- Backward availability at BOTH endpoints of THIS old edge. In the
created source cases the old chain is the actual selected singleton, not an
ancestor-chain source homomorphism. No isomorphism or label equality follows. -/
theorem old_edge_endpoint_availability
    {source target body argument current : LTerm} {site edge oldEdge : Path} {beta alpha : Label}
    {fromVertex toVertex : Vertex target} {sourceEdges targetEdges : List Path}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (origin : BetaNodePreimage body argument site edge oldEdge)
    (lookup : target.subterm edge=some current)
    (fromSpec : Source target edge fromVertex) (toSpec : Target target edge toVertex)
    (fromChain : EndpointChain target fromVertex sourceEdges)
    (toChain : EndpointChain target toVertex targetEdges) :
    ∃oldFrom oldTo oldSourceEdges oldTargetEdges,
      Source source oldEdge oldFrom ∧Target source oldEdge oldTo ∧
      EndpointChain source oldFrom oldSourceEdges ∧EndpointChain source oldTo oldTargetEdges := by
  obtain ⟨oldTo,oldToSpec,toOrigin⟩ := step.beta_incidence_target_preimage redex origin toSpec
  obtain ⟨oldTargetEdges,oldToChain⟩ := endpoint_available_at_beta_preimage step redex toOrigin toChain
  by_cases created : BetaCreatedIncoming body site edge
  · rcases created_old_edge_root origin created with retained |copied
    · let parent : ProperPosition source := ⟨site++[.fn],Or.inr ⟨alpha,body,by rw [LTerm.subterm_append,redex];rfl⟩⟩
      refine ⟨some parent,oldTo,[site++[.fn]],oldTargetEdges,?_,oldToSpec,?_,oldToChain⟩
      · exact ⟨.body,.lam alpha body,.lamBody alpha,by change oldEdge=(site++[Step.fn])++[Step.body];simpa only [List.append_assoc] using retained,
          by rw [LTerm.subterm_append,redex];rfl,.body⟩
      · exact PrerequisiteChain.redex_lam redex
    · let parent : ProperPosition source := ⟨site,Or.inl ⟨beta,.lam alpha body,argument,redex⟩⟩
      refine ⟨some parent,oldTo,[site++[Step.fn]],oldTargetEdges,?_,oldToSpec,?_,oldToChain⟩
      · exact ⟨.arg,.app beta (.lam alpha body) argument,.appArg beta,copied,redex,.arg⟩
      · change PrerequisiteChain source site [site++[Step.fn]]
        exact PrerequisiteChain.redex_app redex

  · obtain ⟨oldFrom,oldFromSpec,fromOrigin⟩ := step.beta_incidence_source_preimage redex origin lookup created fromSpec
    obtain ⟨oldSourceEdges,oldFromChain⟩ := endpoint_available_at_beta_preimage step redex fromOrigin fromChain
    exact ⟨oldFrom,oldTo,oldSourceEdges,oldTargetEdges,oldFromSpec,oldToSpec,oldFromChain,oldToChain⟩
#print axioms endpoint_available_at_beta_preimage
#print axioms old_edge_endpoint_availability
end Lamping.AG
