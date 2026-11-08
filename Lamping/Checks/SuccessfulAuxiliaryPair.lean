import Lamping.Checks.FanSuccessfulReachable
import Lamping.Lamping.SuccessfulEndpointIso
namespace Lamping.Checks.SuccessfulAuxiliaryPair
open AG Graph Lambda Lambda.Labelled FanSuccessfulChains

abbrev leftEdge : SyntaxIncidence.Edge current := ⟨leftBody,rfl⟩
abbrev rightEdge : SyntaxIncidence.Edge current := ⟨rightBody,rfl⟩
def leftLambda : SyntaxIncidence.Vertex current := some ⟨left,Or.inr ⟨_,_,rfl⟩⟩
def rightLambda : SyntaxIncidence.Vertex current := some ⟨right,Or.inr ⟨_,_,rfl⟩⟩
def leftApp : SyntaxIncidence.Vertex current := some ⟨leftBody,Or.inl ⟨_,_,_,rfl⟩⟩
def rightApp : SyntaxIncidence.Vertex current := some ⟨rightBody,Or.inl ⟨_,_,_,rfl⟩⟩

theorem left_source : SyntaxIncidence.source current leftEdge=leftLambda :=
  SyntaxIncidence.source_eq_of_spec current leftEdge
    ⟨.body,.lam leftLabel callerBody,.lamBody leftLabel,rfl,rfl,.body⟩
theorem right_source : SyntaxIncidence.source current rightEdge=rightLambda :=
  SyntaxIncidence.source_eq_of_spec current rightEdge
    ⟨.body,.lam rightLabel callerBody,.lamBody rightLabel,rfl,rfl,.body⟩
theorem left_target : SyntaxIncidence.target current targetClosed leftEdge=leftApp :=
  SyntaxIncidence.target_eq_of_spec current targetClosed leftEdge (Or.inl rfl)
theorem right_target : SyntaxIncidence.target current targetClosed rightEdge=rightApp :=
  SyntaxIncidence.target_eq_of_spec current targetClosed rightEdge (Or.inl rfl)

theorem left_aux : AuxiliaryAt current leftBody := by
  constructor
  · rintro ⟨p,stamp,fn,arg,split,_lookup⟩
    have same:=congrArg List.getLast? split
    simp [leftBody,left] at same
  · rintro ⟨stamp,body,lookup⟩
    cases lookup

theorem right_aux : AuxiliaryAt current rightBody := by
  constructor
  · rintro ⟨p,stamp,fn,arg,split,_lookup⟩
    have same:=congrArg List.getLast? split
    simp [rightBody,right] at same
  · rintro ⟨stamp,body,lookup⟩
    cases lookup

theorem equal_label : SyntaxIncidence.label current leftEdge=SyntaxIncidence.label current rightEdge := rfl

theorem four_successful_endpoints :
    EndpointChain current (SyntaxIncidence.source current leftEdge) leftEdges ∧
    EndpointChain current (SyntaxIncidence.source current rightEdge) rightEdges ∧
    EndpointChain current (SyntaxIncidence.target current targetClosed leftEdge) leftBodyEdges ∧
    EndpointChain current (SyntaxIncidence.target current targetClosed rightEdge) rightBodyEdges := by
  rw [left_source,right_source,left_target,right_target]
  exact ⟨left_lambda_chain,right_lambda_chain,left_body_chain,right_body_chain⟩

theorem source_chains_not_isomorphic :
    ¬ChainIncidenceIsomorphic (chainSyntaxIncidence current targetClosed leftEdges)
      (chainSyntaxIncidence current targetClosed rightEdges) := by
  rintro ⟨iso⟩
  let selected : (chainSyntaxIncidence current targetClosed leftEdges).Edge :=
    ⟨⟨left,rfl⟩,by simp [leftEdges]⟩
  let image := iso.edges selected
  have member : image.val.val∈rightEdges := image.property
  have labels := iso.label_eq selected
  change SyntaxIncidence.label current ⟨left,rfl⟩=SyntaxIncidence.label current image.val at labels
  simp only [rightEdges,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with same | same | same | same
  · have edgeEq : image.val=⟨right,rfl⟩ := Subtype.ext same
    have impossible : ¬ SyntaxIncidence.label current ⟨left,rfl⟩=SyntaxIncidence.label current ⟨right,rfl⟩ := by decide
    exact impossible (labels.trans (congrArg (SyntaxIncidence.label current) edgeEq))
  · have edgeEq : image.val=⟨[.fn,.body,.fn],rfl⟩ := Subtype.ext same
    have impossible : ¬ SyntaxIncidence.label current ⟨left,rfl⟩=SyntaxIncidence.label current ⟨[.fn,.body,.fn],rfl⟩ := by decide
    exact impossible (labels.trans (congrArg (SyntaxIncidence.label current) edgeEq))
  · have edgeEq : image.val=⟨xVar,rfl⟩ := Subtype.ext same
    have impossible : ¬ SyntaxIncidence.label current ⟨left,rfl⟩=SyntaxIncidence.label current ⟨xVar,rfl⟩ := by decide
    exact impossible (labels.trans (congrArg (SyntaxIncidence.label current) edgeEq))
  · have edgeEq : image.val=⟨[.fn],rfl⟩ := Subtype.ext same
    have impossible : ¬ SyntaxIncidence.label current ⟨left,rfl⟩=SyntaxIncidence.label current ⟨[.fn],rfl⟩ := by decide
    exact impossible (labels.trans (congrArg (SyntaxIncidence.label current) edgeEq))
#print axioms four_successful_endpoints
#print axioms source_chains_not_isomorphic

theorem source_endpoints_not_successfully_isomorphic :
    ¬SuccessfulEndpointIso current targetClosed
      (SyntaxIncidence.source current leftEdge) (SyntaxIncidence.source current rightEdge) := by
  rw [left_source,right_source]
  rintro ⟨es,fs,first,second,iso⟩
  have l:=EndpointChain.unique first (show EndpointChain current leftLambda leftEdges from left_lambda_chain)
  have r:=EndpointChain.unique second (show EndpointChain current rightLambda rightEdges from right_lambda_chain)
  subst es;subst fs
  exact source_chains_not_isomorphic iso

theorem target_chains_not_isomorphic :
    ¬ChainIncidenceIsomorphic (chainSyntaxIncidence current targetClosed leftBodyEdges)
      (chainSyntaxIncidence current targetClosed rightBodyEdges) := by
  rintro ⟨iso⟩
  let selected : (chainSyntaxIncidence current targetClosed leftBodyEdges).Edge :=
    ⟨⟨left,rfl⟩,by simp [leftBodyEdges,leftEdges]⟩
  let image := iso.edges selected
  have member : image.val.val∈rightBodyEdges := image.property
  have labels := iso.label_eq selected
  change SyntaxIncidence.label current ⟨left,rfl⟩=SyntaxIncidence.label current image.val at labels
  simp only [rightBodyEdges,rightEdges,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with same | same | same | same | same
  · have edgeEq : image.val=⟨rightVar,rfl⟩ := Subtype.ext same
    have impossible : ¬ SyntaxIncidence.label current ⟨left,rfl⟩=SyntaxIncidence.label current ⟨rightVar,rfl⟩ := by decide
    exact impossible (labels.trans (congrArg (SyntaxIncidence.label current) edgeEq))
  · have edgeEq : image.val=⟨right,rfl⟩ := Subtype.ext same
    have impossible : ¬ SyntaxIncidence.label current ⟨left,rfl⟩=SyntaxIncidence.label current ⟨right,rfl⟩ := by decide
    exact impossible (labels.trans (congrArg (SyntaxIncidence.label current) edgeEq))
  · have edgeEq : image.val=⟨[.fn,.body,.fn],rfl⟩ := Subtype.ext same
    have impossible : ¬ SyntaxIncidence.label current ⟨left,rfl⟩=SyntaxIncidence.label current ⟨[.fn,.body,.fn],rfl⟩ := by decide
    exact impossible (labels.trans (congrArg (SyntaxIncidence.label current) edgeEq))
  · have edgeEq : image.val=⟨xVar,rfl⟩ := Subtype.ext same
    have impossible : ¬ SyntaxIncidence.label current ⟨left,rfl⟩=SyntaxIncidence.label current ⟨xVar,rfl⟩ := by decide
    exact impossible (labels.trans (congrArg (SyntaxIncidence.label current) edgeEq))
  · have edgeEq : image.val=⟨[.fn],rfl⟩ := Subtype.ext same
    have impossible : ¬ SyntaxIncidence.label current ⟨left,rfl⟩=SyntaxIncidence.label current ⟨[.fn],rfl⟩ := by decide
    exact impossible (labels.trans (congrArg (SyntaxIncidence.label current) edgeEq))

theorem target_endpoints_not_successfully_isomorphic :
    ¬SuccessfulEndpointIso current targetClosed
      (SyntaxIncidence.target current targetClosed leftEdge)
      (SyntaxIncidence.target current targetClosed rightEdge) := by
  rw [left_target,right_target]
  rintro ⟨es,fs,first,second,iso⟩
  have l:=EndpointChain.unique first (show EndpointChain current leftApp leftBodyEdges from left_body_chain)
  have r:=EndpointChain.unique second (show EndpointChain current rightApp rightBodyEdges from right_body_chain)
  subst es;subst fs
  exact target_chains_not_isomorphic iso

/-- A non-normal successful-domain pair with real four-endpoint availability.
No physical fragment inequality or whole AuxiliarySeparation is claimed. -/
theorem actual_successful_auxiliary_pair :
    INIT original ∧Closed original.erase ∧History [[.fn]] original current ∧
    GraphTrace (ActualNet.initial FanSuccessfulReachable.term)
      (ActualNet.ofNet FanSuccessfulReachable.fanCro.site.reduce)
      [.beta 0,.fanAction .lam 0 1 (by decide),.fanAction .cro 0 1 (by decide)] ∧
    Matches FanSuccessfulReachable.fanCro.site.net (.inl ()) current.erase ∧
    Matches FanSuccessfulReachable.fanCro.site.reduce (.inl ()) current.erase ∧
    AuxiliaryAt current leftBody ∧AuxiliaryAt current rightBody ∧
    SyntaxIncidence.label current leftEdge=SyntaxIncidence.label current rightEdge ∧
    EndpointChain current (SyntaxIncidence.source current leftEdge) leftEdges ∧
    EndpointChain current (SyntaxIncidence.source current rightEdge) rightEdges ∧
    EndpointChain current (SyntaxIncidence.target current targetClosed leftEdge) leftBodyEdges ∧
    EndpointChain current (SyntaxIncidence.target current targetClosed rightEdge) rightBodyEdges ∧
    ¬SuccessfulEndpointIso current targetClosed
      (SyntaxIncidence.source current leftEdge) (SyntaxIncidence.source current rightEdge) ∧
    ¬SuccessfulEndpointIso current targetClosed
      (SyntaxIncidence.target current targetClosed leftEdge)
      (SyntaxIncidence.target current targetClosed rightEdge) := by
  obtain ⟨ls,rs,lt,rt⟩:=four_successful_endpoints
  exact ⟨initial,sourceClosed,actualHistory,FanSuccessfulReachable.actual_three_step_trace,
    FanSuccessfulReachable.actual_source_matches,FanSuccessfulReachable.actual_final_matches,
    left_aux,right_aux,equal_label,ls,rs,lt,rt,source_endpoints_not_successfully_isomorphic,
    target_endpoints_not_successfully_isomorphic⟩
#print axioms source_endpoints_not_successfully_isomorphic
#print axioms target_endpoints_not_successfully_isomorphic
#print axioms actual_successful_auxiliary_pair
end Lamping.Checks.SuccessfulAuxiliaryPair
