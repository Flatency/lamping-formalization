import Lamping.Checks.FanBodyDoubleLambdaParents
set_option maxHeartbeats 4000000
namespace Lamping.Checks.FanBodySequentialCutsConsumer
open AG Graph Lambda Lambda.Labelled FanBodyDoubleLambdaReachable FanBodyDoubleLambdaParents
abbrev bodyPosition : Path := [.fn,.body]
abbrev bodyEnvironment := [FanBodyContextConsumer.functionTerm.label]
abbrev bodyTerm := FanBodyContextConsumer.functionBody
abbrev bodyContext := SourcePort.lamBody FanBodyContextConsumer.functionTerm.label
abbrev bodyEdge := sourceEdge bodyEnvironment bodyContext bodyTerm
noncomputable abbrev sourceNet := innerFan.site.net
noncomputable abbrev targetNet := innerFan.site.reduce
noncomputable abbrev actualCut : Net signature innerFan.Kept (Boundary term⊕(Bool⊕Bool)) innerFan.Outside :=
  cutFragment innerFan.site.net (pathPartition (Schema.fanAction .lam 0 1 (by decide)) innerFan.Inside) innerFan.site.closed
abbrev actualRight := fanRight Op.lam 0 1

def role : SourceDeparture FanBodyContextConsumer.functionTerm .body bodyEdge.fromPort := .body
/-- The second fan action has a kept lambda BODY parent and copied lambda
context terminal. Both endpoint cases are supplied by the actual fixture. -/
theorem actual_inner_body_cut (principal : SiteActionPrincipal innerFan.site)
    (source : SourceEdgeFragment current sourceNet (.inl ()) bodyEdge bodyPosition)
    (target : SourceEdgeFragment current targetNet (.inl ()) bodyEdge bodyPosition) :
    ∃ (branch : Bool) (a b : Context) (pivot : Endpoint actualCut)
      (rawPiece : List (PlugSegment actualCut actualRight)) (oldPiece : List (Endpoint sourceNet)) (seam : Context),
      Labelling targetNet target.access.val a b ∧
      source.segments=oldPiece++principal.edges ∧
      target.segments.map (plugEnd (actualCut).label (actualRight).label).invFun=
        rawPiece++[.inr (.inr (.inl (.inl branch)))] ∧
      ActionCanonicalBlocks innerFan.site principal (Sum.inl pivot::rawPiece)
        (innerFan.site.outsideEnd pivot::oldPiece) ∧
      PlugLabelling actualCut actualRight (Sum.inl pivot::rawPiece) seam b := by
  obtain ⟨parent,⟨parentNode,parentPort⟩,parentWord,parentFinish⟩ := final_parent_kept principal
  obtain ⟨child,branch,childWord,childFinish⟩ := final_child_copied principal
  have sameAccess : target.access=child := actual_final_matches.accessWord_injective
    (target.word.trans childWord.symm)
  have endAt : target.access.val.getLast?=some
      (targetNet.wire (.inl ⟨.inr (.inl branch),.inl ()⟩)) := by rw [sameAccess];exact childFinish
  obtain ⟨a,b,wholeLabels⟩ := target.access.property.1.1
  obtain ⟨flow,_,_,_,_⟩ := outer_certified
  obtain ⟨pivot,rawPiece,oldPiece,seam,_sourceParentEnd,_targetParentEnd,sourcePiece,targetPiece,relation,labels⟩ :=
    source.fan_kept_parent_copied_context_cut innerFan.site (innerFan.sourceIso.flowBalance flow)
      (.inl ()) rfl actual_inner_source_matches actual_final_matches principal target role
      innerSourceParent parent (by rw [innerSourceWord];rfl) (by rw [parentWord];rfl)
      parentNode parentPort parentFinish branch endAt wholeLabels
  exact ⟨branch,a,b,pivot,rawPiece,oldPiece,seam,wholeLabels,sourcePiece,targetPiece,relation,labels⟩

/-- Genuine same original INIT/history, all three graph rules and the real
successful BODY-lambda chain accompany arbitrary two fragment choices. -/
theorem actual_inner_body_supply :
    INIT original ∧Closed original.erase ∧History [[]] original current ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet targetNet)
      [.beta 0,.fanAction .lam 0 1 (by decide),.fanAction .lam 0 1 (by decide)] ∧
    Matches sourceNet (.inl ()) current.erase ∧Matches targetNet (.inl ()) current.erase ∧
    Nonempty (SourceEdgeFragment current sourceNet (.inl ()) bodyEdge bodyPosition) ∧
    Nonempty (SourceEdgeFragment current targetNet (.inl ()) bodyEdge bodyPosition) ∧
    PrerequisiteChain current bodyPosition [bodyPosition,[.fn]] ∧
    ∃principal : SiteActionPrincipal innerFan.site,
      ∀ (source : SourceEdgeFragment current sourceNet (.inl ()) bodyEdge bodyPosition)
        (target : SourceEdgeFragment current targetNet (.inl ()) bodyEdge bodyPosition),
        ∃branch a b pivot rawPiece oldPiece seam,
          Labelling targetNet target.access.val a b ∧
          source.segments=oldPiece++principal.edges ∧
          target.segments.map (plugEnd (actualCut).label (actualRight).label).invFun=
            rawPiece++[.inr (.inr (.inl (.inl branch)))] ∧
          ActionCanonicalBlocks innerFan.site principal (Sum.inl pivot::rawPiece)
            (innerFan.site.outsideEnd pivot::oldPiece) ∧
          PlugLabelling actualCut actualRight (Sum.inl pivot::rawPiece) seam b := by
  refine ⟨FanBodyContextConsumer.initial,FanBodyContextConsumer.closed,FanBodyContextConsumer.actualHistory,
    actual_three_step_trace,actual_inner_source_matches,actual_final_matches,
    actual_inner_source_matches.base_source_edge_fragment FanBodyContextConsumer.targetClosed FanBodyContextConsumer.leftOccurrence,
    actual_final_matches.base_source_edge_fragment FanBodyContextConsumer.targetClosed FanBodyContextConsumer.leftOccurrence,
    FanBodyContextConsumer.leftChain,?_⟩
  obtain ⟨principal⟩ := innerFan.site.actionPrincipal_exists
  exact ⟨principal,actual_inner_body_cut principal⟩
#print axioms actual_inner_body_cut
#print axioms actual_inner_body_supply
end Lamping.Checks.FanBodySequentialCutsConsumer
