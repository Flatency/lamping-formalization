import Lamping.Lamping.FanCopiedBodyKeptCuts
import Lamping.Checks.FanBodyDoubleLambdaParents
namespace Lamping.Checks.FanBodyOuterCutConsumer
open AG Graph Lambda Lambda.Labelled FanBodyDoubleLambdaReachable FanBodyDoubleLambdaParents
abbrev bodyPosition : Path := [.fn,.body]
abbrev bodyEdge := sourceEdge [FanBodyContextConsumer.functionTerm.label]
  (.lamBody FanBodyContextConsumer.functionTerm.label) FanBodyContextConsumer.functionBody
noncomputable abbrev sourceNet := outerFan.site.net
noncomputable abbrev targetNet := outerFan.site.reduce
noncomputable abbrev actualCut : Net signature outerFan.Kept (Boundary term⊕(Bool⊕Bool)) outerFan.Outside := cut2
abbrev actualRight := fanRight Op.lam 0 1
def role : SourceDeparture FanBodyContextConsumer.functionTerm .body bodyEdge.fromPort := .body
theorem source_matches : Matches sourceNet (.inl ()) current.erase := outerFan.sourceIso.matches beta_matches
theorem target_matches : Matches targetNet (.inl ()) current.erase := by
  obtain ⟨_,_,_,_,matching⟩ := outer_certified;exact matching
/-- Genuine outer fan action: copied lambda BODY parent, kept inner lambda
terminal. The actual entire fragment is the normalized contiguous OLD path. -/
theorem actual_outer_body_cut (principal : SiteActionPrincipal outerFan.site)
    (source : SourceEdgeFragment current sourceNet (.inl ()) bodyEdge bodyPosition)
    (target : SourceEdgeFragment current targetNet (.inl ()) bodyEdge bodyPosition) :
    ∃ (a b : Context) (tail : List (PlugSegment actualCut actualRight))
      (oldTail : List (Endpoint sourceNet)) (seam : Context),
      Labelling targetNet target.access.val a b ∧
      source.segments=.inl ⟨.inr (.inr ()),.inr true⟩::oldTail ∧
      target.segments.map (plugEnd (actualCut).label (actualRight).label).invFun=
        .inr (.inl ⟨.inl false,.inr true⟩):: .inr (.inl ⟨.inr true,.inl ()⟩)::
          .inl (.inr (.inl (.inr (.inr true))))::tail ∧
      ActionCanonicalBlocks outerFan.site principal
        (.inl (.inr (.inl (.inr (.inr true))))::tail) source.segments ∧
      PlugLabelling actualCut actualRight (.inl (.inr (.inl (.inr (.inr true))))::tail) seam b := by
  obtain ⟨parent,parentWord,_observation⟩ := Matches.observation _ source_matches
    (show Position current.erase from ⟨[.fn],rfl⟩)
  have sameAccess : target.access=bodyChild := target_matches.accessWord_injective
    (target.word.trans bodyWord.symm)
  have finish : target.access.val.getLast?=some (targetNet.wire (.inl ⟨.inl innerKept2,.inl ()⟩)) := by
    rw [sameAccess];exact bodyFinish
  obtain ⟨a,b,labels⟩ := target.access.property.1.1
  obtain ⟨flow,_,_,_,_⟩ := beta_certified
  obtain ⟨tail,oldTail,seam,sourcePiece,shape,relation,pieceLabels⟩ := source.fan_copied_body_kept_cut
    outerFan.site (outerFan.sourceIso.flowBalance flow) (.inl ()) rfl source_matches target_matches principal
    target role parent lambdaParent (by rw [parentWord];rfl) (by change bodyPosition=accessWord outerNet lambdaEdges++[.body];rw [lambdaWord];rfl)
    false lambdaFinish innerKept2 (.inl ()) finish labels
  exact ⟨a,b,tail,oldTail,seam,labels,sourcePiece,shape,relation,pieceLabels⟩
theorem actual_outer_body_supply :
    INIT original ∧Closed original.erase ∧History [[]] original current ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet targetNet)
      [.beta 0,.fanAction .lam 0 1 (by decide)] ∧
    Matches sourceNet (.inl ()) current.erase ∧Matches targetNet (.inl ()) current.erase ∧
    Nonempty (SourceEdgeFragment current sourceNet (.inl ()) bodyEdge bodyPosition) ∧
    Nonempty (SourceEdgeFragment current targetNet (.inl ()) bodyEdge bodyPosition) ∧
    PrerequisiteChain current bodyPosition [bodyPosition,[.fn]] ∧
    ∃principal : SiteActionPrincipal outerFan.site,
      ∀ (source : SourceEdgeFragment current sourceNet (.inl ()) bodyEdge bodyPosition)
        (target : SourceEdgeFragment current targetNet (.inl ()) bodyEdge bodyPosition),
        ∃a b tail oldTail seam,
          Labelling targetNet target.access.val a b ∧
          source.segments=.inl ⟨.inr (.inr ()),.inr true⟩::oldTail ∧
          target.segments.map (plugEnd (actualCut).label (actualRight).label).invFun=
            .inr (.inl ⟨.inl false,.inr true⟩):: .inr (.inl ⟨.inr true,.inl ()⟩)::
              .inl (.inr (.inl (.inr (.inr true))))::tail ∧
          ActionCanonicalBlocks outerFan.site principal
            (.inl (.inr (.inl (.inr (.inr true))))::tail) source.segments ∧
          PlugLabelling actualCut actualRight (.inl (.inr (.inl (.inr (.inr true))))::tail) seam b := by
  refine ⟨FanBodyContextConsumer.initial,FanBodyContextConsumer.closed,FanBodyContextConsumer.actualHistory,
    .cons concrete.graph_step (.cons outerFan.graph_step (.refl _)),source_matches,target_matches,
    source_matches.base_source_edge_fragment FanBodyContextConsumer.targetClosed FanBodyContextConsumer.leftOccurrence,
    target_matches.base_source_edge_fragment FanBodyContextConsumer.targetClosed FanBodyContextConsumer.leftOccurrence,
    FanBodyContextConsumer.leftChain,?_⟩
  obtain ⟨principal⟩ := outerFan.site.actionPrincipal_exists
  exact ⟨principal,actual_outer_body_cut principal⟩
#print axioms actual_outer_body_cut
#print axioms actual_outer_body_supply
end Lamping.Checks.FanBodyOuterCutConsumer
