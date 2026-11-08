import Lamping.Lamping.BetaEvaluatedChildResiduals
import Lamping.Lamping.HistoryGeneratedCopyStep
import Lamping.Lamping.HistorySelectedPrincipalWord
import Lamping.Lambda.DirectedMarkerLeafWords
import Lamping.Lambda.LabelPermutation

namespace Lamping.Lambda.Labelled

private theorem paired_lookup {left right node : LTerm}
    (same : left.erase=right.erase) (lookup : left.subterm p=some node) :
    ∃ other,right.subterm p=some other ∧other.erase=node.erase := by
  have bare : subtermAt right.erase p=some node.erase := by
    rw [←same,←LTerm.erase_subterm,lookup];rfl
  rw [←LTerm.erase_subterm] at bare
  exact Option.map_eq_some_iff.mp bare

private theorem paired_history_erase
    (left : History ps source target) (right : History ps localSource localTarget)
    (same : source.erase=localSource.erase) : target.erase=localTarget.erase := by
  obtain ⟨candidate,lifted,erased⟩ := lift_history left.betaHistory localSource same.symm
  rw [lifted.deterministic right] at erased
  exact erased.symm

/-- Reannotation preserves the GIVEN origin constructor and all coordinates,
including copied q=[] overlaps; no new origin is arbitrarily selected. -/
theorem BetaIncomingReadingOrigin.reannotated
    (origin : BetaIncomingReadingOrigin body argument site edge reader oldReader first last)
    (bodySame : body.erase=localBody.erase) (argumentSame : argument.erase=localArgument.erase) :
    BetaIncomingReadingOrigin localBody localArgument site edge reader oldReader first last := by
  cases origin with
  | resultFunction result function => exact .resultFunction result function
  | resultLambda result reading oldLambda =>
    subst body
    cases localBody with
    | var stamp index => cases bodySame
    | app stamp fn arg => cases bodySame
    | lam stamp inner => exact .resultLambda result reading rfl
  | @copyFunction parent occurs copy reading =>
    have actual : ArgumentOccurrence localBody.erase (parent++[.fn]) := by rw [←bodySame];exact occurs
    exact .copyFunction actual copy reading
  | @copyLambda q stamp inner occurs copy reading oldLambda =>
    have actual : ArgumentOccurrence localBody.erase q := by rw [←bodySame];exact occurs
    subst argument
    cases localArgument with
    | var stamp index => cases argumentSame
    | app stamp fn arg => cases argumentSame
    | lam stamp inner => exact .copyLambda actual copy reading rfl

theorem PrerequisiteReadsDirected.reannotated
    (reading : PrerequisiteReadsDirected current reader edge forward)
    (same : current.erase=other.erase) : PrerequisiteReadsDirected other reader edge forward := by
  rcases reading.1 with app | lam
  · obtain ⟨stamp,fn,arg,atReader,edgeEq⟩ := app
    obtain ⟨node,lookup,erased⟩ := paired_lookup same atReader
    cases node with
    | var stamp index => cases erased
    | lam stamp body => cases erased
    | app stamp fn arg => exact ⟨Or.inl ⟨stamp,fn,arg,lookup,edgeEq⟩,reading.2⟩
  · obtain ⟨stamp,body,atReader,edgeEq⟩ := lam
    obtain ⟨node,lookup,erased⟩ := paired_lookup same atReader
    cases node with
    | var stamp index => cases erased
    | app stamp fn arg => cases erased
    | lam stamp body => exact ⟨Or.inr ⟨stamp,body,lookup,edgeEq⟩,reading.2⟩

/-- OUTPUT of an actual paired schedule, never a field of a history/net.
The global leaf remains fixed; local labels are not identified with it. -/
structure PairedMarkerEventGeometry
    (leaf : DirectedMarkerLeafOutput F source degree forward ps word)
    (localSource localTarget : LTerm) where
  middle : LTerm
  target : LTerm
  prefixLabels : History leaf.pre localSource middle
  turn : StepAt leaf.site middle target
  suffix : History leaf.after target localTarget
  middleErase : middle.erase=leaf.middle.erase
  targetErase : target.erase=leaf.target.erase
  beta : Label
  alpha : Label
  body : LTerm
  argument : LTerm
  redex : middle.subterm leaf.site=some (.app beta (.lam alpha body) argument)
  origin : BetaIncomingReadingOrigin body argument leaf.site leaf.edge leaf.reader leaf.oldReader leaf.first leaf.last
  current : LTerm
  lookup : target.subterm leaf.edge=some current
  reading : PrerequisiteReadsDirected target leaf.reader leaf.edge forward
  firstNode : LTerm
  lastNode : LTerm
  firstLookup : middle.subterm leaf.first=some firstNode
  lastLookup : middle.subterm leaf.last=some lastNode
  marker : Letter
  marks : marker.MarksDegree alpha
  formula : ExactDirectedReadingFormula middle leaf.site alpha forward firstNode lastNode marker current

/-- Cut the SAME supplied local schedule at the GIVEN global event. All
local event geometry and its exact overlap formula are conclusions. -/
theorem paired_marker_leaf_geometry
    (leaf : DirectedMarkerLeafOutput F source degree forward ps word)
    (localHistory : History ps localSource localTarget)
    (same : source.erase=localSource.erase) :
    Nonempty (PairedMarkerEventGeometry leaf localSource localTarget) := by
  rw [leaf.schedule] at localHistory
  obtain ⟨middle,prefixLabels,remaining⟩ := localHistory.split
  cases remaining with
  | cons turn suffix =>
    have midErase := paired_history_erase leaf.event.labels prefixLabels same
    have targetErase := paired_history_erase (.cons leaf.event.turn (.nil _)) (.cons turn (.nil _)) midErase
    obtain ⟨beta,alpha,body,argument,redex,_contractum⟩ := turn.head_lookups
    have heads := congrArg (fun t=>subtermAt t leaf.site) midErase
    simp only [←LTerm.erase_subterm,leaf.event.redex,redex,Option.map_some,LTerm.erase] at heads
    have components := Term.app.inj (Option.some.inj heads)
    have bodySame := Term.lam.inj components.1
    have origin := leaf.origin.reannotated bodySame components.2
    have reading := leaf.reading.reannotated targetErase
    obtain ⟨current,lookup,_erased⟩ := paired_lookup targetErase leaf.lookup
    obtain ⟨firstNode,lastNode,marker,firstLookup,lastLookup,marks,formula⟩ :=
      origin.directed_label_decomposition turn redex reading lookup
    exact ⟨⟨middle,_,prefixLabels,turn,suffix,midErase.symm,targetErase.symm,beta,alpha,body,argument,redex,
      origin,current,lookup,reading,firstNode,lastNode,firstLookup,lastLookup,marker,marks,formula⟩⟩
end Lamping.Lambda.Labelled

namespace Lamping.Lambda.Marked
private theorem relative_prefix_split (history : RelativeHistory (pre++after) source target) :
    ∃ middle,RelativeHistory pre source middle ∧RelativeHistory after middle target := by
  induction pre generalizing source with
  | nil => exact ⟨source,.nil _,history⟩
  | cons p pre ih =>
    cases history with
    | cons turn tail =>
      obtain ⟨middle,prefixLabels,suffix⟩ := ih tail
      exact ⟨middle,.cons turn prefixLabels,suffix⟩
end Lamping.Lambda.Marked

namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))

/-- Actual local event degree evaluates to THIS producer edge's principal.
Only physical geometry is locally initialized; global leaf/family untouched. -/
theorem PathSite.paired_marker_leaf_active_geometry
    {root : B} {marked : Marked}
    (leaf : DirectedMarkerLeafOutput F source degree forward ps word)
    (localHistory : History ps (initLabels source.erase) localTarget)
    (matching : Matches site.net root source.erase)
    (relative : Marked.RelativeHistory ps
      (Marked.mark (site.betaSyntaxFiber root source.erase) source.erase) marked)
    (edge : BetaEdge site.net) (geometry : SiteBetaGeometry site edge)
    (selection : SourceEdgeSelection (initLabels source.erase) site.net root) :
    ∃ paired : PairedMarkerEventGeometry leaf (initLabels source.erase) localTarget,
      selection.evalLabel edge paired.alpha=edge.principal := by
  obtain ⟨paired⟩ := paired_marker_leaf_geometry leaf localHistory (erase_initLabels source.erase).symm
  have schedule : ps=(leaf.pre++[leaf.site])++leaf.after := by
    exact leaf.schedule.trans (by simp only [List.append_assoc,List.singleton_append])
  rw [schedule] at relative
  obtain ⟨middle,prefixLabels,_suffix⟩ := Marked.relative_prefix_split relative
  have localRelative : Marked.RelativeHistory (leaf.pre++[leaf.site])
      (Marked.mark (site.betaSyntaxFiber root (initLabels source.erase).erase) (initLabels source.erase).erase) middle := by
    simpa only [erase_initLabels] using prefixLabels
  have degreeAt : paired.middle.degreeAt leaf.site=some paired.alpha := by
    simp only [LTerm.degreeAt,paired.redex,Option.bind_some,LTerm.degree]
  have selected := relative_last_selected_degree (init_is_INIT source.erase) localRelative paired.prefixLabels paired.turn degreeAt
  have localMatching : Matches site.net root (initLabels source.erase).erase := by
    simpa only [erase_initLabels] using matching
  have app : edge.app=.inr (.inl ()) := congrArg Sigma.fst (Sum.inl.inj geometry.appCtx)
  have lam : edge.lam=.inr (.inr ()) := congrArg Sigma.fst (Sum.inl.inj geometry.body)
  exact ⟨paired,site.selected_principal_word_at (init_is_INIT source.erase) localMatching selection edge app lam selected⟩
end
#print axioms BetaIncomingReadingOrigin.reannotated
#print axioms PrerequisiteReadsDirected.reannotated
#print axioms paired_marker_leaf_geometry
#print axioms PathSite.paired_marker_leaf_active_geometry
end Lamping.AG
