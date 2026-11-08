import Lamping.Lamping.RecentSpineFarOrigins
import Lamping.Checks.CanonicalAfterFarComparison
import Lamping.Checks.ForwardExpandedFarOrigins
namespace Lamping.Checks.RecentSpineFarOriginsChecks
open Graph Lambda Lambda.Labelled AG SyntaxIncidence

private theorem empty_node_coordinates
    {a b : LTerm} {xs : List Path} {labels : History xs a b}
    (trace : BetaNodeHistoryPreimage labels p q) (empty : xs=[]) : p=q := by
  subst xs
  cases trace
  rfl

private theorem empty_trace_chain
    {a b : LTerm} {xs : List Path} {labels : History xs a b}
    (trace : BetaNodeHistoryPreimage labels p q) (empty : xs=[])
    (chain : PrerequisiteChain b p edges) : PrerequisiteChain a q edges := by
  subst xs
  cases trace
  exact chain

private theorem node_cast
    {a b c : LTerm} {xs ys : List Path}
    (schedule : xs=ys) (sourceEq : a=b)
    {labels : History xs a c} {other : History ys b c}
    (trace : BetaNodeHistoryPreimage other p q) : BetaNodeHistoryPreimage labels p q := by
  subst ys
  subst b
  exact trace

private theorem origin_subtree
    (origin : BetaIncomingReadingOrigin body argument site edge reader oldReader first last) :
    ∃relative,edge=site++relative := by
  cases origin with
  | resultFunction result _ => exact ⟨[],by simpa using result⟩
  | resultLambda result _ _ => exact ⟨[],by simpa using result⟩
  | copyFunction _ copy _ => exact ⟨_,copy⟩
  | copyLambda _ copy _ _ => exact ⟨_,copy⟩

private theorem one_schedule {pre suffix : List Path} {site only : Path}
    (schedule : [only]=(pre++[site])++suffix) : pre=[] ∧site=only ∧suffix=[] := by
  have size:=congrArg List.length schedule
  simp only [List.length_append,List.length_cons,List.length_nil] at size
  have preEmpty : pre=[]:=List.length_eq_zero_iff.mp (by omega)
  have suffixEmpty : suffix=[]:=List.length_eq_zero_iff.mp (by omega)
  rw [preEmpty,suffixEmpty] at schedule
  exact ⟨preEmpty,by simpa using (List.cons.inj schedule).1.symm,suffixEmpty⟩

private theorem two_schedule {pre suffix : List Path} {site s1 s2 : Path}
    (schedule : [s1,s2]=(pre++[site])++suffix) :
    (pre=[] ∧site=s1 ∧suffix=[s2]) ∨(pre=[s1] ∧site=s2 ∧suffix=[]) := by
  have size:=congrArg List.length schedule
  simp only [List.length_append,List.length_cons,List.length_nil] at size
  cases preEq : pre with
  | nil =>
    rw [preEq,List.nil_append,List.singleton_append] at schedule
    have parts:=List.cons.inj schedule
    exact Or.inl ⟨rfl,parts.1.symm,parts.2.symm⟩
  | cons first rest =>
    have count : rest.length=0 ∧suffix.length=0 := by
      rw [preEq] at size
      simp only [List.length_cons] at size
      omega
    have restEq:=List.length_eq_zero_iff.mp count.1
    have suffixEq:=List.length_eq_zero_iff.mp count.2
    rw [preEq,restEq,suffixEq] at schedule
    have parts:=List.cons.inj schedule
    have next:=List.cons.inj parts.2
    exact Or.inr ⟨by rw [restEq,←parts.1],next.1.symm,suffixEq⟩

private theorem current_far_context
    {a b : LTerm} {labels : History ps a b}
    {cut : ActualUnsafeMarkerCut F ps a b degree start edges}
    {leaf snapshot} {geometry : SpineIncidenceProvenance F a degree cut.forward cut.spine cut.lookup leaf snapshot}
    {canonical : CanonicalAfterFarOutput labels cut snapshot}
    {recent : RecentSpineFrame geometry}
    (compat : RecentFarCompatibility canonical recent)
    (suffixNil : recent.suffixSites=[])
    (currentEq : canonical.currentProper.val=position)
    (outside : ¬∃relative,position=recent.packet.site++relative) :
    compat.expandedProper.val=position := by
  obtain ⟨suffixPosition,node,lookup,suffixTrace⟩:=recent.suffixHistory.node_preimage_from_lookup canonical.currentLookup
  have suffixEq : suffixPosition=position := (empty_node_coordinates suffixTrace suffixNil).symm.trans currentEq
  have origin : BetaNodePreimage recent.packet.event.body recent.packet.event.argument recent.packet.site suffixPosition position :=
    Eq.mp (congrArg (fun p : Path=>BetaNodePreimage recent.packet.event.body recent.packet.event.argument recent.packet.site p position) suffixEq.symm)
      (BetaNodePreimage.context outside)
  have known : BetaNodeHistoryPreimage (.cons recent.packet.event.turn recent.suffixHistory)
      canonical.currentProper.val position := .one (step:=recent.packet.event.turn) recent.packet.event.redex origin suffixTrace
  have actual : BetaNodeHistoryPreimage (.cons recent.packet.event.turn recent.suffixHistory)
      canonical.currentProper.val compat.expandedProper.val := by
    cases compat.farHistory with
    | proper trace => exact trace
  exact actual.unique known

private theorem uncreated_cast
    {a b c : LTerm} {xs ys : List Path}
    (schedule : xs=ys) (sourceEq : a=b)
    {labels : History xs a c} {other : History ys b c}
    (trace : UncreatedNodeHistoryPreimage labels p q) : UncreatedNodeHistoryPreimage other p q := by
  subst ys
  subst b
  exact trace

private theorem singleton_uncreated_not_created
    {a b body argument : LTerm} {site edge oldEdge : Path} {beta alpha : Label}
    {labels : History [site] a b}
    (trace : UncreatedNodeHistoryPreimage labels edge oldEdge)
    (redex : a.subterm site=some (.app beta (.lam alpha body) argument))
    (created : BetaCreatedIncoming body site edge) : False := by
  cases trace with
  | one actualRedex _ uncreated tail =>
    cases tail
    have shape:=Option.some.inj (redex.symm.trans actualRedex)
    injection shape with _ fnEq _
    injection fnEq with _ bodyEq
    rw [←bodyEq] at uncreated
    exact uncreated created

private theorem recent_latest_created_second
    {a b c body argument : LTerm} {F : List Path} {degree beta : Label} {s1 s2 edge : Path}
    {spine : DirectedMarkerSpine F a degree forward [s1,s2] c before edge}
    {lookup : c.subterm edge=some node} {leaf snapshot}
    {geometry : SpineIncidenceProvenance F a degree forward spine lookup leaf snapshot}
    (recent : RecentSpineFrame geometry)
    (firstStep : StepAt s1 a b) (secondStep : StepAt s2 b c)
    (redex : b.subterm s2=some (.app beta (.lam degree body) argument))
    (created : BetaCreatedIncoming body s2 edge) :
    recent.packet.pre=[s1] ∧recent.packet.site=s2 ∧recent.suffixSites=[] := by
  rcases two_schedule recent.schedule with earlier | latest
  · obtain ⟨preEq,siteEq,suffixEq⟩:=earlier
    have noPrefix : History [] a recent.packet.middle :=
      Eq.mp (congrArg (fun xs : List Path => History xs a recent.packet.middle) preEq) recent.packet.event.labels
    have middleEq:=noPrefix.deterministic (.nil a)
    have actualTurn : StepAt s1 a recent.packet.target :=
      Eq.mp (congrArg (fun pair : Path×LTerm => StepAt pair.1 pair.2 recent.packet.target)
        (show (recent.packet.site,recent.packet.middle)=(s1,a) from Prod.ext siteEq middleEq)) recent.packet.event.turn
    have targetEq := (History.cons actualTurn (.nil _)).deterministic (.cons firstStep (.nil _))
    have actualUncreated : UncreatedNodeHistoryPreimage (.cons secondStep (.nil _)) edge recent.packet.edge :=
      uncreated_cast suffixEq targetEq recent.uncreatedSuffix
    exact False.elim (singleton_uncreated_not_created actualUncreated redex created)
  · exact latest

namespace EmptyCopy
open UniformOldCreatedIncomingLabelsChecks.Distinct
open ActualSpineAfterAlignmentChecks.EmptyCopy

def rightCopyTrace : BetaNodeHistoryPreimage (.cons secondStep (.nil target)) right oldRight :=
  .one (step:=secondStep) (by rfl) (by simpa only [List.append_nil] using
      (BetaNodePreimage.copied (body:=.var (.atom 8) 0) (argument:=oldArgument) (site:=right) (q:=[]) (relative:=[]) (old:=oldArgument) rfl rfl)) (.nil _ _)

private theorem packet_latest
    {leaf snapshot} {g : SpineIncidenceProvenance F source (.atom 7) false cut.spine cut.lookup leaf snapshot}
    (recent : RecentSpineFrame g) :
    recent.packet.pre=[left] ∧recent.packet.site=right ∧recent.suffixSites=[] := by
  rcases two_schedule recent.schedule with earlier | latest
  · obtain ⟨preEq,siteEq,suffixEq⟩:=earlier
    have noPrefix : History [] source recent.packet.middle :=
      Eq.mp (congrArg (fun xs : List Path => History xs source recent.packet.middle) preEq) recent.packet.event.labels
    have middleEq:=noPrefix.deterministic (.nil source)
    have actualTurn : StepAt left source recent.packet.target :=
      Eq.mp (congrArg (fun pair : Path×LTerm => StepAt pair.1 pair.2 recent.packet.target)
        (show (recent.packet.site,recent.packet.middle)=(left,UniformOldCreatedIncomingLabelsChecks.Distinct.source) from Prod.ext siteEq middleEq)) recent.packet.event.turn
    have targetEq := (History.cons actualTurn (.nil _)).deterministic (.cons firstStep (.nil _))
    have known : BetaNodeHistoryPreimage recent.suffixHistory right oldRight := node_cast suffixEq targetEq rightCopyTrace
    have edgeEq : recent.packet.edge=oldRight := recent.uncreatedSuffix.to_node.unique known
    obtain ⟨relative,inside⟩:=origin_subtree recent.packet.origin
    have impossible : oldRight=left++relative := edgeEq.symm.trans (inside.trans (congrArg (fun p : Path=>p++relative) siteEq))
    cases impossible
  · exact latest

private theorem canonical_coordinates
    {snapshot : IncomingIncidenceSnapshot target cut.edge}
    (far : snapshot.far false=some currentParent)
    (canonical : CanonicalAfterFarOutput labels cut snapshot) :
    canonical.currentProper.val=[.arg] ∧canonical.sourceProper.val=[.arg] ∧canonical.sourceEdges=[[.arg],[.fn]] := by
  have currentEq:=congrArg Subtype.val (Option.some.inj (canonical.farEq.symm.trans far))
  have own : BetaNodeHistoryPreimage labels [.arg] canonical.sourceProper.val :=
    Eq.mp (congrArg (fun p : Path=>BetaNodeHistoryPreimage labels p canonical.sourceProper.val) currentEq) canonical.nodeTrace
  have sourceEq:=own.unique CanonicalAfterFarComparisonChecks.EmptyCopy.ownParentTrace
  have actualChain : PrerequisiteChain source [.arg] canonical.sourceEdges :=
    Eq.mp (congrArg (fun p : Path=>PrerequisiteChain source p canonical.sourceEdges) sourceEq) canonical.sourceChain
  exact ⟨currentEq,sourceEq,actualChain.unique originalChain⟩

/-- The NEW compatibility output is for the actual latest q=[] frame after
an older left event, not the selected BODY-variable triple endpoint. -/
theorem actual_latest_q0_source_chain : ∃leaf snapshot,
    ∃g : SpineIncidenceProvenance F source (.atom 7) false cut.spine cut.lookup leaf snapshot,
      ∃canonical : CanonicalAfterFarOutput labels cut snapshot,
        ∃recent : RecentSpineFrame g,∃compat : RecentFarCompatibility canonical recent,
          recent.packet.pre=[left] ∧recent.packet.site=right ∧recent.suffixSites=[] ∧
          canonical.currentProper.val=[.arg] ∧compat.expandedProper.val=[.arg] ∧
          recent.packet.middle=middle ∧compat.middleEdges=[[.arg],[.fn]] ∧compat.sourcePosition=[.arg] ∧
          compat.originalEdges=[[.arg],[.fn]] ∧canonical.sourceEdges=[[.arg],[.fn]] ∧
          BetaVertexHistoryPreimage recent.packet.event.labels (some compat.expandedProper) (some canonical.sourceProper) := by
  obtain ⟨leaf,snapshot,g,_,_,_,far⟩:=actual_cut_alignment
  obtain ⟨canonical,recent,⟨compat⟩⟩:=cut.recent_far_compatibility labels sourceClosed (by decide) g
  obtain ⟨pre,site,suffix⟩:=packet_latest recent
  obtain ⟨cur,old,edges⟩:=canonical_coordinates far canonical
  have expanded := current_far_context compat suffix cur (by
    rintro ⟨rest,eq⟩
    have equal : [.arg]=right++rest := eq.trans (congrArg (fun p : Path=>p++rest) site)
    have size:=congrArg List.length equal
    simp [right] at size)
  have prefixHistory : History [left] source recent.packet.middle :=
    Eq.mp (congrArg (fun xs : List Path=>History xs source recent.packet.middle) pre) recent.packet.event.labels
  have middleEq:=prefixHistory.deterministic (.cons firstStep (.nil _))
  have actualMiddle : PrerequisiteChain middle [.arg] compat.middleEdges := by
    have rebased : PrerequisiteChain middle compat.expandedProper.val compat.middleEdges :=
      Eq.mp (congrArg (fun t : LTerm=>PrerequisiteChain t compat.expandedProper.val compat.middleEdges) middleEq) compat.middleChain
    exact Eq.mp (congrArg (fun p : Path=>PrerequisiteChain middle p compat.middleEdges) expanded) rebased
  have middleList:=actualMiddle.unique middleChain
  exact ⟨leaf,snapshot,g,canonical,recent,compat,pre,site,suffix,cur,expanded,middleEq,middleList,compat.sourceCoordinate.trans old,
    compat.exactSourceEdges.trans edges,edges,compat.prefixVertexTrace⟩

end EmptyCopy
namespace ForwardOverlap
open ForwardExpandedFarOriginsChecks.Overlap
abbrev node : LTerm:=LTerm.contract (.atom 4) (.atom 5) body argument
abbrev selected := ForwardFarChainComparisonChecks.Overlap.selected
abbrev sourceSafe := ForwardFarChainComparisonChecks.Overlap.sourceSafe

theorem marked : ¬node.label.OuterBarsSafe (fun x=>x≠Label.atom 5) :=
  event.turn.created_label_not_safe event.redex (by rfl : target.subterm [.fn]=some node) (Or.inl rfl)

def spine : DirectedMarkerSpine F source (.atom 5) true [[.fn]] target [] [.fn] :=
  event.final_old.directed_marker_spine event.final_history selected sourceSafe .refl reading rfl marked (by intro e h;cases h)
def cut : ActualUnsafeMarkerCut F [[.fn]] source target (.atom 5) [] [[.fn],[.fn,.fn]] where
  before:=[]
  edge:=[.fn]
  after:=[[.fn,.fn]]
  reader:=[]
  node:=node
  forward:=true
  split:=rfl
  segment:=.refl
  remaining:=remaining
  reading:=reading
  lookup:=rfl
  safeBefore:=by intro e h;cases h
  marked:=marked
  spine:=spine
  leaf:=spine.leaf_output rfl

def currentProper : ProperPosition target:=⟨[.fn],Or.inl ⟨_,_,_,rfl⟩⟩
def ownTrace : BetaNodeHistoryPreimage event.final_history [.fn] [.fn,.arg] :=
  .one (step:=event.turn) event.redex knownNodeOrigin (.nil _ _)

theorem actual_true_var0_arg_far : ∃leaf snapshot,
    ∃g : SpineIncidenceProvenance F source (.atom 5) true cut.spine cut.lookup leaf snapshot,
      ∃canonical : CanonicalAfterFarOutput event.final_history cut snapshot,
        ∃recent : RecentSpineFrame g,∃compat : RecentFarCompatibility canonical recent,
          recent.packet.pre=[] ∧recent.packet.site=[.fn] ∧recent.suffixSites=[] ∧
          recent.packet.middle=ForwardExpandedFarOriginsChecks.Overlap.source ∧canonical.currentProper.val=[.fn] ∧
          compat.expandedProper.val=[.fn,.arg] ∧compat.sourcePosition=[.fn,.arg] ∧
          compat.middleEdges=[[.fn,.arg,.fn]] ∧compat.originalEdges=[[.fn,.arg,.fn]] ∧
          canonical.sourceEdges=[[.fn,.arg,.fn]] ∧sourceSelected.val≠compat.expandedProper.val := by
  obtain ⟨leaf,snapshot,⟨g⟩⟩:=spine.incidence_leaf_output sourceClosed cut.lookup
  obtain ⟨canonical,recent,⟨compat⟩⟩:=cut.recent_far_compatibility event.final_history sourceClosed (by decide) g
  obtain ⟨pre,site,suffix⟩:=one_schedule recent.schedule
  have far : snapshot.far true=some currentProper := Target.unique snapshot.toSpec (Or.inl rfl)
  have currentEq:=congrArg Subtype.val (Option.some.inj (canonical.farEq.symm.trans far))
  have own : BetaNodeHistoryPreimage event.final_history [.fn] canonical.sourceProper.val :=
    Eq.mp (congrArg (fun p : Path=>BetaNodeHistoryPreimage event.final_history p canonical.sourceProper.val) currentEq) canonical.nodeTrace
  have sourceEq:=own.unique ownTrace
  have sourcePos:=compat.sourceCoordinate.trans sourceEq
  have expanded:compat.expandedProper.val=[.fn,.arg] := (empty_node_coordinates compat.prefixNodeTrace pre).trans sourcePos
  have actualSource : PrerequisiteChain source [.fn,.arg] canonical.sourceEdges :=
    Eq.mp (congrArg (fun p : Path=>PrerequisiteChain source p canonical.sourceEdges) sourceEq) canonical.sourceChain
  have edges:=actualSource.unique sourceTail
  have middleAtSource:=empty_trace_chain compat.prefixNodeTrace pre compat.middleChain
  have middleAtArg : PrerequisiteChain source [.fn,.arg] compat.middleEdges :=
    Eq.mp (congrArg (fun p : Path=>PrerequisiteChain source p compat.middleEdges) sourcePos) middleAtSource
  have middleList:=middleAtArg.unique sourceTail
  have noPrefix : History [] source recent.packet.middle :=
    Eq.mp (congrArg (fun xs : List Path=>History xs source recent.packet.middle) pre) recent.packet.event.labels
  have middleEq:=noPrefix.deterministic (.nil _)
  exact ⟨leaf,snapshot,g,canonical,recent,compat,pre,site,suffix,middleEq,currentEq,expanded,sourcePos,middleList,
    compat.exactSourceEdges.trans edges,edges,by rw [expanded];decide⟩

theorem actual_same_init_prior_and_triple : INIT original ∧History [[],[.fn]] original target ∧¬INIT source ∧
    Target source [.fn,.fn,.body] (some sourceSelected) ∧sourceSelected.val≠sourceArgument.val :=
  ⟨initial,prefixHistory.append event.final_history,sourceNotInit,triple_LAST_targets_another_vertex⟩
end ForwardOverlap
namespace Inherited
open PairedCurrentChainSourceLabelsChecks.NoninitialDistinct
open ActualSpineAfterAlignmentChecks.Inherited

def ownFarTrace : BetaNodeHistoryPreimage labels [.fn] [.fn,.fn,.body] :=
  .one (step:=firstStep) (by rfl)
    (by simpa only [List.append_nil] using
      (BetaNodePreimage.retained (body:=body) (argument:=argument) (site:=[.fn]) (relative:=[]) (old:=body)
        (by rfl) (by intro stamp eq;cases eq)))
    (.one (step:=secondStep) (by rfl) (.context (by rintro ⟨rest,eq⟩;cases eq)) (.nil _ _))

def originalBodyChain : PrerequisiteChain source [.fn,.fn,.body] [[.fn,.fn,.body,.fn]] := .redex_app rfl

private theorem latest_first_with_inherited_suffix
    {leaf snapshot} {g : SpineIncidenceProvenance F source (.atom 6) false cut.spine cut.lookup leaf snapshot}
    (recent : RecentSpineFrame g) :
    recent.packet.pre=[] ∧recent.packet.site=[.fn] ∧recent.suffixSites=[[.arg]] := by
  rcases two_schedule recent.schedule with first | last
  · exact first
  · obtain ⟨_pre,site,suffix⟩:=last
    have edgeEq : recent.packet.edge=leftStart := (empty_node_coordinates recent.uncreatedSuffix.to_node suffix).symm
    obtain ⟨relative,inside⟩:=origin_subtree recent.packet.origin
    have impossible : leftStart=[.arg]++relative := edgeEq.symm.trans (inside.trans (congrArg (fun p : Path=>p++relative) site))
    cases impossible

/-- A real later ARG step is an inherited suffix, not a marker word. The
most recent creation stays at FN; its expanded FAR is the old BODY APP,
not the selected FIRST-far APP or earliest triple endpoint. -/
theorem actual_inherited_suffix_body_app : ∃leaf snapshot,
    ∃g : SpineIncidenceProvenance F source (.atom 6) false cut.spine cut.lookup leaf snapshot,
      ∃canonical : CanonicalAfterFarOutput labels cut snapshot,
        ∃recent : RecentSpineFrame g,∃compat : RecentFarCompatibility canonical recent,
          recent.packet.pre=[] ∧recent.packet.site=[.fn] ∧recent.suffixSites=[[.arg]] ∧
          canonical.currentProper.val=[.fn] ∧compat.expandedProper.val=[.fn,.fn,.body] ∧
          compat.sourcePosition=[.fn,.fn,.body] ∧compat.middleEdges=[[.fn,.fn,.body,.fn]] ∧
          compat.originalEdges=[[.fn,.fn,.body,.fn]] ∧canonical.sourceEdges=[[.fn,.fn,.body,.fn]] ∧
          recent.suffixSites≠[] := by
  obtain ⟨leaf,snapshot,⟨g⟩⟩:=cut.spine.incidence_leaf_output sourceClosed cut.lookup
  obtain ⟨canonical,recent,⟨compat⟩⟩:=cut.recent_far_compatibility labels sourceClosed (by decide) g
  obtain ⟨pre,site,suffix⟩:=latest_first_with_inherited_suffix recent
  have actualSource : Source current leftStart (some currentParent) := ⟨.arg,_,_,rfl,rfl,.arg⟩
  have far : snapshot.far false=some currentParent := Source.unique snapshot.fromSpec actualSource
  have currentEq:=congrArg Subtype.val (Option.some.inj (canonical.farEq.symm.trans far))
  have own : BetaNodeHistoryPreimage labels [.fn] canonical.sourceProper.val :=
    Eq.mp (congrArg (fun p : Path=>BetaNodeHistoryPreimage labels p canonical.sourceProper.val) currentEq) canonical.nodeTrace
  have sourceEq:=own.unique ownFarTrace
  have sourcePos:=compat.sourceCoordinate.trans sourceEq
  have expanded:compat.expandedProper.val=[.fn,.fn,.body] := (empty_node_coordinates compat.prefixNodeTrace pre).trans sourcePos
  have actualChain : PrerequisiteChain source [.fn,.fn,.body] canonical.sourceEdges :=
    Eq.mp (congrArg (fun p : Path=>PrerequisiteChain source p canonical.sourceEdges) sourceEq) canonical.sourceChain
  have edges:=actualChain.unique originalBodyChain
  have middleAtSource:=empty_trace_chain compat.prefixNodeTrace pre compat.middleChain
  have middleAtBody : PrerequisiteChain source [.fn,.fn,.body] compat.middleEdges :=
    Eq.mp (congrArg (fun p : Path=>PrerequisiteChain source p compat.middleEdges) sourcePos) middleAtSource
  have middleList:=middleAtBody.unique originalBodyChain
  exact ⟨leaf,snapshot,g,canonical,recent,compat,pre,site,suffix,currentEq,expanded,sourcePos,middleList,
    compat.exactSourceEdges.trans edges,edges,by rw [suffix];decide⟩

theorem actual_selected_singleton_different_from_body :
    PrerequisiteChain source [.fn] [[.fn,.fn]] ∧
    PrerequisiteChain source [.fn,.fn,.body] [[.fn,.fn,.body,.fn]] ∧
    ([.fn] : Path)≠[.fn,.fn,.body] ∧
    ([[.fn,.fn]] : List Path)≠[[.fn,.fn,.body,.fn]] :=
  ⟨.redex_app rfl,originalBodyChain,by decide,by decide⟩
end Inherited
namespace MarkedLowOnly
open DirectedMarkerSpineIncidenceChecks.Nested

theorem forward_stops_at_recent_marked : ∃leaf snapshot,
    ∃g : SpineIncidenceProvenance family sourceWrapped (.atom 10) true forwardSpine
      (by rfl : targetForward.subterm [.fn]=some UniformOldNodeLabelSuffixChecks.target) leaf snapshot,
      ∃recent : RecentSpineFrame g,
        recent.packet.pre=[[.fn]] ∧recent.packet.site=[.fn] ∧recent.suffixSites=[] ∧leaf.continuation≠[] := by
  obtain ⟨leaf,snapshot,⟨g⟩,continuation⟩:=forward_nonempty
  obtain ⟨recent⟩:=g.recent_frame
  have latest:=recent_latest_created_second recent forwardFirst forwardLast (by rfl) (Or.inl rfl)
  exact ⟨leaf,snapshot,g,recent,latest.1,latest.2.1,latest.2.2,continuation⟩

theorem reverse_stops_at_recent_marked : ∃leaf snapshot,
    ∃g : SpineIncidenceProvenance family sourceWrapped (.atom 10) false reverseSpine
      (by rfl : targetReverse.subterm [.fn]=some reverseResult) leaf snapshot,
      ∃recent : RecentSpineFrame g,
        recent.packet.pre=[[.fn,.arg]] ∧recent.packet.site=[.fn] ∧recent.suffixSites=[] ∧leaf.continuation≠[] := by
  obtain ⟨leaf,snapshot,⟨g⟩,continuation⟩:=reverse_nonempty
  obtain ⟨recent⟩:=g.recent_frame
  have latest:=recent_latest_created_second recent reverseFirst reverseLast (by rfl) (Or.inl rfl)
  exact ⟨leaf,snapshot,g,recent,latest.1,latest.2.1,latest.2.2,continuation⟩
end MarkedLowOnly

#print axioms SpineIncidenceProvenance.recent_frame
#print axioms Lamping.AG.RecentSpineFrame.canonical_far_compatibility
#print axioms ActualUnsafeMarkerCut.recent_far_compatibility
#print axioms EmptyCopy.actual_latest_q0_source_chain
#print axioms ForwardOverlap.actual_true_var0_arg_far
#print axioms ForwardOverlap.actual_same_init_prior_and_triple
#print axioms Inherited.ownFarTrace
#print axioms Inherited.actual_inherited_suffix_body_app
#print axioms Inherited.actual_selected_singleton_different_from_body
#print axioms MarkedLowOnly.forward_stops_at_recent_marked
#print axioms MarkedLowOnly.reverse_stops_at_recent_marked
end Lamping.Checks.RecentSpineFarOriginsChecks



