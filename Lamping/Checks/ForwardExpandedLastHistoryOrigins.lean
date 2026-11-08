import Lamping.Lamping.ForwardExpandedLastHistoryOrigins
import Lamping.Checks.CrossPrefixExpandedArgumentConsumer
import Lamping.Lamping.ForwardFarChainComparison
set_option maxHeartbeats 4000000
namespace Lamping.Checks.ForwardExpandedLastHistoryOriginsChecks
open Graph Lambda Lambda.Labelled AG SyntaxIncidence

private theorem one_schedule (schedule : [step]=(pre++[site])++suffix) :
    pre=[] ∧site=step ∧suffix=[] := by
  have lengths:=congrArg List.length schedule
  simp only [List.length_append,List.length_cons,List.length_nil] at lengths
  have pe : pre=[] := List.length_eq_zero_iff.mp (by omega)
  have se : suffix=[] := List.length_eq_zero_iff.mp (by omega)
  rw [pe,se] at schedule
  simp only [List.nil_append,List.append_nil,List.singleton_inj] at schedule
  exact ⟨pe,schedule.symm,se⟩

private theorem empty_coordinates {source target : LTerm} {ps : List Path} {edge oldEdge : Path}
    {labels : History ps source target} (trace : BetaNodeHistoryPreimage labels edge oldEdge)
    (empty : ps=[]) : edge=oldEdge := by
  subst ps
  cases labels
  cases trace
  rfl

namespace OrdinaryResult
abbrev I : Term := .lam (.var 0)
abbrev source : LTerm:=initLabels (.app (.app (.lam (.app (.var 0) I)) (.app I I)) I)
abbrev body : LTerm:=.app (.atom 3) (.var (.atom 4) 0) (.lam (.atom 5) (.var (.atom 6) 0))
abbrev argument : LTerm:=.app (.atom 7) (.lam (.atom 8) (.var (.atom 9) 0))
  (.lam (.atom 10) (.var (.atom 11) 0))
abbrev current : LTerm:=LTerm.contract (.atom 1) (.atom 2) body argument
abbrev target : LTerm:=.app (.atom 0) current (.lam (.atom 12) (.var (.atom 13) 0))
abbrev F : List Path:=[[.fn]]
abbrev markedBody : Marked:=.app [] (.var 0) (.lam (.var 0))
abbrev markedArgument : Marked:=.app [[.fn,.arg]] (.lam (.var 0)) (.lam (.var 0))

def event : SelectedOldTurn F source (.atom 2) [] source target [.fn] where
  markedBefore:=Marked.mark F source.erase
  markedAfter:=.app [] (Marked.contract markedBody markedArgument) (.lam (.var 0))
  beforeOld:=.nil _
  reduction:=by
    change Marked.ReductionAt [.fn] (.app [] (.red [[.fn]] markedBody markedArgument) (.lam (.var 0)))
      (.app [] (Marked.contract markedBody markedArgument) (.lam (.var 0)))
    exact .appL (.redRoot _ _ _)
  member:=by decide
  labels:=.nil _
  turn:=.fn (.root _ _ _ _)
  beta:=.atom 1
  body:=body
  argument:=argument
  redex:=rfl

theorem sourceClosed : Closed source.erase := by
  simp [Closed,Scoped,source,initLabels,initFrom,nodeCount,LTerm.erase]
theorem sourceSafe : source.OuterBarsSafe (fun x=>x≠Label.atom 2) := (init_is_INIT _).outerBarsSafe _
theorem selected (name : Path) (member : name∈F) : source.degreeAt name=some (.atom 2) := by
  have same:=List.mem_singleton.mp member
  subst name
  rfl
theorem currentLookup : target.subterm [.fn]=some current := rfl
theorem currentMarked : ¬current.label.OuterBarsSafe (fun x=>x≠Label.atom 2) := by
  intro safe
  change (Label.atom 2≠Label.atom 2) ∧True at safe
  exact safe.1 rfl

abbrev edges : List Path:=[[.fn],[.fn,.fn],[.fn,.fn,.fn]]
def remaining : PrerequisiteChain target [] edges :=
  .app rfl (by intro a b impossible;cases impossible)
    (.app rfl (by intro a b impossible;cases impossible)
      (.redex_app (p:=[.fn,.fn]) rfl))
def reading : PrerequisiteReadsDirected target [] [.fn] true:=⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩
def spine : DirectedMarkerSpine F source (.atom 2) true [[.fn]] target [] [.fn] :=
  event.final_old.directed_marker_spine event.final_history selected sourceSafe
    .refl reading currentLookup currentMarked (by simp)
def cut : ActualUnsafeMarkerCut F [[.fn]] source target (.atom 2) [] edges where
  before:=[]
  edge:=[.fn]
  after:=[[.fn,.fn],[.fn,.fn,.fn]]
  reader:=[]
  node:=current
  forward:=true
  split:=rfl
  segment:=.refl
  remaining:=remaining
  reading:=reading
  lookup:=currentLookup
  safeBefore:=by simp
  marked:=currentMarked
  spine:=spine
  leaf:=spine.leaf_output currentLookup

def retainedWholeTrace : BetaNodeHistoryPreimage event.final_history [.fn] [.fn,.fn,.body] := by
  apply BetaNodeHistoryPreimage.one (step:=event.turn) event.redex
  · simpa only [List.append_nil] using
      (BetaNodePreimage.retained (body:=body) (argument:=argument) (site:=[.fn])
        (relative:=[]) (old:=body) rfl (by intro stamp impossible;cases impossible))
  · exact .nil _ _

/-- Genuine ordinary RESULT/nonvar0, with two later READs and actual
GIVEN geometry. The expanded ancestor is BODY, not the overlap's ARG. -/
theorem actual_ordinary_result_ancestor_auxiliary : ∃leaf snapshot,
    ∃g : SpineIncidenceProvenance F source (.atom 2) true cut.spine cut.lookup leaf snapshot,
    ∃canonical : CanonicalAfterFarOutput event.final_history cut snapshot,
    ∃recent : RecentSpineFrame g,∃compat : RecentFarCompatibility canonical recent,
    ∃low : ExpandedLastSelectedEndpoint recent.packet.middle recent.packet.site
      (recent.packet.frame.edges.getLastD []) true (some compat.expandedProper),
    ∃out : ExpandedLastOriginalEndpoints F source recent.packet.middle (.atom 2) recent.packet.event.labels
      (recent.packet.frame.edges.getLastD []) low.node true canonical.sourceProper compat.originalEdges,
      BetaNodeHistoryPreimage event.final_history cut.edge out.oldEdge ∧
      out.oldEdge=[.fn,.fn,.body] ∧
      recent.packet.frame.edges.getLastD []=[.fn,.fn,.body] ∧
      AuxiliaryAt source out.oldEdge ∧out.oldEdge≠[.fn,.arg] := by
  obtain ⟨leaf,snapshot,⟨g⟩⟩:=cut.spine.incidence_leaf_output sourceClosed cut.lookup
  obtain ⟨canonical,recent,⟨compat⟩⟩:=cut.recent_far_compatibility event.final_history sourceClosed (by decide) g
  obtain ⟨pre,_site,_suffix⟩:=one_schedule recent.schedule
  obtain ⟨low,⟨out⟩⟩:=compat.expanded_last_endpoints selected sourceSafe
  have trace:=recent.forward_expanded_last_history_preimage event.final_history out
  have original : out.oldEdge=[.fn,.fn,.body]:=trace.unique retainedWholeTrace
  have last : recent.packet.frame.edges.getLastD []=[.fn,.fn,.body]:=
    (empty_coordinates out.nodeTrace pre).trans original
  have auxiliary:=cut.forward_original_last_auxiliary rfl (by decide) recent out
  exact ⟨leaf,snapshot,g,canonical,recent,compat,low,out,trace,original,last,auxiliary,by rw [original];decide⟩
end OrdinaryResult

#print axioms OrdinaryResult.event
#print axioms OrdinaryResult.retainedWholeTrace
#print axioms OrdinaryResult.actual_ordinary_result_ancestor_auxiliary
namespace CrossPrefix
open SingleUnsafeCopyFunctionAppInputsChecks
open ExpandedArgumentHistoryOriginsChecks.CrossPrefix

/-- The new all-TRUE kernel directly consumes the actual distinct-prefix
ARG pair and both originalAux outputs; no old SOURCE iso is used as input. -/
theorem actual_cross_prefix_all_true_comparison :
    ∃earlyLeaf earlySnapshot,
    ∃eg : SpineIncidenceProvenance F source (.atom 6) true earlyCut.spine earlyCut.lookup earlyLeaf earlySnapshot,
    ∃ec : CanonicalAfterFarOutput event.final_history earlyCut earlySnapshot,
    ∃er : RecentSpineFrame eg,∃ex : RecentFarCompatibility ec er,
    ∃earlyLow : ExpandedLastSelectedEndpoint er.packet.middle er.packet.site
      (er.packet.frame.edges.getLastD []) true (some ex.expandedProper),
    ∃eo : ExpandedLastOriginalEndpoints F source er.packet.middle (.atom 6) er.packet.event.labels
      (er.packet.frame.edges.getLastD []) earlyLow.node true ec.sourceProper ex.originalEdges,
    ∃lateLeaf lateSnapshot,
    ∃lg : SpineIncidenceProvenance F source (.atom 6) true lateCut.spine lateCut.lookup lateLeaf lateSnapshot,
    ∃lc : CanonicalAfterFarOutput event.final_history lateCut lateSnapshot,
    ∃lr : RecentSpineFrame lg,∃lx : RecentFarCompatibility lc lr,
    ∃lateLow : ExpandedLastSelectedEndpoint lr.packet.middle lr.packet.site
      (lr.packet.frame.edges.getLastD []) true (some lx.expandedProper),
    ∃lo : ExpandedLastOriginalEndpoints F source lr.packet.middle (.atom 6) lr.packet.event.labels
      (lr.packet.frame.edges.getLastD []) lateLow.node true lc.sourceProper lx.originalEdges,
      er.packet.pre=[] ∧er.packet.site=[.fn] ∧er.suffixSites=[[.arg]] ∧
      lr.packet.pre=[[.fn]] ∧lr.packet.site=[.arg] ∧lr.suffixSites=[] ∧
      er.packet.frame.edges.getLastD []=[.fn,.arg] ∧lr.packet.frame.edges.getLastD []=[.arg,.arg] ∧
      eo.oldEdge=[.fn,.arg] ∧lo.oldEdge=[.arg,.arg] ∧eo.oldEdge≠lo.oldEdge ∧
      eo.original.label=lo.original.label ∧
      SuccessfulEndpointIso source sourceClosed (some eo.fromVertex) (some lo.fromVertex) ∧
      AuxiliaryAt source eo.oldEdge ∧AuxiliaryAt source lo.oldEdge := by
  obtain ⟨el,es,eg,ec,er,ex,elow,eo,ll,ls,lg,lc,lr,lx,llow,lo,
    ep,et,ef,lp,lt,lf,ee,le,_eorig,_lorig,different,_oldLabel,_oldIso⟩:=
      CrossPrefixExpandedArgumentConsumer.actual_cross_prefix_source_comparison
  have pair:=recent_forward_expanded_last_source_comparison er lr event.final_history eo lo
    event.final_old selected sourceSafe sourceClosed copiedMarked copiedMarked rfl
  have earlyAux:=earlyCut.forward_original_last_auxiliary rfl (by decide) er eo
  have lateAux:=lateCut.forward_original_last_auxiliary rfl (by decide) lr lo
  have earlyTrace:=er.forward_expanded_last_history_preimage event.final_history eo
  have lateTrace:=lr.forward_expanded_last_history_preimage event.final_history lo
  have eorigNew:=earlyTrace.unique CrossPrefixExpandedArgumentConsumer.earlyWholeTrace
  have lorigNew:=lateTrace.unique CrossPrefixExpandedArgumentConsumer.lateWholeTrace
  exact ⟨el,es,eg,ec,er,ex,elow,eo,ll,ls,lg,lc,lr,lx,llow,lo,
    ep,et,ef,lp,lt,lf,ee,le,eorigNew,lorigNew,different,pair.1,pair.2,earlyAux,lateAux⟩
end CrossPrefix

#print axioms CrossPrefix.actual_cross_prefix_all_true_comparison
end Lamping.Checks.ForwardExpandedLastHistoryOriginsChecks
