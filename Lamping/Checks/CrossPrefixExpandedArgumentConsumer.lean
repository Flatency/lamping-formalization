import Lamping.Checks.ExpandedArgumentHistoryOrigins
namespace Lamping.Checks.CrossPrefixExpandedArgumentConsumer
open Graph Lambda Lambda.Labelled AG SyntaxIncidence

private theorem two_schedule {pre suffix : List Path} {site : Path}
    (schedule : [[.fn],[.arg]]=(pre++[site])++suffix) :
    (pre=[] ∧site=[.fn] ∧suffix=[[.arg]]) ∨
    (pre=[[.fn]] ∧site=[.arg] ∧suffix=[]) := by
  have sizes:=congrArg List.length schedule
  simp only [List.length_append,List.length_cons,List.length_nil] at sizes
  cases pre with
  | nil =>
    simp only [List.nil_append,List.singleton_append,List.cons.injEq] at schedule
    exact Or.inl ⟨rfl,schedule.1.symm,schedule.2.symm⟩
  | cons head tail =>
    simp only [List.length_cons] at sizes
    have te : tail=[]:=List.length_eq_zero_iff.mp (by omega)
    have se : suffix=[]:=List.length_eq_zero_iff.mp (by omega)
    subst tail
    rw [se] at schedule
    simp only [List.cons_append,List.nil_append,List.append_nil,List.cons.injEq] at schedule
    exact Or.inr ⟨congrArg (fun p : Path=>[p]) schedule.1.symm,schedule.2.1.symm,se⟩

private theorem origin_below
    (origin : BetaIncomingReadingOrigin body argument site edge reader oldReader first last) :
    ∃relative,edge=site++relative := by
  cases origin with
  | resultFunction eq _ => exact ⟨[],by simpa only [List.append_nil] using eq⟩
  | resultLambda eq _ _ => exact ⟨[],by simpa only [List.append_nil] using eq⟩
  | copyFunction _ eq _ => exact ⟨_,eq⟩
  | copyLambda _ eq _ _ => exact ⟨_,eq⟩

private theorem empty_coordinates {source target : LTerm} {ps : List Path}
    {labels : History ps source target}
    (trace : BetaNodeHistoryPreimage labels p old) (empty : ps=[]) : p=old := by
  subst ps
  cases trace
  rfl

private theorem one_context_coordinates {source target : LTerm} {ps : List Path}
    {labels : History ps source target}
    (trace : BetaNodeHistoryPreimage labels p old) (single : ps=[site])
    (outside : ¬∃relative,p=site++relative) : p=old := by
  subst ps
  cases trace with
  | one redex origin tail =>
    cases tail
    exact (origin.unique (.context outside)).symm

private theorem one_uncreated {source target body argument : LTerm} {ps : List Path}
    {labels : History ps source target}
    (trace : UncreatedNodeHistoryPreimage labels p old) (single : ps=[site])
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument)) :
    ¬BetaCreatedIncoming body site p := by
  subst ps
  cases trace with
  | one actual origin uncreated tail =>
    cases tail
    have same:=Option.some.inj (actual.symm.trans redex)
    cases same
    exact uncreated

open SingleUnsafeCopyFunctionAppInputsChecks
open ExpandedArgumentHistoryOriginsChecks.CrossPrefix

private theorem early_recent_signature
    {leaf snapshot}
    {g : SpineIncidenceProvenance F source (.atom 6) true earlyCut.spine earlyCut.lookup leaf snapshot}
    (recent : RecentSpineFrame g) :
    recent.packet.pre=[] ∧recent.packet.site=[.fn] ∧recent.suffixSites=[[.arg]] := by
  rcases two_schedule recent.schedule with good |late
  · exact good
  · obtain ⟨pre,site,suffix⟩:=late
    have head:=empty_coordinates recent.uncreatedSuffix.to_node suffix
    obtain ⟨relative,inside⟩:=origin_below recent.packet.origin
    rw [←head,site] at inside
    change [.fn,.fn,.fn]=[.arg]++relative at inside
    cases inside

private theorem late_recent_signature
    {leaf snapshot}
    {g : SpineIncidenceProvenance F source (.atom 6) true lateCut.spine lateCut.lookup leaf snapshot}
    (recent : RecentSpineFrame g) :
    recent.packet.pre=[[.fn]] ∧recent.packet.site=[.arg] ∧recent.suffixSites=[] := by
  rcases two_schedule recent.schedule with early |good
  · obtain ⟨pre,site,suffix⟩:=early
    have history : History [[.fn]] source recent.packet.target := by
      have actual:=recent.packet.event.final_history
      exact Eq.mp (congrArg (fun sites : List Path=>History sites source recent.packet.target)
        (show recent.packet.pre++[recent.packet.site]=[[.fn]] from by rw [pre,site];rfl)) actual
    have targetEq:=history.deterministic preHistory
    have redex : recent.packet.target.subterm [.arg]=some (.app event.beta (.lam (.atom 6) body) argument) := by
      rw [targetEq]
      exact event.redex
    have noCreated:=one_uncreated recent.uncreatedSuffix suffix redex
    exact False.elim (noCreated (by decide))
  · exact good

def firstStep : StepAt [.fn] source middle:=.fn (.root _ _ _ _)
abbrev firstBeta : Label:=match SingleUnsafeCopyFunctionAppInputsChecks.source with |.app _ (.app b _ _) _=>b |t=>t.label

theorem firstRedex : source.subterm [.fn]=some (.app firstBeta (.lam (.atom 6) body) argument) := rfl

def earlyWholeTrace : BetaNodeHistoryPreimage event.final_history earlyHead [.fn,.arg] := by
  apply BetaNodeHistoryPreimage.one (step:=firstStep) firstRedex
  · simpa only [List.append_nil] using
      (BetaNodePreimage.copied (body:=body) (argument:=argument) (site:=[.fn])
        (q:=[.fn,.fn]) (relative:=[]) (old:=argument) rfl rfl)
  · exact .one (step:=event.turn) event.redex
      (.context (by rintro ⟨relative,eq⟩;cases eq)) (.nil _ _)

def lateWholeTrace : BetaNodeHistoryPreimage event.final_history leftHead [.arg,.arg] := by
  apply BetaNodeHistoryPreimage.one (step:=firstStep) firstRedex
  · exact .context (by rintro ⟨relative,eq⟩;cases eq)
  · apply BetaNodeHistoryPreimage.one (step:=event.turn) event.redex
    · simpa only [List.append_nil] using
        (BetaNodePreimage.copied (body:=body) (argument:=argument) (site:=[.arg])
          (q:=[.fn,.fn]) (relative:=[]) (old:=argument) rfl rfl)
    · exact .nil _ _

/-- Two actual returned geometries and recents from ONE full history, with
different prefixes and an early inherited suffix. Only SOURCE iso is claimed. -/
theorem actual_cross_prefix_source_comparison :
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
      SuccessfulEndpointIso source sourceClosed (some eo.fromVertex) (some lo.fromVertex) := by
  obtain ⟨el,es,⟨eg⟩⟩:=earlyCut.spine.incidence_leaf_output sourceClosed earlyCut.lookup
  obtain ⟨ec,er,⟨ex⟩⟩:=earlyCut.recent_far_compatibility event.final_history sourceClosed (by decide) eg
  obtain ⟨ll,ls,⟨lg⟩⟩:=lateCut.spine.incidence_leaf_output sourceClosed lateCut.lookup
  obtain ⟨lc,lr,⟨lx⟩⟩:=lateCut.recent_far_compatibility event.final_history sourceClosed (by decide) lg
  obtain ⟨ep,et,ef⟩:=early_recent_signature er
  obtain ⟨lp,lt,lf⟩:=late_recent_signature lr
  have ehead : earlyCut.edge=er.packet.edge:=one_context_coordinates er.uncreatedSuffix.to_node ef
    (by rintro ⟨relative,eq⟩;cases eq)
  have lhead : lateCut.edge=lr.packet.edge:=empty_coordinates lr.uncreatedSuffix.to_node lf
  have earg:=er.packet.origin.expanded_argument_end_of_nonresult er.packet.frame.expansion (by rw [←ehead,et];decide)
  have larg:=lr.packet.origin.expanded_argument_end_of_nonresult lr.packet.frame.expansion (by rw [←lhead,lt];decide)
  obtain ⟨elow,⟨eo⟩⟩:=ex.expanded_last_endpoints selected sourceSafe
  obtain ⟨llow,⟨lo⟩⟩:=lx.expanded_last_endpoints selected sourceSafe
  have etrace:=er.expanded_argument_history_preimage event.final_history earg eo
  have ltrace:=lr.expanded_argument_history_preimage event.final_history larg lo
  have eoEq : eo.oldEdge=[.fn,.arg]:=etrace.unique earlyWholeTrace
  have loEq : lo.oldEdge=[.arg,.arg]:=ltrace.unique lateWholeTrace
  have sourceComparison:=recent_expanded_argument_source_comparison er lr event.final_history earg larg eo lo
    event.final_old selected sourceSafe sourceClosed copiedMarked copiedMarked (by rfl)
  refine ⟨el,es,eg,ec,er,ex,elow,eo,ll,ls,lg,lc,lr,lx,llow,lo,ep,et,ef,lp,lt,lf,?_,?_,eoEq,loEq,?_,sourceComparison⟩
  · rw [earg,et];rfl
  · rw [larg,lt];rfl
  · rw [eoEq,loEq];decide

#print axioms firstRedex
#print axioms earlyWholeTrace
#print axioms lateWholeTrace
#print axioms actual_cross_prefix_source_comparison
end Lamping.Checks.CrossPrefixExpandedArgumentConsumer
