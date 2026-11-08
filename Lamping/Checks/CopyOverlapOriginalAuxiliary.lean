import Lamping.Lamping.CopyOverlapOriginalAuxiliary
import Lamping.Checks.DirectedMarkerSpineIncidence
namespace Lamping.Checks.CopyOverlapOriginalAuxiliaryChecks
open Graph Lambda Lambda.Labelled AG SyntaxIncidence
open UniformOldNodeLabelSuffixChecks

abbrev initialTerm : LTerm:=.app (.atom 30) DirectedMarkerSpineIncidenceChecks.Nested.fresh original
abbrev src : LTerm:=.app (.atom 30) DirectedMarkerSpineIncidenceChecks.Nested.fresh source
abbrev mid : LTerm:=.app (.atom 30) DirectedMarkerSpineIncidenceChecks.Nested.fresh DirectedMarkerSpineIncidenceChecks.Nested.reverseInner
abbrev dst : LTerm:=.app (.atom 30) DirectedMarkerSpineIncidenceChecks.Nested.fresh DirectedMarkerSpineIncidenceChecks.Nested.reverseResult
abbrev family : List Path:=[[.arg],[.arg,.arg]]
def firstStep : StepAt [.arg,.arg] src mid:=.arg (.arg (.root _ _ _ _))
def lastStep : StepAt [.arg] mid dst:=.arg (.root _ _ _ _)
def labels : History [[.arg,.arg],[.arg]] src dst:=.cons firstStep (.cons lastStep (.nil _))
def old : Marked.RelativeOldHistory family [[.arg,.arg],[.arg]] (Marked.mark family src.erase)
    (.app [[]] (.lam (.var 0)) (.lam (.var 0))) :=
  .cons (.appR (.redR (.redRoot _ _ _))) (by decide) (.cons (.appR (.redRoot _ _ _)) (by decide) (.nil _))
theorem initial : INIT initialTerm := by
  dsimp [initialTerm,original,bare,caller,I,WrappedSuccessfulChains.I,initLabels,initFrom,nodeCount,DirectedMarkerSpineIncidenceChecks.Nested.fresh]
  simp [INIT,LTerm.labels,IsAtomic,Label.atom]
theorem initialClosed : Closed initialTerm.erase := by
  change Scoped 0 (.app (.lam (.var 0)) bare)
  simp [Scoped]
def prefixHistory : History [[.arg],[.arg],[.arg,.arg]] initialTerm src:=
  .cons (.arg (.root _ _ _ _)) (.cons (.arg (.root _ _ _ _)) (.cons (.arg (.arg (.root _ _ _ _))) (.nil _)))
theorem srcClosed : Closed src.erase:=prefixHistory.closed initialClosed
theorem srcSafe : src.OuterBarsSafe (fun x=>x≠Label.atom 10):=⟨trivial,⟨trivial,trivial⟩,source_safe⟩
theorem selected (p : Path) (member : p∈family) : src.degreeAt p=some (.atom 10) := by
  rcases List.mem_cons.mp member with rfl | member
  · rfl
  · have eq:=List.mem_singleton.mp member;subst p;rfl
theorem chain : PrerequisiteChain dst [.arg] [[.arg],[.fn]]:=
  .lam (parent:=[]) (step:=.arg) rfl (by decide) (.redex_app (p:=[]) rfl)
theorem read : PrerequisiteReadsDirected dst [.arg] [.arg] false:=⟨Or.inr ⟨_,_,rfl,rfl⟩,rfl⟩
theorem marked : ¬DirectedMarkerSpineIncidenceChecks.Nested.reverseResult.label.OuterBarsSafe (fun x=>x≠Label.atom 10):=
  lastStep.created_label_not_safe (by rfl) (current:=DirectedMarkerSpineIncidenceChecks.Nested.reverseResult) (by rfl) (Or.inl rfl)
def spine : DirectedMarkerSpine family src (.atom 10) false [[.arg,.arg],[.arg]] dst [] [.arg]:=
  old.directed_marker_spine labels selected srcSafe .refl read rfl marked (by simp)
def cut : ActualUnsafeMarkerCut family [[.arg,.arg],[.arg]] src dst (.atom 10) [.arg] [[.arg],[.fn]] where
  before:=[]
  edge:=[.arg]
  after:=[[.fn]]
  reader:=[.arg]
  node:=DirectedMarkerSpineIncidenceChecks.Nested.reverseResult
  forward:=false
  split:=rfl
  segment:=.refl
  remaining:=chain
  reading:=read
  lookup:=rfl
  safeBefore:=by simp
  marked:=marked
  spine:=spine
  leaf:=spine.leaf_output rfl
private theorem two_schedule {pre suffix : List Path} {site : Path}
    (schedule : [[.arg,.arg],[.arg]]=(pre++[site])++suffix) :
    (pre=[] ∧site=[.arg,.arg] ∧suffix=[[.arg]]) ∨
    (pre=[[.arg,.arg]] ∧site=[.arg] ∧suffix=[]) := by
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
private theorem one_uncreated {source target body argument : LTerm} {ps : List Path}
    {p old : Path} {h : History ps source target}
    (trace : UncreatedNodeHistoryPreimage h p old) (single : ps=[site])
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument)) :
    ¬BetaCreatedIncoming body site p := by
  subst ps
  cases trace with
  | one actual origin uncreated tail =>
    cases tail
    have same:=Option.some.inj (actual.symm.trans redex)
    cases same
    exact uncreated
private theorem empty_coordinates {source target : LTerm} {ps : List Path}
    {p old : Path} {h : History ps source target} (trace : BetaNodeHistoryPreimage h p old) (empty : ps=[]) : p=old := by
  subst ps
  cases trace
  rfl
private theorem recent_signature
    {leaf snapshot}
    {g : SpineIncidenceProvenance family src (.atom 10) false cut.spine cut.lookup leaf snapshot}
    (recent : RecentSpineFrame g) :
    recent.packet.pre=[[.arg,.arg]] ∧recent.packet.site=[.arg] ∧recent.suffixSites=[] := by
  rcases two_schedule recent.schedule with early | good
  · obtain ⟨pre,site,suffix⟩:=early
    have history : History [[.arg,.arg]] src recent.packet.target := by
      have actual:=recent.packet.event.labels.append (.cons recent.packet.event.turn (.nil _))
      exact Eq.mp (congrArg (fun sites : List Path=>History sites src recent.packet.target)
        (show recent.packet.pre++[recent.packet.site]=[[.arg,.arg]] from by rw [pre,site];rfl)) actual
    have targetEq:=history.deterministic (.cons firstStep (.nil _))
    have redex : recent.packet.target.subterm [.arg]=some (.app DirectedMarkerSpineIncidenceChecks.Nested.reverseInner.label (.lam (.atom 10) (.var (.atom 11) 0))
      (WrappedSuccessfulChains.contractRoot (match UniformOldNodeLabelSuffixChecks.source with |.app _ _ a=>a |t=>t))) := by rw [targetEq];rfl
    exact False.elim ((one_uncreated recent.uncreatedSuffix suffix redex) (Or.inl rfl))
  · exact good
private theorem rootvar_false {first last : Path}
    (origin : BetaIncomingReadingOrigin (.var stamp 0) argument site edge reader oldReader first last)
    (reading : PrerequisiteReadsDirected t reader edge false) :
    first=site++[.arg] ∧last=site++[.fn,.body] := by
  cases origin with
  | resultFunction result fn =>
    have n:=congrArg List.length (reading.2.symm.trans (result.trans fn));simp at n
  | resultLambda _ _ impossible => cases impossible
  | @copyFunction parent occurs _ _ =>
    change subtermAt (.var 0) (parent++[.fn])=some (.var _) at occurs
    cases parent with
    | nil => cases occurs
    | cons s tail => cases s <;> cases occurs
  | @copyLambda q a b occurs copy read shape =>
    have empty : q=[] := by
      change subtermAt (.var 0) q=some (.var _) at occurs
      cases q with
      | nil => rfl
      | cons s tail => cases s <;> cases occurs
    exact ⟨rfl,by rw [empty,List.append_nil]⟩
private theorem actual_rootcopy
    {leaf snapshot}
    {g : SpineIncidenceProvenance family src (.atom 10) false cut.spine cut.lookup leaf snapshot}
    (recent : RecentSpineFrame g) :
    recent.packet.first=recent.packet.site++[.arg] ∧recent.packet.last=recent.packet.site++[.fn,.body] := by
  obtain ⟨pre,site,_⟩:=recent_signature recent
  have history : History [[.arg,.arg]] src recent.packet.middle:=by rw [←pre];exact recent.packet.event.labels
  have middleEq:=history.deterministic (.cons firstStep (.nil _))
  have redex:=recent.packet.event.redex
  conv at redex => lhs; rw [middleEq,site]
  have bodyEq : recent.packet.event.body=.var (.atom 11) 0 := by
    have eq:=Option.some.inj (redex.symm.trans (show mid.subterm [.arg]=some (.app DirectedMarkerSpineIncidenceChecks.Nested.reverseInner.label (.lam (.atom 10) (.var (.atom 11) 0))
      (WrappedSuccessfulChains.contractRoot (match UniformOldNodeLabelSuffixChecks.source with |.app _ _ a=>a |t=>t))) from rfl))
    injection eq with _ fn _
    injection fn
  have origin:=recent.packet.origin
  rw [bodyEq] at origin
  exact rootvar_false origin recent.packet.reading
private theorem one_context_coordinates {source target : LTerm} {ps : List Path}
    {p old : Path} {h : History ps source target}
    (trace : BetaNodeHistoryPreimage h p old) (single : ps=[site])
    (outside : ¬∃relative,p=site++relative) : p=old := by
  subst ps
  cases trace with
  | one redex origin tail =>
    cases tail
    exact (origin.unique (.context outside)).symm

abbrev innerResult : LTerm:=WrappedSuccessfulChains.contractRoot
  (match UniformOldNodeLabelSuffixChecks.source with |.app _ _ a=>a |t=>t)
theorem innerMarked : ¬innerResult.label.OuterBarsSafe (fun x=>x≠Label.atom 10):=
  firstStep.created_label_not_safe (by rfl) (current:=innerResult) (by rfl) (Or.inl rfl)

/-- The recently created FIRST is genuinely marked in THIS middle term. -/
theorem recent_first_marked
    {leaf snapshot}
    {g : SpineIncidenceProvenance family src (.atom 10) false cut.spine cut.lookup leaf snapshot}
    (recent : RecentSpineFrame g) :
    recent.packet.middle.subterm recent.packet.first=some innerResult ∧
    ¬innerResult.label.OuterBarsSafe (fun x=>x≠Label.atom 10) := by
  obtain ⟨pre,site,_⟩:=recent_signature recent
  have h : History [[.arg,.arg]] src recent.packet.middle:=by rw [←pre];exact recent.packet.event.labels
  have midEq:=h.deterministic (.cons firstStep (.nil _))
  have firstEq:=(actual_rootcopy recent).1
  refine ⟨?_,innerMarked⟩
  rw [midEq,firstEq,site]
  rfl

/-- Node ancestry of the current copied lambda is a different original
occurrence from the expanded LAST APP. -/
def currentNodeTrace : BetaNodeHistoryPreimage labels [.arg] [.arg,.arg,.arg] := by
  apply BetaNodeHistoryPreimage.one (step:=firstStep)
    (show src.subterm [.arg,.arg]=some (.app (UniformOldNodeLabelSuffixChecks.firstArgument.label)
      (.lam (.atom 10) (.var (.atom 11) 0)) UniformOldNodeLabelSuffixChecks.secondArgument) from rfl)
    (BetaNodePreimage.copied (q:=[]) (relative:=[]) (old:=UniformOldNodeLabelSuffixChecks.secondArgument) (by rfl) (by rfl))
  exact BetaNodeHistoryPreimage.one (step:=lastStep) (by rfl)
    (BetaNodePreimage.copied (q:=[]) (relative:=[]) (old:=innerResult) (by rfl) (by rfl)) (.nil _ _)

theorem distinct_current_ancestor : BetaNodeHistoryPreimage labels [.arg] [.arg,.arg,.arg] ∧
    ([.arg,.arg,.arg] : Path)≠[.arg] :=⟨currentNodeTrace,by decide⟩
/-- The very same returned geometry, recent packet and original endpoints.
The LAST is the selected APP at ARG, not the current copied lambda's ancestor. -/
theorem actual_nonterminal_q0 :
    ∃leaf snapshot,
    ∃g : SpineIncidenceProvenance family src (.atom 10) false cut.spine cut.lookup leaf snapshot,
    ∃canonical : CanonicalAfterFarOutput labels cut snapshot,
    ∃recent : RecentSpineFrame g,
    ∃compat : RecentFarCompatibility canonical recent,
    ∃low : ExpandedLastSelectedEndpoint recent.packet.middle recent.packet.site
      (recent.packet.frame.edges.getLastD []) false (some compat.expandedProper),
    ∃out : ExpandedLastOriginalEndpoints family src recent.packet.middle (.atom 10) recent.packet.event.labels
      (recent.packet.frame.edges.getLastD []) low.node false canonical.sourceProper compat.originalEdges,
      recent.packet.pre=[[.arg,.arg]] ∧recent.packet.site=[.arg] ∧recent.suffixSites=[] ∧
      recent.packet.first=recent.packet.site++[.arg] ∧recent.packet.last=recent.packet.site++[.fn,.body] ∧
      recent.packet.middle.subterm recent.packet.first=some innerResult ∧
      ¬innerResult.label.OuterBarsSafe (fun x=>x≠Label.atom 10) ∧
      recent.packet.frame.edges.getLastD []=[.arg] ∧out.oldEdge=[.arg] ∧
      AuxiliaryAt src out.oldEdge ∧out.toVertex.val=[.arg] ∧out.targetEdges=[[.arg,.fn]] ∧
      out.fromVertex.val=[] ∧out.sourceEdges=[[.fn]] := by
  obtain ⟨leaf,snapshot,⟨g⟩⟩:=cut.spine.incidence_leaf_output srcClosed cut.lookup
  obtain ⟨canonical,recent,⟨compat⟩⟩:=cut.recent_far_compatibility labels srcClosed (by decide) g
  obtain ⟨low,⟨out⟩⟩:=compat.expanded_last_endpoints selected srcSafe
  have sig:=recent_signature recent
  have role:=actual_rootcopy recent
  obtain ⟨_,endEq,aux,name,beta,body,argument,member,redex,position,edgesEq⟩:=
    cut.copy_overlap_original_last_auxiliary recent (by decide) role selected out
  have endCoord : recent.packet.frame.edges.getLastD []=[.arg]:=endEq.trans sig.2.1
  have trace : BetaNodeHistoryPreimage recent.packet.event.labels [.arg] out.oldEdge:=by
    exact Eq.mp (congrArg (fun p : Path=>BetaNodeHistoryPreimage recent.packet.event.labels p out.oldEdge) endCoord) out.nodeTrace
  have oldEq : out.oldEdge=[.arg]:=(one_context_coordinates trace sig.1 (by rintro ⟨r,h⟩;cases h)).symm
  let app : ProperPosition src:=⟨[.arg],Or.inl ⟨_,_,_,(by rfl)⟩⟩
  have actualTarget : Target src out.oldEdge (some app):=by rw [oldEq];exact Or.inl rfl
  have targetEq:=Option.some.inj (Target.unique out.targetSpec actualTarget)
  have targetPosition : out.toVertex.val=[.arg]:=congrArg Subtype.val targetEq
  have nameEq : name=[.arg]:=position.symm.trans targetPosition
  have targetEdges : out.targetEdges=[[.arg,.fn]]:=by rw [edgesEq,nameEq];rfl
  let root : ProperPosition src:=⟨[],Or.inl ⟨_,_,_,(by rfl)⟩⟩
  have actualSource : Source src out.oldEdge (some root):=by
    rw [oldEq]
    exact ⟨.arg,_,_,rfl,rfl,.arg⟩
  have sourceEq:=Option.some.inj (Source.unique out.sourceSpec actualSource)
  have sourcePosition : out.fromVertex.val=[]:=congrArg Subtype.val sourceEq
  have oldChain : PrerequisiteChain src [] out.sourceEdges:=by
    have c:=out.sourceChain
    change PrerequisiteChain src out.fromVertex.val out.sourceEdges at c
    rw [sourcePosition] at c;exact c
  have sourceEdges : out.sourceEdges=[[.fn]]:=oldChain.unique (.redex_app (p:=[]) rfl)
  exact ⟨leaf,snapshot,g,canonical,recent,compat,low,out,sig.1,sig.2.1,sig.2.2,
    role.1,role.2,(recent_first_marked recent).1,(recent_first_marked recent).2,endCoord,oldEq,aux,targetPosition,targetEdges,sourcePosition,sourceEdges⟩

/-- The original INIT and complete history are retained through the wrapper. -/
theorem same_initial_history : INIT initialTerm ∧Closed initialTerm.erase ∧
    History [[.arg],[.arg],[.arg,.arg],[.arg,.arg],[.arg]] initialTerm dst ∧
    PrerequisiteChain dst [.arg] [[.arg],[.fn]] :=
  ⟨initial,initialClosed,prefixHistory.append labels,chain⟩

/-- The earlier terminal FN-wrapper remains terminal; no AFTER completion
is inferred from its event-local endpoint chains. -/
theorem existing_terminal_regression :
    INIT DirectedMarkerSpineIncidenceChecks.Nested.originalWrapped ∧
    PrerequisiteChain DirectedMarkerSpineIncidenceChecks.Nested.targetReverse [.fn] [[.fn]] ∧
    ([[.fn]] : List Path).tail=[] :=
  ⟨DirectedMarkerSpineIncidenceChecks.Nested.initial,
    DirectedMarkerSpineIncidenceChecks.Nested.successful_readings.2,rfl⟩

#print axioms ActualUnsafeMarkerCut.copy_overlap_original_last_auxiliary
#print axioms initial
#print axioms prefixHistory
#print axioms old
#print axioms selected
#print axioms chain
#print axioms recent_first_marked
#print axioms distinct_current_ancestor
#print axioms actual_nonterminal_q0
#print axioms same_initial_history
#print axioms existing_terminal_regression
end Lamping.Checks.CopyOverlapOriginalAuxiliaryChecks
