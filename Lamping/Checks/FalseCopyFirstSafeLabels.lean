import Lamping.Lamping.FalseCopyFirstSafeLabels
import Lamping.Checks.SafeLastCopyArgumentAuxInputs
namespace Lamping.Checks.FalseCopyFirstSafeLabelsChecks
open Graph Lambda Lambda.Labelled AG SyntaxIncidence
open SafeLastCopyArgumentAuxInputsChecks

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
    {body argument : LTerm} {site edge reader oldReader first last : Path}
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


abbrev earlyHead : Path:=[.fn,.fn,.arg]
abbrev earlyEdges : List Path:=[earlyHead,[.fn,.fn,.fn]]
def earlyChain : PrerequisiteChain target earlyHead earlyEdges:=
  .lam (parent:=[.fn,.fn]) (step:=.arg) rfl (by decide) (.redex_app (p:=[.fn,.fn]) rfl)
theorem earlyLookup : target.subterm earlyHead=some newK:=rfl

theorem markedHead : ¬newK.label.OuterBarsSafe (fun x=>x≠Label.atom 6) := by
  intro safe
  change (Label.atom 6≠Label.atom 6) ∧True at safe
  exact safe.1 rfl

def earlyReading : PrerequisiteReadsDirected target earlyHead earlyHead false:=
  ⟨Or.inr ⟨_,_,rfl,rfl⟩,rfl⟩
def lateReading : PrerequisiteReadsDirected target leftStart leftStart false:=
  ⟨Or.inr ⟨_,_,rfl,rfl⟩,rfl⟩
def earlySpine : DirectedMarkerSpine F source (.atom 6) false [[.fn],[.arg]] target [] earlyHead:=
  event.final_old.directed_marker_spine event.final_history selected sourceSafe .refl earlyReading earlyLookup markedHead (by simp)
def lateSpine : DirectedMarkerSpine F source (.atom 6) false [[.fn],[.arg]] target [] leftStart:=
  event.final_old.directed_marker_spine event.final_history selected sourceSafe .refl lateReading leftLookup markedHead (by simp)

def earlyCut : ActualUnsafeMarkerCut F [[.fn],[.arg]] source target (.atom 6) earlyHead earlyEdges where
  before:=[]
  edge:=earlyHead
  after:=[[.fn,.fn,.fn]]
  reader:=earlyHead
  node:=newK
  forward:=false
  split:=rfl
  segment:=.refl
  remaining:=earlyChain
  reading:=earlyReading
  lookup:=earlyLookup
  safeBefore:=by simp
  marked:=markedHead
  spine:=earlySpine
  leaf:=earlySpine.leaf_output earlyLookup

def lateCut : ActualUnsafeMarkerCut F [[.fn],[.arg]] source target (.atom 6) leftStart es where
  before:=[]
  edge:=leftStart
  after:=[[.arg,.fn,.fn]]
  reader:=leftStart
  node:=newK
  forward:=false
  split:=rfl
  segment:=.refl
  remaining:=leftChain
  reading:=lateReading
  lookup:=leftLookup
  safeBefore:=by simp
  marked:=markedHead
  spine:=lateSpine
  leaf:=lateSpine.leaf_output leftLookup

private theorem early_recent_signature
    {leaf snapshot}
    {g : SpineIncidenceProvenance F source (.atom 6) false earlyCut.spine earlyCut.lookup leaf snapshot}
    (recent : RecentSpineFrame g) :
    recent.packet.pre=[] ∧recent.packet.site=[.fn] ∧recent.suffixSites=[[.arg]] := by
  rcases two_schedule recent.schedule with good |late
  · exact good
  · obtain ⟨pre,site,suffix⟩:=late
    have head:=empty_coordinates recent.uncreatedSuffix.to_node suffix
    obtain ⟨relative,inside⟩:=origin_below recent.packet.origin
    rw [←head,site] at inside
    change [.fn,.fn,.arg]=[.arg]++relative at inside
    cases inside

private theorem late_recent_signature
    {leaf snapshot}
    {g : SpineIncidenceProvenance F source (.atom 6) false lateCut.spine lateCut.lookup leaf snapshot}
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

private theorem false_copy_shape
    {body argument t : LTerm} {site edge reader oldReader first last : Path}
    (origin : BetaIncomingReadingOrigin body argument site edge reader oldReader first last)
    (reading : PrerequisiteReadsDirected t reader edge false) (notresult : edge≠site) :
    ∃q,edge=site++q ∧first=site++[.arg] ∧last=(site++[.fn,.body])++q := by
  cases origin with
  | resultFunction result function =>
    have size:=congrArg List.length (reading.2.symm.trans (result.trans function));simp at size
  | resultLambda result _ _ => exact False.elim (notresult result)
  | copyFunction occurs copy read =>
    have size:=congrArg List.length reading.2
    simp only [copy,read,List.length_append,List.length_singleton] at size
    omega
  | copyLambda occurs copy _ _ => exact ⟨_,copy,rfl,rfl⟩

private theorem normal_end
    {body : LTerm} {site first last : Path} {es : List Path} {ds : List Bool}
    (expansion : CreatedReadingExpansion body site first last false es ds)
    (normal : last=(site++[.fn,.body])++[.fn,.arg]) : es.getLastD []=last := by
  cases expansion with
  | resultLambda => have size:=congrArg List.length normal;simp at size
  | copyLambda => rfl
  | copyOverlap =>
    have size:=congrArg List.length normal
    simp only [List.length_append,List.length_cons,List.length_nil] at size
    omega

/-- Direct consumption of the new projection on two returned recents from
ONE actual history. The original LASTs are distinct BODY variables, not
ancestors of either current copied lambda. -/
theorem actual_different_prefix_false_labels :
    ∃el esnap,
    ∃eg : SpineIncidenceProvenance F source (.atom 6) false earlyCut.spine earlyCut.lookup el esnap,
    ∃ec : CanonicalAfterFarOutput event.final_history earlyCut esnap,
    ∃er : RecentSpineFrame eg,∃ex : RecentFarCompatibility ec er,
    ∃elow : ExpandedLastSelectedEndpoint er.packet.middle er.packet.site
      (er.packet.frame.edges.getLastD []) false (some ex.expandedProper),
    ∃eo : ExpandedLastOriginalEndpoints F source er.packet.middle (.atom 6) er.packet.event.labels
      (er.packet.frame.edges.getLastD []) elow.node false ec.sourceProper ex.originalEdges,
    ∃ll lsnap,
    ∃lg : SpineIncidenceProvenance F source (.atom 6) false lateCut.spine lateCut.lookup ll lsnap,
    ∃lc : CanonicalAfterFarOutput event.final_history lateCut lsnap,
    ∃lr : RecentSpineFrame lg,∃lx : RecentFarCompatibility lc lr,
    ∃llow : ExpandedLastSelectedEndpoint lr.packet.middle lr.packet.site
      (lr.packet.frame.edges.getLastD []) false (some lx.expandedProper),
    ∃lo : ExpandedLastOriginalEndpoints F source lr.packet.middle (.atom 6) lr.packet.event.labels
      (lr.packet.frame.edges.getLastD []) llow.node false lc.sourceProper lx.originalEdges,
    er.packet.pre=[] ∧er.packet.site=[.fn] ∧er.suffixSites=[[.arg]] ∧
    lr.packet.pre=[[.fn]] ∧lr.packet.site=[.arg] ∧lr.suffixSites=[] ∧
    eo.oldEdge=[.fn,.fn,.body,.fn,.arg] ∧lo.oldEdge=[.arg,.fn,.body,.fn,.arg] ∧
    eo.oldEdge≠lo.oldEdge ∧
    ∃efirst lfirst,
      er.packet.middle.subterm er.packet.first=some efirst ∧
      lr.packet.middle.subterm lr.packet.first=some lfirst ∧
      efirst.label=lfirst.label ∧elow.node.label=llow.node.label ∧
      eo.original.label=lo.original.label ∧
      (elow.node.label.OuterBarsSafe (fun x=>x≠Label.atom 6) ↔
        llow.node.label.OuterBarsSafe (fun x=>x≠Label.atom 6)) := by
  obtain ⟨el,esnap,⟨eg⟩⟩:=earlyCut.spine.incidence_leaf_output sourceClosed earlyCut.lookup
  obtain ⟨ec,er,⟨ex⟩⟩:=earlyCut.recent_far_compatibility event.final_history sourceClosed (by decide) eg
  obtain ⟨ll,lsnap,⟨lg⟩⟩:=lateCut.spine.incidence_leaf_output sourceClosed lateCut.lookup
  obtain ⟨lc,lr,⟨lx⟩⟩:=lateCut.recent_far_compatibility event.final_history sourceClosed (by decide) lg
  obtain ⟨ep,et,ef⟩:=early_recent_signature er
  obtain ⟨lp,lt,lf⟩:=late_recent_signature lr
  have eh : earlyCut.edge=er.packet.edge:=one_context_coordinates er.uncreatedSuffix.to_node ef
    (by rintro ⟨relative,equal⟩;cases equal)
  have lh : lateCut.edge=lr.packet.edge:=empty_coordinates lr.uncreatedSuffix.to_node lf
  have em : er.packet.middle=SafeLastCopyArgumentAuxInputsChecks.source := by
    have history:=er.packet.event.labels
    rw [ep] at history
    exact history.deterministic (.nil _)
  have lm : lr.packet.middle=middle := by
    have history:=lr.packet.event.labels
    rw [lp] at history
    exact history.deterministic preHistory
  obtain ⟨eq,eqHead,eqFirst,eqLast⟩:=false_copy_shape er.packet.origin er.packet.reading (by rw [←eh,et];decide)
  obtain ⟨lq,lqHead,lqFirst,lqLast⟩:=false_copy_shape lr.packet.origin lr.packet.reading (by rw [←lh,lt];decide)
  have eqPath : eq=[.fn,.arg] := by
    have actual:=eqHead
    rw [←eh,et] at actual
    exact List.cons.inj actual |>.2 |>.symm
  have lqPath : lq=[.fn,.arg] := by
    have actual:=lqHead
    rw [←lh,lt] at actual
    exact List.cons.inj actual |>.2 |>.symm
  have enormal : er.packet.last=(er.packet.site++[.fn,.body])++[.fn,.arg] := by rw [eqLast,eqPath]
  have lnormal : lr.packet.last=(lr.packet.site++[.fn,.body])++[.fn,.arg] := by rw [lqLast,lqPath]
  have ee:=normal_end er.packet.frame.expansion enormal
  have le:=normal_end lr.packet.frame.expansion lnormal
  have eSafe : ∀node,er.packet.middle.subterm er.packet.first=some node →node.label.OuterBarsSafe (fun x=>x≠Label.atom 6) := by
    intro node lookup
    rw [em,eqFirst,et] at lookup
    have same : node=.lam (.atom 16) (.var (.atom 17) 0):=Option.some.inj lookup.symm
    rw [same];trivial
  have lSafe : ∀node,lr.packet.middle.subterm lr.packet.first=some node →node.label.OuterBarsSafe (fun x=>x≠Label.atom 6) := by
    intro node lookup
    rw [lm,lqFirst,lt] at lookup
    have same : node=.lam (.atom 16) (.var (.atom 17) 0):=Option.some.inj lookup.symm
    rw [same];trivial
  obtain ⟨elow,⟨eo⟩⟩:=ex.expanded_last_endpoints selected sourceSafe
  obtain ⟨llow,⟨lo⟩⟩:=lx.expanded_last_endpoints selected sourceSafe
  have labelsResult:=recent_normal_false_copy_first_safe_labels er lr selected sourceSafe
    ⟨[.fn,.arg],by decide,enormal⟩ ⟨[.fn,.arg],by decide,lnormal⟩
    eSafe lSafe eo lo elow.lookup llow.lookup (by rfl)
  have eOld : eo.oldEdge=[.fn,.fn,.body,.fn,.arg] := by
    have same:er.packet.frame.edges.getLastD []=eo.oldEdge:=empty_coordinates eo.nodeTrace ep
    rw [←same,ee,enormal,et];rfl
  have lOld : lo.oldEdge=[.arg,.fn,.body,.fn,.arg] := by
    have same:lr.packet.frame.edges.getLastD []=lo.oldEdge:=one_context_coordinates lo.nodeTrace lp (by
      rw [le,lnormal,lt]
      rintro ⟨relative,equal⟩;cases equal)
    rw [←same,le,lnormal,lt];rfl
  exact ⟨el,esnap,eg,ec,er,ex,elow,eo,ll,lsnap,lg,lc,lr,lx,llow,lo,
    ep,et,ef,lp,lt,lf,eOld,lOld,by rw [eOld,lOld];decide,labelsResult⟩

/-- The label projection above uses the original canonical INIT and a
nonempty global prefix, not a freshly relabelled relative source. -/
theorem actual_one_initial_two_read_context :
    INIT original ∧Closed original.erase ∧
    History [[.arg,.fn,.body],[],[.fn],[.arg]] original target ∧
    earlyEdges.length=2 ∧es.length=2 ∧
    earlyCut.before=[] ∧lateCut.before=[] ∧
    earlyCut.after.length=1 ∧lateCut.after.length=1 ∧
    earlyHead≠leftStart ∧
    target.subterm earlyHead=some newK ∧target.subterm leftStart=some newK :=
  ⟨initial,originalClosed,prefixHistory.append event.final_history,rfl,rfl,rfl,rfl,rfl,rfl,
    by decide,rfl,rfl⟩

#print axioms earlyChain
#print axioms markedHead
#print axioms earlySpine
#print axioms lateSpine
#print axioms actual_one_initial_two_read_context
#print axioms actual_different_prefix_false_labels
end Lamping.Checks.FalseCopyFirstSafeLabelsChecks
