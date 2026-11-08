import Lamping.Lambda.DirectedReadingCreation
import Lamping.Lambda.UniformOldChainPreimages
import Lamping.Lambda.UniformAnnotatedOrigins
/-!
The first degree marker of an actual directed reading after a uniform OLD
schedule is traced to an original-source prefix. Intermediate sources need
not be marker-free. The recursion keeps literal occurrence ancestry; its
other endpoints are not asserted to preserve labels or admit chains.
-/
namespace Lamping.Lambda.Marked
/-- Splitting the supplied OLD schedule, with no new scheduling choice. -/
private theorem RelativeOldHistory.split_at_internal
    (old : RelativeOldHistory F (pre++post) m n) :
    ∃ middle,RelativeOldHistory F pre m middle ∧RelativeOldHistory F post middle n := by
  induction pre generalizing m with
  | nil => exact ⟨m,.nil _,old⟩
  | cons site rest ih =>
    cases old with
    | cons turn member tail =>
      obtain ⟨middle,before,after⟩ := ih tail
      exact ⟨middle,.cons turn member before,after⟩
end Lamping.Lambda.Marked
namespace Lamping.Lambda.Labelled
private theorem path_unsnoc {ps : List Path} (nonempty : ps≠[]) :
    ∃ pre site,ps=pre++[site] := by
  induction ps with
  | nil => exact False.elim (nonempty rfl)
  | cons p rest ih =>
    cases rest with
    | nil => exact ⟨[],p,rfl⟩
    | cons q qs =>
      obtain ⟨pre,site,same⟩ := ih (by simp)
      exact ⟨p::pre,site,congrArg (p::·) same⟩
/-- Real uncreated incoming readings keep their application/lambda role. -/
private theorem StepAt.uncreated_read_direction {body argument : LTerm}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (readerOrigin : BetaNodePreimage body argument site middle oldMiddle)
    (reads : PrerequisiteReadsDirected target middle edge forward)
    (oldReads : PrerequisiteReads source oldMiddle oldEdge) :
    PrerequisiteReadsDirected source oldMiddle oldEdge forward := by
  refine ⟨oldReads,?_⟩
  cases forward with
  | true =>
    rcases reads.1 with ⟨stamp,fn,arg,lookup,equal⟩ | ⟨stamp,inner,lookup,equal⟩
    · obtain ⟨old,oldLookup,same⟩ := step.preimage_node_constructor redex readerOrigin lookup
      rcases oldReads with ⟨a,f,b,atApp,oldEq⟩ | ⟨a,b,atLambda,oldEq⟩
      · exact oldEq
      · have oldEq := Option.some.inj (oldLookup.symm.trans atLambda)
        subst old;cases same
    · have impossible := equal.symm.trans reads.2
      have lengths := congrArg List.length impossible
      simp only [List.length_append,List.length_singleton] at lengths
      omega
  | false =>
    rcases reads.1 with ⟨stamp,fn,arg,lookup,equal⟩ | ⟨stamp,inner,lookup,equal⟩
    · have impossible := equal.symm.trans reads.2
      have lengths := congrArg List.length impossible
      simp only [List.length_append,List.length_singleton] at lengths
      omega
    · obtain ⟨old,oldLookup,same⟩ := step.preimage_node_constructor redex readerOrigin lookup
      rcases oldReads with ⟨a,f,b,atApp,oldEq⟩ | ⟨a,b,atLambda,oldEq⟩
      · have oldEq := Option.some.inj (oldLookup.symm.trans atApp)
        subst old;cases same
      · exact oldEq
/-- One actual selected OLD turn and its supplied source prefix history.
There is no target representation or desired source-chain field. -/
structure SelectedOldTurn (F : List Path) (source : LTerm) (degree : Label)
    (pre : List Path) (middle target : LTerm) (site : Path) where
  markedBefore : Marked
  markedAfter : Marked
  beforeOld : Marked.RelativeOldHistory F pre (Marked.mark F source.erase) markedBefore
  reduction : Marked.ReductionAt site markedBefore markedAfter
  member : site∈Marked.setResidualPositions F markedBefore
  labels : History pre source middle
  turn : StepAt site middle target
  beta : Label
  body : LTerm
  argument : LTerm
  redex : middle.subterm site=some (.app beta (.lam degree body) argument)
/-- Operational backwards marker descent. The only label equality in the
inherited case is the local actual uncreated-edge equality. Original-source
chains and first-marker prefix conclusions are NOT fields or input oracles. -/
inductive DirectedMarkerSpine (F : List Path) (source : LTerm) (degree : Label) (forward : Bool) :
    List Path →LTerm →List (Option Label) →Path →Prop where
  | inherited {pre middle target site beforeLabels edge oldEdge current old}
      (event : SelectedOldTurn F source degree pre middle target site)
      (lookup : target.subterm edge=some current) (oldLookup : middle.subterm oldEdge=some old)
      (origin : BetaNodePreimage event.body event.argument site edge oldEdge)
      (uncreated : ¬BetaCreatedIncoming event.body site edge)
      (same : current.label=old.label)
      (earlier : DirectedMarkerSpine F source degree forward pre middle beforeLabels oldEdge) :
      DirectedMarkerSpine F source degree forward (pre++[site]) target beforeLabels edge
  | safe {pre middle target site beforeLabels edge reader oldStart oldBefore oldMiddle first last
      current firstNode lastNode lastSourcePosition lastSourceNode}
      (event : SelectedOldTurn F source degree pre middle target site)
      (reading : PrerequisiteReadsDirected target reader edge forward)
      (lookup : target.subterm edge=some current)
      (origin : BetaIncomingReadingOrigin event.body event.argument site edge reader oldMiddle first last)
      (segment : PrerequisitePrefix middle oldStart oldBefore oldMiddle)
      (beforeEq : beforeLabels=oldBefore.map middle.labelAt)
      (beforeSafe : ∀ e∈oldBefore,∀ node,middle.subterm e=some node →node.label.OuterBarsSafe (fun x=>x≠degree))
      (firstLookup : middle.subterm first=some firstNode)
      (firstSafe : firstNode.label.OuterBarsSafe (fun x=>x≠degree))
      (lastLookup : middle.subterm last=some lastNode)
      (lastSourceLookup : source.subterm lastSourcePosition=some lastSourceNode)
      (lastTrace : BetaNodeHistoryPreimage event.labels last lastSourcePosition) :
      DirectedMarkerSpine F source degree forward (pre++[site]) target beforeLabels edge
  | marked {pre middle target site beforeLabels edge reader oldStart oldBefore oldMiddle first last
      current firstNode lastNode lastSourcePosition lastSourceNode}
      (event : SelectedOldTurn F source degree pre middle target site)
      (reading : PrerequisiteReadsDirected target reader edge forward)
      (lookup : target.subterm edge=some current)
      (origin : BetaIncomingReadingOrigin event.body event.argument site edge reader oldMiddle first last)
      (segment : PrerequisitePrefix middle oldStart oldBefore oldMiddle)
      (beforeEq : beforeLabels=oldBefore.map middle.labelAt)
      (beforeSafe : ∀ e∈oldBefore,∀ node,middle.subterm e=some node →node.label.OuterBarsSafe (fun x=>x≠degree))
      (firstLookup : middle.subterm first=some firstNode)
      (firstMarked : ¬firstNode.label.OuterBarsSafe (fun x=>x≠degree))
      (lastLookup : middle.subterm last=some lastNode)
      (lastSourceLookup : source.subterm lastSourcePosition=some lastSourceNode)
      (lastTrace : BetaNodeHistoryPreimage event.labels last lastSourcePosition)
      (earlier : DirectedMarkerSpine F source degree forward pre middle beforeLabels first) :
      DirectedMarkerSpine F source degree forward (pre++[site]) target beforeLabels edge
end Lamping.Lambda.Labelled
namespace Lamping.Lambda.Labelled
private theorem prefix_lookup {t : LTerm} (segment : PrerequisitePrefix t start edges finish)
    (member : e∈edges) : ∃ node,t.subterm e=some node := by
  induction segment with
  | refl => cases member
  | @app p a fn arg es finish atApp notLambda tail ih =>
    rcases List.mem_cons.mp member with rfl | inside
    · exact ⟨fn,by rw [LTerm.subterm_append,atApp];cases fn <;> rfl⟩
    · exact ih inside
  | lam atLambda _ _ ih =>
    rcases List.mem_cons.mp member with rfl | inside
    · exact ⟨_,atLambda⟩
    · exact ih inside
  | var _ _ _ _ _ ih => exact ih member
private theorem safe_from_labels {left right : LTerm} {es other : List Path}
    (same : es.map left.labelAt=other.map right.labelAt)
    (safe : ∀ e∈es,∀ node,left.subterm e=some node →node.label.OuterBarsSafe (fun x=>x≠degree))
    (e : Path) (member : e∈other) (node : LTerm) (lookup : right.subterm e=some node) :
    node.label.OuterBarsSafe (fun x=>x≠degree) := by
  have present : some node.label∈other.map right.labelAt := List.mem_map.mpr ⟨e,member,by simp [LTerm.labelAt,lookup]⟩
  rw [←same] at present
  obtain ⟨old,inside,atOld⟩ := List.mem_map.mp present
  change (left.subterm old).map LTerm.label=some node.label at atOld
  obtain ⟨oldNode,oldLookup,labelEq⟩ := Option.map_eq_some_iff.mp atOld
  rw [←labelEq];exact safe old inside oldNode oldLookup
end Lamping.Lambda.Labelled
namespace Lamping.Lambda.Labelled
private theorem BetaNodeHistoryPreimage.constructor_internal {ps : List Path} {source target current : LTerm}
    {labels : History ps source target} (trace : BetaNodeHistoryPreimage labels p oldPosition)
    (lookup : target.subterm p=some current) :
    ∃ old,source.subterm oldPosition=some old ∧old.constructorTag=current.constructorTag := by
  induction trace with
  | nil => exact ⟨current,lookup,rfl⟩
  | @one _ _ _ _ _ _ _ _ _ _ _ _ step _ redex origin tail ih =>
    obtain ⟨middleNode,middleAt,middleTag⟩ := ih lookup
    obtain ⟨old,oldAt,oldTag⟩ := step.preimage_node_constructor redex origin middleAt
    exact ⟨old,oldAt,oldTag.trans middleTag⟩
private theorem BetaEdgeHistoryPreimages.prefix_length
    (origins : BetaEdgeHistoryPreimages labels es oldEs) : es.length=oldEs.length := by
  induction origins with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih
private theorem BetaEdgeHistoryPreimages.split_two
    (origins : BetaEdgeHistoryPreimages labels (before++[first,last]) oldEdges) :
    ∃ oldBefore oldFirst oldLast,
      oldEdges=oldBefore++[oldFirst,oldLast] ∧
      BetaEdgeHistoryPreimages labels before oldBefore ∧
      BetaNodeHistoryPreimage labels first oldFirst ∧BetaNodeHistoryPreimage labels last oldLast := by
  induction before generalizing oldEdges with
  | nil =>
    cases origins with
    | cons firstTrace tail =>
      cases tail with
      | cons lastTrace finish =>
        cases finish
        exact ⟨[],_,_,rfl,.nil,firstTrace,lastTrace⟩
  | cons head tail ih =>
    cases origins with
    | cons headTrace rest =>
      obtain ⟨oldBefore,oldFirst,oldLast,same,origins,firstTrace,lastTrace⟩ := ih rest
      exact ⟨_::oldBefore,oldFirst,oldLast,by rw [same];rfl,.cons headTrace origins,firstTrace,lastTrace⟩
/-- A safe creation first endpoint really returns to an original selected
FUNCTION endpoint and a real source prefix. This is derived, not a spine field. -/
private theorem SelectedOldTurn.safe_source_prefix_internal
    (event : SelectedOldTurn F source degree pre middle target site)
    (selected : ∀ name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (origin : BetaIncomingReadingOrigin event.body event.argument site edge reader oldMiddle first last)
    (segment : PrerequisitePrefix middle oldStart oldBefore oldMiddle)
    (beforeEq : beforeLabels=oldBefore.map middle.labelAt)
    (beforeSafe : ∀ e∈oldBefore,∀ node,middle.subterm e=some node →node.label.OuterBarsSafe (fun x=>x≠degree))
    (firstLookup : middle.subterm first=some firstNode)
    (firstSafe : firstNode.label.OuterBarsSafe (fun x=>x≠degree)) :
    ∃ sourceStart sourceBefore sourceReader sourceFirst name sourceFirstNode,
      name∈F ∧source.subterm sourceFirst=some sourceFirstNode ∧sourceFirstNode.label=firstNode.label ∧
      PrerequisitePrefix source sourceStart sourceBefore sourceReader ∧PrerequisiteReads source sourceReader sourceFirst ∧
      PrerequisiteChain source sourceReader [sourceFirst,name++[.fn]] ∧
      PrerequisiteChain source sourceStart (sourceBefore++[sourceFirst,name++[.fn]]) ∧
      beforeLabels=sourceBefore.map source.labelAt ∧BetaNodeHistoryPreimage event.labels first sourceFirst ∧
      BetaNodeHistoryPreimage event.labels oldStart sourceStart ∧
      BetaEdgeHistoryPreimages event.labels oldBefore sourceBefore := by
  obtain ⟨name,chosen,originalRedex,_,functionTrace⟩ := event.beforeOld.selected_app_function_preimages event.labels event.member
  obtain ⟨originalBeta,originalBody,originalArgument,atOriginal⟩ := LTerm.degreeAt_redex (selected name chosen)
  have originalFunction : source.subterm (name++[.fn])=some (.lam degree originalBody) := by
    rw [LTerm.subterm_append,atOriginal];rfl
  have degreeSafe := (LTerm.outerBarsSafe_iff _ _).mp sourceSafe degree (LTerm.label_mem_of_subterm originalFunction)
  obtain ⟨lastChain,_⟩ := origin.old_prerequisite event.redex
  have whole := segment.close lastChain
  have allSafe (e : Path) (inside : e∈oldBefore++[first,site++[.fn]]) (node : LTerm)
      (lookup : middle.subterm e=some node) : node.label.OuterBarsSafe (fun x=>x≠degree) := by
    rcases List.mem_append.mp inside with before | tail
    · exact beforeSafe e before node lookup
    · rcases List.mem_cons.mp tail with rfl | tail
      · have same := Option.some.inj (firstLookup.symm.trans lookup);subst node;exact firstSafe
      · have same := List.mem_singleton.mp tail;subst e
        have actual : middle.subterm (site++[.fn])=some (.lam degree event.body) := by rw [LTerm.subterm_append,event.redex];rfl
        have same := Option.some.inj (lookup.symm.trans actual);subst node;exact degreeSafe
  obtain ⟨sourceStart,sourceEdges,sourceChain,startTrace,edgeTraces,mapEq,_⟩ :=
    event.beforeOld.marker_free_chain_preimages (DegreeAligned.initial source F) event.labels selected whole allSafe
  obtain ⟨sourceBefore,sourceFirst,sourceFunction,edgesEq,beforeTraces,firstTrace,lastTrace⟩ := edgeTraces.split_two
  have finalEq := lastTrace.unique functionTrace
  subst sourceFunction
  rw [edgesEq] at sourceChain mapEq
  obtain ⟨coordinate,sourceFirstNode,_,sourceLookup,_,labelEq,_,actualTrace⟩ :=
    event.beforeOld.marker_free_paired_origin (DegreeAligned.initial source F) event.labels event.labels rfl selected firstLookup firstLookup firstSafe
  have firstEq := actualTrace.unique firstTrace
  subst coordinate
  obtain ⟨sb,sa,sr,split,sourcePrefix,sourceTail,sourceRead⟩ := sourceChain.split_at_member
    (List.mem_append_right sourceBefore List.mem_cons_self)
  have same := sourceChain.first_created_split_unique rfl split
  obtain ⟨sameBefore,sameAfter⟩ := same
  subst sb;subst sa
  have beforeMaps : oldBefore.map middle.labelAt=sourceBefore.map source.labelAt :=
    List.append_inj_left (by simpa only [List.map_append,List.map_cons,List.map_nil] using mapEq)
      (by simpa only [List.length_map] using beforeTraces.prefix_length)
  exact ⟨sourceStart,sourceBefore,sr,sourceFirst,name,sourceFirstNode,chosen,sourceLookup,labelEq,
    sourcePrefix,sourceRead,sourceTail,sourceChain,beforeEq.trans beforeMaps,firstTrace,startTrace,beforeTraces⟩
end Lamping.Lambda.Labelled
namespace Lamping.Lambda.Labelled
private theorem PrerequisitePrefix.drop_zero
    (segment : PrerequisitePrefix t start es finish) (empty : es=[]) (chain : PrerequisiteChain t start edges) :
    PrerequisiteChain t finish edges := by
  induction segment with
  | refl => exact chain
  | app => cases empty
  | lam => cases empty
  | var lookup binder split depth tail ih =>
    obtain ⟨otherParent,otherRest,_,_,otherSplit,otherDepth,_,restChain⟩ := chain.variable_cases lookup
    have same := binding_prefix_depth_unique (split.symm.trans otherSplit) (depth.symm.trans otherDepth)
    cases same.1
    exact ih empty restChain
private theorem two_read_constructor
    (chain : PrerequisiteChain t reader [first,last])
    (reading : PrerequisiteReadsDirected t reader first forward) (lookup : t.subterm first=some node) :
    if forward then node.constructorTag≠1 else node.constructorTag=1 := by
  cases forward with
  | true =>
    rcases reading.1 with ⟨stamp,fn,arg,atApp,equal⟩ | ⟨stamp,inner,atLambda,equal⟩
    · have atFirst : t.subterm first=some fn := by rw [equal,LTerm.subterm_append,atApp];cases fn <;> rfl
      have same := Option.some.inj (lookup.symm.trans atFirst)
      subst fn
      cases node with
      | var => change (0:Nat)≠1;decide
      | app => change (2:Nat)≠1;decide
      | lam alpha body =>
        have lengths := congrArg List.length (chain.unique (.redex_app atApp))
        simp only [List.length_cons,List.length_nil] at lengths
        omega
    · have impossible := equal.symm.trans reading.2
      have lengths := congrArg List.length impossible
      simp only [List.length_append,List.length_singleton] at lengths
      omega
  | false =>
    rcases reading.1 with ⟨stamp,fn,arg,atApp,equal⟩ | ⟨stamp,inner,atLambda,equal⟩
    · have impossible := equal.symm.trans reading.2
      have lengths := congrArg List.length impossible
      simp only [List.length_append,List.length_singleton] at lengths
      omega
    · have same := Option.some.inj (lookup.symm.trans (equal ▸ atLambda))
      subst node;rfl
private theorem two_read_direction
    (chain : PrerequisiteChain t reader [first,last]) (reading : PrerequisiteReads t reader first)
    (lookup : t.subterm first=some node)
    (tag : if forward then node.constructorTag≠1 else node.constructorTag=1) :
    PrerequisiteReadsDirected t reader first forward := by
  refine ⟨reading,?_⟩
  cases forward with
  | true =>
    rcases reading with ⟨a,f,b,atApp,equal⟩ | ⟨a,b,atLambda,equal⟩
    · exact equal
    · have same := Option.some.inj (lookup.symm.trans (equal ▸ atLambda))
      subst node;exact False.elim (tag rfl)
  | false =>
    rcases reading with ⟨a,f,b,atApp,equal⟩ | ⟨a,b,atLambda,equal⟩
    · have opposite := two_read_constructor chain ⟨Or.inl ⟨a,f,b,atApp,equal⟩,equal⟩ lookup (forward:=true)
      exact False.elim (opposite tag)
    · exact equal
end Lamping.Lambda.Labelled
namespace Lamping.Lambda.Labelled
private theorem BetaNodeHistoryPreimage.append_start
    {ps qs : List Path} {source middle target : LTerm}
    {firstHistory : History ps source middle} {lastHistory : History qs middle target}
    {edge middleEdge oldEdge : Path}
    (first : BetaNodeHistoryPreimage firstHistory middleEdge oldEdge)
    (last : BetaNodeHistoryPreimage lastHistory edge middleEdge) :
    BetaNodeHistoryPreimage (firstHistory.append lastHistory) edge oldEdge := by
  induction first with
  | nil => exact last
  | @one _ _ _ _ _ _ _ _ _ _ _ _ step _ redex origin tail ih => exact .one (step:=step) redex origin (ih last)
private theorem BetaNodeHistoryPreimage.snoc_start
    {ps : List Path} {source middle target body argument : LTerm}
    {labels : History ps source middle} {turn : StepAt site middle target}
    (redex : middle.subterm site=some (.app beta (.lam alpha body) argument))
    (startOrigin : BetaNodePreimage body argument site start oldStart)
    (trace : BetaNodeHistoryPreimage labels oldStart sourceStart) :
    BetaNodeHistoryPreimage (labels.append (.cons turn (.nil target))) start sourceStart :=
  trace.append_start (.one (step:=turn) redex startOrigin (.nil target start))
private theorem BetaEdgeHistoryPreimages.snoc_before
    {ps : List Path} {edges middleEdges originalEdges : List Path} {source middle target body argument : LTerm}
    {labels : History ps source middle} {turn : StepAt site middle target}
    (redex : middle.subterm site=some (.app beta (.lam alpha body) argument))
    (previous : BetaEdgeHistoryPreimages labels middleEdges originalEdges)
    (current : BetaEdgePreimages body argument site edges middleEdges) :
    BetaEdgeHistoryPreimages (labels.append (.cons turn (.nil target))) edges originalEdges := by
  induction current generalizing originalEdges with
  | nil => cases previous;exact .nil
  | cons origin rest ih =>
    cases previous with
    | cons trace tail =>
      exact .cons (BetaNodeHistoryPreimage.snoc_start (turn:=turn) redex origin trace) (ih tail)
end Lamping.Lambda.Labelled
namespace Lamping.Lambda.Marked
open Labelled

private def MarkerSourceAtStart (F : List Path) (source : LTerm) (degree : Label) (forward : Bool)
    {ps : List Path} {target : LTerm} (labels : Labelled.History ps source target)
    (start : Path) (before : List Path) (beforeLabels : List (Option Label)) (current : LTerm) : Prop :=
  ∃ sourceStart sourceBefore sourceReader sourceFirst name sourceFirstNode marker rest,
    name∈F ∧source.subterm sourceFirst=some sourceFirstNode ∧
    sourceFirstNode.label.OuterBarsSafe (fun x=>x≠degree) ∧
    PrerequisitePrefix source sourceStart sourceBefore sourceReader ∧
    PrerequisiteReadsDirected source sourceReader sourceFirst forward ∧
    PrerequisiteChain source sourceStart (sourceBefore++[sourceFirst,name++[.fn]]) ∧
    beforeLabels=sourceBefore.map source.labelAt ∧marker.MarksDegree degree ∧
    current.label.readLetters forward=sourceFirstNode.label.readLetters forward++marker::rest ∧
    BetaNodeHistoryPreimage labels start sourceStart ∧
    BetaEdgeHistoryPreimages labels before sourceBefore
/-- Actual strict schedule-length recursion constructs all peeling data.
No desired spine, original chain or marker-position certificate is input. -/
private theorem RelativeOldHistory.directed_marker_spine_core
    {F ps : List Path} {source target current : LTerm} {n : Marked} {degree : Label}
    (old : RelativeOldHistory F ps (mark F source.erase) n)
    (labels : Labelled.History ps source target)
    (selected : ∀ name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (segment : PrerequisitePrefix target start before middle)
    (reading : PrerequisiteReadsDirected target middle edge forward)
    (lookup : target.subterm edge=some current)
    (marked : ¬current.label.OuterBarsSafe (fun x=>x≠degree))
    (safeBefore : ∀ e∈before,∀ node,target.subterm e=some node →node.label.OuterBarsSafe (fun x=>x≠degree)) :
    DirectedMarkerSpine F source degree forward ps target (before.map target.labelAt) edge ∧
    MarkerSourceAtStart F source degree forward labels start before (before.map target.labelAt) current := by
  classical
  have main : ∀ k ps n target (old : RelativeOldHistory F ps (mark F source.erase) n)
      (labels : Labelled.History ps source target), ps.length=k →
      ∀ start before middle edge current,
        PrerequisitePrefix target start before middle →PrerequisiteReadsDirected target middle edge forward →
        target.subterm edge=some current →(¬current.label.OuterBarsSafe (fun x=>x≠degree)) →
        (∀ e∈before,∀ node,target.subterm e=some node →node.label.OuterBarsSafe (fun x=>x≠degree)) →
        DirectedMarkerSpine F source degree forward ps target (before.map target.labelAt) edge ∧
        MarkerSourceAtStart F source degree forward labels start before (before.map target.labelAt) current := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro ps n target old labels length start before middle edge current segment reading lookup marked safeBefore
      by_cases empty : ps=[]
      · subst ps;cases labels
        exact False.elim (marked ((LTerm.outerBarsSafe_iff _ _).mp sourceSafe _ (LTerm.label_mem_of_subterm lookup)))
      obtain ⟨pre,site,split⟩ := path_unsnoc empty
      subst ps
      obtain ⟨markBefore,preOld,lastOld⟩ := old.split_at_internal
      cases lastOld with
      | cons reduction member tail =>
        cases tail
        obtain ⟨prior,preLabels,lastLabels⟩ := labels.split
        cases lastLabels with
        | cons turn tail =>
          cases tail
          have preLength : pre.length<k := by
            simp only [List.length_append,List.length_singleton] at length
            omega
          have general := ((relativeOld_iff_relative (selected_mark F source.erase)).mp preOld).general
          have aligned := DegreeAligned.history general (DegreeAligned.initial source F) preLabels
          obtain ⟨name,chosen,residual⟩ := (mem_setResidualPositions F _ site).mp member
          have atDegree := (aligned.trace_degree residual).trans (selected name chosen)
          obtain ⟨beta,body,argument,redex⟩ := LTerm.degreeAt_redex atDegree
          let event : SelectedOldTurn F source degree pre prior target site :=
            ⟨_,_,preOld,reduction,member,preLabels,turn,beta,body,argument,redex⟩
          have beforeOld (e : Path) (inside : e∈before) : ¬BetaCreatedIncoming body site e := by
            obtain ⟨node,atNode⟩ := prefix_lookup segment inside
            intro created
            exact turn.created_label_not_safe redex atNode created (safeBefore e inside node atNode)
          by_cases created : BetaCreatedIncoming body site edge
          · obtain ⟨oldStart,oldBefore,oldMiddle,first,last,startOrigin,origin,oldSegment,edgeOrigins,wholeChain,mapEq,lastAt⟩ :=
              turn.created_prefix_old_chain redex segment reading.1 created beforeOld
            obtain ⟨firstNode,lastNode,marker,rest,firstLookup,lastLookup,markerMarks,wordEq⟩ :=
              origin.directed_label_prefix turn redex reading lookup
            obtain ⟨lastSourcePosition,lastSourceNode,lastSourceLookup,lastTrace⟩ := preLabels.node_preimage_from_lookup lastLookup
            have beforeSafe := safe_from_labels mapEq safeBefore
            by_cases firstSafe : firstNode.label.OuterBarsSafe (fun x=>x≠degree)
            · obtain ⟨s,es,r,f,originalName,node,chosen,atNode,labelEq,sourcePrefix,sourceReads,sourceTail,sourceChain,sourceLabels,firstTrace,startTrace,beforeTraces⟩ :=
                event.safe_source_prefix_internal selected sourceSafe origin oldSegment mapEq beforeSafe firstLookup firstSafe
              obtain ⟨oldReader,jumps,oldReading⟩ := origin.old_directed_reading redex reading
              obtain ⟨two,_⟩ := origin.old_prerequisite redex
              have twoFromReader := jumps.drop_zero rfl two
              have tag := two_read_constructor twoFromReader oldReading firstLookup
              obtain ⟨sourceNode,sourceLookup,sameTag⟩ := firstTrace.constructor_internal firstLookup
              have sameNode := Option.some.inj (sourceLookup.symm.trans atNode)
              subst sourceNode
              rw [←sameTag] at tag
              have directed := two_read_direction sourceTail sourceReads atNode tag
              refine ⟨.safe event reading lookup origin oldSegment mapEq beforeSafe firstLookup firstSafe lastLookup lastSourceLookup lastTrace,
                s,es,r,f,originalName,node,marker,rest,chosen,atNode,?_,sourcePrefix,directed,sourceChain,sourceLabels,markerMarks,?_,?_,?_⟩
              · rw [labelEq];exact firstSafe
              · rw [labelEq];exact wordEq
              · exact BetaNodeHistoryPreimage.snoc_start (turn:=turn) redex startOrigin startTrace
              · exact BetaEdgeHistoryPreimages.snoc_before (turn:=turn) redex beforeTraces edgeOrigins
            · obtain ⟨oldReader,jumps,oldReading⟩ := origin.old_directed_reading redex reading
              have oldPrefix : PrerequisitePrefix prior oldStart oldBefore oldReader := by
                simpa only [List.append_nil] using oldSegment.append jumps
              have earlier := ih pre.length preLength pre markBefore prior preOld preLabels rfl
                oldStart oldBefore oldReader first firstNode oldPrefix oldReading firstLookup firstSafe beforeSafe
              rw [←mapEq] at earlier
              obtain ⟨earlierSpine,s,es,r,f,originalName,node,firstMarker,firstRest,chosen,atNode,safe,sourcePrefix,sourceReads,sourceChain,sourceLabels,firstMarked,firstEquation,startTrace,beforeTraces⟩ := earlier
              rw [firstEquation] at wordEq
              refine ⟨.marked event reading lookup origin oldSegment mapEq beforeSafe firstLookup firstSafe lastLookup lastSourceLookup lastTrace earlierSpine,
                s,es,r,f,originalName,node,firstMarker,firstRest++marker::rest,chosen,atNode,safe,sourcePrefix,sourceReads,sourceChain,sourceLabels,firstMarked,?_,?_,?_⟩
              · simpa only [List.append_assoc,List.cons_append] using wordEq
              · exact BetaNodeHistoryPreimage.snoc_start (turn:=turn) redex startOrigin startTrace
              · exact BetaEdgeHistoryPreimages.snoc_before (turn:=turn) redex beforeTraces edgeOrigins
          · obtain ⟨oldStart,oldMiddle,oldBefore,oldEdge,startOrigin,oldPrefix,middleOrigin,edgeOrigins,oldReads,edgeOrigin,mapEq,chosenEq⟩ :=
              turn.uncreated_prefix_reading redex segment reading.1 beforeOld created
            have directed := turn.uncreated_read_direction redex middleOrigin reading oldReads
            obtain ⟨oldNode,oldLookup,same⟩ := turn.beta_preimage_label redex edgeOrigin lookup created
            have oldMarked : ¬oldNode.label.OuterBarsSafe (fun x=>x≠degree) := by rw [same];exact marked
            have oldSafe := safe_from_labels mapEq safeBefore
            have earlier := ih pre.length preLength pre markBefore prior preOld preLabels rfl
              oldStart oldBefore oldMiddle oldEdge oldNode oldPrefix directed oldLookup oldMarked oldSafe
            rw [←mapEq] at earlier
            obtain ⟨earlierSpine,s,es,r,f,originalName,node,firstMarker,firstRest,chosen,atNode,safe,sourcePrefix,sourceReads,sourceChain,sourceLabels,firstMarked,firstEquation,startTrace,beforeTraces⟩ := earlier
            refine ⟨.inherited event lookup oldLookup edgeOrigin created same.symm earlierSpine,
              s,es,r,f,originalName,node,firstMarker,firstRest,chosen,atNode,safe,sourcePrefix,sourceReads,sourceChain,sourceLabels,firstMarked,?_,?_,?_⟩
            · rw [←same];exact firstEquation
            · exact BetaNodeHistoryPreimage.snoc_start (turn:=turn) redex startOrigin startTrace
            · exact BetaEdgeHistoryPreimages.snoc_before (turn:=turn) redex beforeTraces edgeOrigins
  exact main ps.length ps n target old labels rfl start before middle edge current segment reading lookup marked safeBefore
theorem RelativeOldHistory.directed_marker_spine
    {F ps : List Path} {source target current : LTerm} {n : Marked} {degree : Label}
    (old : RelativeOldHistory F ps (mark F source.erase) n)
    (labels : Labelled.History ps source target)
    (selected : ∀ name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (segment : PrerequisitePrefix target start before middle)
    (reading : PrerequisiteReadsDirected target middle edge forward)
    (lookup : target.subterm edge=some current)
    (marked : ¬current.label.OuterBarsSafe (fun x=>x≠degree))
    (safeBefore : ∀ e∈before,∀ node,target.subterm e=some node →node.label.OuterBarsSafe (fun x=>x≠degree)) :
    DirectedMarkerSpine F source degree forward ps target (before.map target.labelAt) edge := by
  exact (old.directed_marker_spine_core labels selected sourceSafe segment reading lookup marked safeBefore).1
end Lamping.Lambda.Marked
namespace Lamping.Lambda.Labelled
/-- The source prefix and first marker are conclusions proved from the
operational spine. No chain or source label is assumed by the public producer. -/
theorem DirectedMarkerSpine.source_marker_prefix
    (spine : DirectedMarkerSpine F source degree forward ps target beforeLabels edge)
    (selected : ∀ name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (currentLookup : target.subterm edge=some current) :
    ∃ sourceStart sourceBefore sourceReader sourceFirst name sourceFirstNode marker rest,
      name∈F ∧source.subterm sourceFirst=some sourceFirstNode ∧
      sourceFirstNode.label.OuterBarsSafe (fun x=>x≠degree) ∧
      PrerequisitePrefix source sourceStart sourceBefore sourceReader ∧
      PrerequisiteReadsDirected source sourceReader sourceFirst forward ∧
      PrerequisiteChain source sourceStart (sourceBefore++[sourceFirst,name++[.fn]]) ∧
      beforeLabels=sourceBefore.map source.labelAt ∧marker.MarksDegree degree ∧
      current.label.readLetters forward=sourceFirstNode.label.readLetters forward++marker::rest := by
  induction spine generalizing current with
  | inherited event lookup oldLookup origin uncreated same earlier ih =>
    have equal := Option.some.inj (lookup.symm.trans currentLookup)
    cases equal
    obtain ⟨s,es,r,f,name,node,marker,rest,chosen,atNode,safe,segment,reads,chain,labels,marked,equation⟩ := ih oldLookup
    refine ⟨s,es,r,f,name,node,marker,rest,chosen,atNode,safe,segment,reads,chain,labels,marked,?_⟩
    rw [same];exact equation
  | safe event reading lookup origin segment beforeEq beforeSafe firstLookup firstSafe lastLookup lastSourceLookup lastTrace =>
    have equal := Option.some.inj (lookup.symm.trans currentLookup)
    cases equal
    obtain ⟨s,es,r,f,name,node,chosen,atNode,labelEq,sourcePrefix,sourceReads,sourceTail,sourceChain,sourceLabels,firstTrace,_startTrace,_beforeTraces⟩ :=
      event.safe_source_prefix_internal selected sourceSafe origin segment beforeEq beforeSafe firstLookup firstSafe
    obtain ⟨oldReader,jumps,oldReading⟩ := origin.old_directed_reading event.redex reading
    obtain ⟨two,_⟩ := origin.old_prerequisite event.redex
    have tail := jumps.drop_zero rfl two
    have tag := two_read_constructor tail oldReading firstLookup
    obtain ⟨sourceNode,sourceLookup,sameTag⟩ := firstTrace.constructor_internal firstLookup
    have same := Option.some.inj (sourceLookup.symm.trans atNode)
    subst sourceNode
    rw [←sameTag] at tag
    have directed := two_read_direction sourceTail sourceReads atNode tag
    obtain ⟨firstNode,lastNode,marker,rest,firstAt,lastAt,marked,equation⟩ := origin.directed_label_prefix event.turn event.redex reading lookup
    have equal := Option.some.inj (firstAt.symm.trans firstLookup)
    subst firstNode
    refine ⟨s,es,r,f,name,node,marker,rest,chosen,atNode,?_,sourcePrefix,directed,sourceChain,sourceLabels,marked,?_⟩
    · rw [labelEq];exact firstSafe
    · rw [labelEq];exact equation
  | marked event reading lookup origin segment beforeEq beforeSafe firstLookup firstMarked lastLookup lastSourceLookup lastTrace earlier ih =>
    have equal := Option.some.inj (lookup.symm.trans currentLookup)
    cases equal
    obtain ⟨s,es,r,f,name,node,marker,rest,chosen,atNode,safe,sourcePrefix,reads,chain,labels,marked,equation⟩ := ih firstLookup
    obtain ⟨firstNode,lastNode,nextMarker,nextRest,firstAt,lastAt,_,nextEquation⟩ := origin.directed_label_prefix event.turn event.redex reading lookup
    have equal := Option.some.inj (firstAt.symm.trans firstLookup)
    subst firstNode
    refine ⟨s,es,r,f,name,node,marker,rest++nextMarker::nextRest,chosen,atNode,safe,sourcePrefix,reads,chain,labels,marked,?_⟩
    rw [equation] at nextEquation
    simpa only [List.append_assoc,List.cons_append] using nextEquation
end Lamping.Lambda.Labelled
namespace Lamping.Lambda.Marked
open Labelled
/-- No caller spine or source prefix: both follow from the supplied actual
uniform OLD history and unsafe current reading. Suffix may contain markers. -/
theorem RelativeOldHistory.earliest_marker_prefix
    {F ps : List Path} {source target current : LTerm} {n : Marked} {degree : Label}
    (old : RelativeOldHistory F ps (mark F source.erase) n)
    (labels : Labelled.History ps source target)
    (selected : ∀ name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (segment : PrerequisitePrefix target start before middle)
    (reading : PrerequisiteReadsDirected target middle edge forward)
    (lookup : target.subterm edge=some current)
    (marked : ¬current.label.OuterBarsSafe (fun x=>x≠degree))
    (safeBefore : ∀ e∈before,∀ node,target.subterm e=some node →node.label.OuterBarsSafe (fun x=>x≠degree)) :
    DirectedMarkerSpine F source degree forward ps target (before.map target.labelAt) edge ∧
    ∃ sourceStart sourceBefore sourceReader sourceFirst name sourceFirstNode marker rest,
      name∈F ∧source.subterm sourceFirst=some sourceFirstNode ∧
      sourceFirstNode.label.OuterBarsSafe (fun x=>x≠degree) ∧
      PrerequisitePrefix source sourceStart sourceBefore sourceReader ∧
      PrerequisiteReadsDirected source sourceReader sourceFirst forward ∧
      PrerequisiteChain source sourceStart (sourceBefore++[sourceFirst,name++[.fn]]) ∧
      before.map target.labelAt=sourceBefore.map source.labelAt ∧marker.MarksDegree degree ∧
      current.label.readLetters forward=sourceFirstNode.label.readLetters forward++marker::rest := by
  have spine := old.directed_marker_spine labels selected sourceSafe segment reading lookup marked safeBefore
  exact ⟨spine,spine.source_marker_prefix selected sourceSafe lookup⟩
end Lamping.Lambda.Marked



namespace Lamping.Lambda.Marked
open Labelled
theorem RelativeOldHistory.earliest_marker_prefix_at_start
    {F ps : List Path} {source target current : LTerm} {n : Marked} {degree : Label}
    (old : RelativeOldHistory F ps (mark F source.erase) n)
    (labels : Labelled.History ps source target)
    (selected : ∀ name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (segment : PrerequisitePrefix target start before middle)
    (reading : PrerequisiteReadsDirected target middle edge forward)
    (lookup : target.subterm edge=some current)
    (marked : ¬current.label.OuterBarsSafe (fun x=>x≠degree))
    (safeBefore : ∀ e∈before,∀ node,target.subterm e=some node →node.label.OuterBarsSafe (fun x=>x≠degree)) :
    DirectedMarkerSpine F source degree forward ps target (before.map target.labelAt) edge ∧
    ∃ sourceStart sourceBefore sourceReader sourceFirst name sourceFirstNode marker rest,
      name∈F ∧source.subterm sourceFirst=some sourceFirstNode ∧
      sourceFirstNode.label.OuterBarsSafe (fun x=>x≠degree) ∧
      PrerequisitePrefix source sourceStart sourceBefore sourceReader ∧
      PrerequisiteReadsDirected source sourceReader sourceFirst forward ∧
      PrerequisiteChain source sourceStart (sourceBefore++[sourceFirst,name++[.fn]]) ∧
      before.map target.labelAt=sourceBefore.map source.labelAt ∧marker.MarksDegree degree ∧
      current.label.readLetters forward=sourceFirstNode.label.readLetters forward++marker::rest ∧
      BetaNodeHistoryPreimage labels start sourceStart := by
  obtain ⟨spine,s,es,r,f,name,node,marker,rest,chosen,atNode,safe,sourcePrefix,sourceReads,sourceChain,
    sourceLabels,firstMarked,equation,startTrace,_beforeTraces⟩ :=
    old.directed_marker_spine_core labels selected sourceSafe segment reading lookup marked safeBefore
  exact ⟨spine,s,es,r,f,name,node,marker,rest,chosen,atNode,safe,sourcePrefix,sourceReads,sourceChain,
    sourceLabels,firstMarked,equation,startTrace⟩
end Lamping.Lambda.Marked




namespace Lamping.Lambda.Marked
open Labelled
theorem RelativeOldHistory.earliest_marker_prefix_with_before_origins
    {F ps : List Path} {source target current : LTerm} {n : Marked} {degree : Label}
    (old : RelativeOldHistory F ps (mark F source.erase) n)
    (labels : Labelled.History ps source target)
    (selected : ∀ name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (segment : PrerequisitePrefix target start before middle)
    (reading : PrerequisiteReadsDirected target middle edge forward)
    (lookup : target.subterm edge=some current)
    (marked : ¬current.label.OuterBarsSafe (fun x=>x≠degree))
    (safeBefore : ∀ e∈before,∀ node,target.subterm e=some node →node.label.OuterBarsSafe (fun x=>x≠degree)) :
    DirectedMarkerSpine F source degree forward ps target (before.map target.labelAt) edge ∧
    ∃ sourceStart sourceBefore sourceReader sourceFirst name sourceFirstNode marker rest,
      name∈F ∧source.subterm sourceFirst=some sourceFirstNode ∧
      sourceFirstNode.label.OuterBarsSafe (fun x=>x≠degree) ∧
      PrerequisitePrefix source sourceStart sourceBefore sourceReader ∧
      PrerequisiteReadsDirected source sourceReader sourceFirst forward ∧
      PrerequisiteChain source sourceStart (sourceBefore++[sourceFirst,name++[.fn]]) ∧
      before.map target.labelAt=sourceBefore.map source.labelAt ∧marker.MarksDegree degree ∧
      current.label.readLetters forward=sourceFirstNode.label.readLetters forward++marker::rest ∧
      BetaNodeHistoryPreimage labels start sourceStart ∧
      BetaEdgeHistoryPreimages labels before sourceBefore := by
  exact old.directed_marker_spine_core labels selected sourceSafe segment reading lookup marked safeBefore
end Lamping.Lambda.Marked
