import Lamping.Lamping.CanonicalAfterFarComparison
namespace Lamping.Lambda.Labelled
open SyntaxIncidence
variable {source middle target : LTerm}

private theorem node_append
    {firstHistory : History ps source middle} {lastHistory : History qs middle target}
    (first : BetaNodeHistoryPreimage firstHistory middleEdge oldEdge)
    (last : BetaNodeHistoryPreimage lastHistory edge middleEdge) :
    BetaNodeHistoryPreimage (firstHistory.append lastHistory) edge oldEdge := by
  induction first with
  | nil => exact last
  | @one _ _ _ _ _ _ _ _ _ _ _ _ step _ redex origin tail ih =>
    exact .one (step:=step) redex origin (ih last)

private theorem vertex_append
    {firstHistory : History ps source middle} {lastHistory : History qs middle target}
    (first : BetaVertexHistoryPreimage firstHistory mid oldVertex)
    (last : BetaVertexHistoryPreimage lastHistory vertex mid) :
    BetaVertexHistoryPreimage (firstHistory.append lastHistory) vertex oldVertex := by
  cases first with
  | boundary => cases last;exact .boundary
  | proper first => cases last with
    | proper last => exact .proper (node_append first last)

private theorem uncreated_append
    {firstHistory : History ps source middle} {lastHistory : History qs middle target}
    (first : UncreatedNodeHistoryPreimage firstHistory middleEdge oldEdge)
    (last : UncreatedNodeHistoryPreimage lastHistory edge middleEdge) :
    UncreatedNodeHistoryPreimage (firstHistory.append lastHistory) edge oldEdge := by
  induction first with
  | nil => exact last
  | @one _ _ _ _ _ _ _ _ _ _ _ _ step _ redex origin uncreated tail ih =>
    exact .one (step:=step) redex origin uncreated (ih last)

private theorem node_reindex {ps qs : List Path}
    (same : ps=qs) {labels : History ps source target} (other : History qs source target)
    (trace : BetaNodeHistoryPreimage labels edge oldEdge) : BetaNodeHistoryPreimage other edge oldEdge := by
  subst qs
  exact trace

private theorem reflect_node_chain
    {labels : History ps source target}
    (trace : BetaNodeHistoryPreimage labels edge oldEdge)
    (chain : PrerequisiteChain target edge edges) :
    ∃oldEdges,PrerequisiteChain source oldEdge oldEdges := by
  classical
  apply Classical.byContradiction
  intro absent
  exact (trace.no_prerequisite absent) ⟨edges,chain⟩

private theorem transport_far_origin
    (transport : IncomingIncidenceTransport (body:=body) (argument:=argument) (site:=site) snapshot oldSnapshot)
    (forward : Bool) :
    BetaVertexPreimage body argument site _ _ (snapshot.far forward) (oldSnapshot.far forward) := by
  cases forward with
  | true => exact transport.toOrigin
  | false => exact transport.fromOrigin

private def packet_of
    (event : SelectedOldTurn F source degree pre middle target site)
    (reading : PrerequisiteReadsDirected target reader edge forward)
    (origin : BetaIncomingReadingOrigin event.body event.argument site edge reader oldReader first last)
    (lookup : target.subterm edge=some current)
    (snapshot : IncomingIncidenceSnapshot target edge)
    (firstSnapshot : IncomingIncidenceSnapshot middle first)
    (frame : CreatedSpineIncidenceFrame event.body event.argument site middle target first last oldReader forward snapshot firstSnapshot) :
    SpineCreationPacket F source degree forward :=
  ⟨pre,middle,target,site,event,edge,reader,oldReader,first,last,current,lookup,reading,origin,snapshot,firstSnapshot,frame⟩

/-- The last creation packet on THIS geometry, with only genuinely
uncreated inherited turns after it. It is not the earliest safe leaf. -/
structure RecentSpineFrame
    {F : List Path} {source : LTerm} {degree : Label} {forward : Bool}
    {ps : List Path} {target current : LTerm} {beforeLabels : List (Option Label)} {edge : Path}
    {spine : DirectedMarkerSpine F source degree forward ps target beforeLabels edge}
    {lookup : target.subterm edge=some current}
    {leaf : DirectedMarkerLeafOutput F source degree forward ps (current.label.readLetters forward)}
    {snapshot : IncomingIncidenceSnapshot target edge}
    (geometry : SpineIncidenceProvenance F source degree forward spine lookup leaf snapshot) where
  packet : SpineCreationPacket F source degree forward
  olderPackets : List (SpineCreationPacket F source degree forward)
  lastPacket : geometry.creationFrames=olderPackets++[packet]
  suffixSites : List Path
  schedule : ps=(packet.pre++[packet.site])++suffixSites
  suffixHistory : History suffixSites packet.target target
  uncreatedSuffix : UncreatedNodeHistoryPreimage suffixHistory edge packet.edge
  suffixFar : BetaVertexHistoryPreimage suffixHistory (snapshot.far forward) (packet.snapshot.far forward)

namespace SpineIncidenceProvenance
variable {F : List Path} {source : LTerm} {degree : Label} {forward : Bool}
variable {ps : List Path} {target current : LTerm} {beforeLabels : List (Option Label)} {edge : Path}
variable {spine : DirectedMarkerSpine F source degree forward ps target beforeLabels edge}
variable {lookup : target.subterm edge=some current}
variable {leaf : DirectedMarkerLeafOutput F source degree forward ps (current.label.readLetters forward)}
variable {snapshot : IncomingIncidenceSnapshot target edge}

theorem recent_frame (geometry : SpineIncidenceProvenance F source degree forward spine lookup leaf snapshot) :
    Nonempty (RecentSpineFrame geometry) := by
  induction geometry with
  | inherited event lookup oldLookup origin uncreated same earlier earlierGeometry snap transport ih =>
    obtain ⟨recent⟩ := ih
    have lastFar := (BetaVertexHistoryPreimage.refl (History.nil _) (snap.far forward)).prepend (step:=event.turn) event.redex (transport_far_origin transport forward)
    exact ⟨{
      packet:=recent.packet,olderPackets:=recent.olderPackets
      lastPacket:=by simpa only [creationFrames] using recent.lastPacket
      suffixSites:=recent.suffixSites++[_]
      schedule:=by simp only [recent.schedule,List.append_assoc]
      suffixHistory:=recent.suffixHistory.append (.cons event.turn (.nil _))
      uncreatedSuffix:=uncreated_append recent.uncreatedSuffix (.one (step:=event.turn) event.redex origin uncreated (.nil _ _))
      suffixFar:=vertex_append recent.suffixFar lastFar }⟩
  | safe event reading lookup origin _ _ _ _ _ _ _ _ _ _ snap firstSnap frame =>
    exact ⟨{
      packet:=packet_of event reading origin lookup snap firstSnap frame,olderPackets:=[]
      lastPacket:=rfl,suffixSites:=[],schedule:=by simp only [List.append_nil];rfl
      suffixHistory:=.nil _,uncreatedSuffix:=.nil _ _,suffixFar:=.refl (.nil _) _ }⟩
  | marked event reading lookup origin _ _ _ _ _ _ _ _ _ _ _ _ _ snap frame _ih =>
    exact ⟨{
      packet:=packet_of event reading origin lookup snap _ frame,olderPackets:=_
      lastPacket:=rfl,suffixSites:=[],schedule:=by simp only [List.append_nil];rfl
      suffixHistory:=.nil _,uncreatedSuffix:=.nil _ _,suffixFar:=.refl (.nil _) _ }⟩
end SpineIncidenceProvenance
end Lamping.Lambda.Labelled

namespace Lamping.AG
open Graph Lambda Lambda.Labelled SyntaxIncidence
variable {source current : LTerm}

/-- OWN expanded-FAR prefix and complete source chain at the actual
canonical ancestor. No FIRST singleton or earliest triple LAST is substituted. -/
structure RecentFarCompatibility
    {labels : History ps source current}
    {cut : ActualUnsafeMarkerCut F ps source current degree start edges}
    {leaf : DirectedMarkerLeafOutput F source degree cut.forward ps (cut.node.label.readLetters cut.forward)}
    {snapshot : IncomingIncidenceSnapshot current cut.edge}
    {geometry : SpineIncidenceProvenance F source degree cut.forward cut.spine cut.lookup leaf snapshot}
    (canonical : CanonicalAfterFarOutput labels cut snapshot)
    (recent : RecentSpineFrame geometry) where
  expandedProper : ProperPosition recent.packet.middle
  expandedEq : recent.packet.frame.oldFar=some expandedProper
  farHistory : BetaVertexHistoryPreimage (.cons recent.packet.event.turn recent.suffixHistory)
    (some canonical.currentProper) (some expandedProper)
  middleEdges : List Path
  middleChain : PrerequisiteChain recent.packet.middle expandedProper.val middleEdges
  sourcePosition : Path
  sourceNode : LTerm
  sourceLookup : source.subterm sourcePosition=some sourceNode
  prefixNodeTrace : BetaNodeHistoryPreimage recent.packet.event.labels expandedProper.val sourcePosition
  wholeNodeTrace : BetaNodeHistoryPreimage labels canonical.currentProper.val sourcePosition
  sourceCoordinate : sourcePosition=canonical.sourceProper.val
  prefixVertexTrace : BetaVertexHistoryPreimage recent.packet.event.labels
    (some expandedProper) (some canonical.sourceProper)
  originalEdges : List Path
  originalChain : PrerequisiteChain source sourcePosition originalEdges
  exactSourceEdges : originalEdges=canonical.sourceEdges

/-- Compose the actual inherited suffix with THIS frame's farOrigin,
then its independently constructed OWN prefix ancestry. Only actual-history
and actual-chain uniqueness identify the source coordinate and complete list. -/
theorem RecentSpineFrame.canonical_far_compatibility
    {labels : History ps source current}
    {cut : ActualUnsafeMarkerCut F ps source current degree start edges}
    {leaf : DirectedMarkerLeafOutput F source degree cut.forward ps (cut.node.label.readLetters cut.forward)}
    {snapshot : IncomingIncidenceSnapshot current cut.edge}
    {geometry : SpineIncidenceProvenance F source degree cut.forward cut.spine cut.lookup leaf snapshot}
    (recent : RecentSpineFrame geometry)
    (canonical : CanonicalAfterFarOutput labels cut snapshot) :
    Nonempty (RecentFarCompatibility canonical recent) := by
  have throughFrame : BetaVertexHistoryPreimage (.cons recent.packet.event.turn recent.suffixHistory)
      (snapshot.far cut.forward) recent.packet.frame.oldFar :=
    recent.suffixFar.prepend (step:=recent.packet.event.turn) recent.packet.event.redex recent.packet.frame.farOrigin
  have properHistory : BetaVertexHistoryPreimage (.cons recent.packet.event.turn recent.suffixHistory)
      (some canonical.currentProper) recent.packet.frame.oldFar :=
    Eq.mp (congrArg (fun v : Vertex current => BetaVertexHistoryPreimage
      (.cons recent.packet.event.turn recent.suffixHistory) v recent.packet.frame.oldFar) canonical.farEq) throughFrame
  cases expandedEq : recent.packet.frame.oldFar with
  | none =>
    have impossible : BetaVertexHistoryPreimage (.cons recent.packet.event.turn recent.suffixHistory)
        (some canonical.currentProper) none := by simpa only [expandedEq] using properHistory
    cases impossible
  | some expandedProper =>
    have actualHistory : BetaVertexHistoryPreimage (.cons recent.packet.event.turn recent.suffixHistory)
        (some canonical.currentProper) (some expandedProper) := by simpa only [expandedEq] using properHistory
    have actualNode : BetaNodeHistoryPreimage (.cons recent.packet.event.turn recent.suffixHistory)
        canonical.currentProper.val expandedProper.val := by
      cases actualHistory with
      | proper trace => exact trace
    obtain ⟨middleEdges,middleChain⟩ := reflect_node_chain actualNode canonical.currentChain
    obtain ⟨midNode,midLookup⟩ : ∃node,recent.packet.middle.subterm expandedProper.val=some node := by
      rcases expandedProper.property with ⟨stamp,fn,arg,lookup⟩ | ⟨stamp,body,lookup⟩
      · exact ⟨_,lookup⟩
      · exact ⟨_,lookup⟩
    obtain ⟨sourcePosition,sourceNode,sourceLookup,prefixTrace⟩ := recent.packet.event.labels.node_preimage_from_lookup midLookup
    have fullSchedule : recent.packet.pre++(recent.packet.site::recent.suffixSites)=ps := by
      simpa only [List.append_assoc,List.singleton_append] using recent.schedule.symm
    have fullTrace : BetaNodeHistoryPreimage labels canonical.currentProper.val sourcePosition :=
      node_reindex fullSchedule labels (node_append prefixTrace actualNode)
    have sourceEq := fullTrace.unique canonical.nodeTrace
    obtain ⟨originalEdges,originalChain⟩ := reflect_node_chain prefixTrace middleChain
    have canonicalChain : PrerequisiteChain source sourcePosition canonical.sourceEdges :=
      Eq.mp (congrArg (fun p : Path => PrerequisiteChain source p canonical.sourceEdges) sourceEq.symm) canonical.sourceChain
    have edgesEq := originalChain.unique canonicalChain
    have prefixToCanonical : BetaNodeHistoryPreimage recent.packet.event.labels expandedProper.val canonical.sourceProper.val :=
      Eq.mp (congrArg (fun p : Path => BetaNodeHistoryPreimage recent.packet.event.labels expandedProper.val p) sourceEq) prefixTrace
    exact ⟨{
      expandedProper:=expandedProper,expandedEq:=expandedEq,farHistory:=actualHistory
      middleEdges:=middleEdges,middleChain:=middleChain,sourcePosition:=sourcePosition,sourceNode:=sourceNode
      sourceLookup:=sourceLookup,prefixNodeTrace:=prefixTrace,wholeNodeTrace:=fullTrace,sourceCoordinate:=sourceEq
      prefixVertexTrace:=.proper prefixToCanonical,originalEdges:=originalEdges,originalChain:=originalChain,exactSourceEdges:=edgesEq }⟩

theorem ActualUnsafeMarkerCut.recent_far_compatibility
    (labels : History ps source current) (sourceClosed : Closed source.erase)
    (cut : ActualUnsafeMarkerCut F ps source current degree start edges)
    (more : cut.after≠[])
    {leaf : DirectedMarkerLeafOutput F source degree cut.forward ps (cut.node.label.readLetters cut.forward)}
    {snapshot : IncomingIncidenceSnapshot current cut.edge}
    (geometry : SpineIncidenceProvenance F source degree cut.forward cut.spine cut.lookup leaf snapshot) :
    ∃canonical : CanonicalAfterFarOutput labels cut snapshot,
      ∃recent : RecentSpineFrame geometry,Nonempty (RecentFarCompatibility canonical recent) := by
  obtain ⟨canonical⟩ := cut.canonical_far_output labels sourceClosed more snapshot
  obtain ⟨recent⟩ := geometry.recent_frame
  exact ⟨canonical,recent,Lamping.AG.RecentSpineFrame.canonical_far_compatibility recent canonical⟩
end Lamping.AG
