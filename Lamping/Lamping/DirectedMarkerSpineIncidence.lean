import Lamping.Lamping.CreatedReadingIncidenceExpansion
import Lamping.Lambda.DirectedMarkerLeafWords
namespace Lamping.Lambda.Labelled
open SyntaxIncidence
variable {source target : LTerm}

/-- Actual incidences at ONE literal incoming edge; no successful chain or
label-derived coordinate is supplied. -/
structure IncomingIncidenceSnapshot (t : LTerm) (edge : Path) where
  fromVertex : Vertex t
  toVertex : Vertex t
  fromSpec : Source t edge fromVertex
  toSpec : Target t edge toVertex

def IncomingIncidenceSnapshot.near (s : IncomingIncidenceSnapshot t edge) (forward : Bool) : Vertex t :=
  if forward then s.fromVertex else s.toVertex
def IncomingIncidenceSnapshot.far (s : IncomingIncidenceSnapshot t edge) (forward : Bool) : Vertex t :=
  if forward then s.toVertex else s.fromVertex

private theorem snapshot_exists (closed : Closed t.erase) (lookup : t.subterm edge=some current) :
    Nonempty (IncomingIncidenceSnapshot t edge) := by
  let position : Edge t:=⟨edge,by rw [←LTerm.erase_subterm,lookup];rfl⟩
  obtain ⟨fromVertex,fromSpec⟩:=source_total t position
  obtain ⟨toVertex,toSpec⟩:=target_total t closed position
  exact ⟨⟨fromVertex,toVertex,fromSpec,toSpec⟩⟩

private theorem reading_near_target
    (reading : PrerequisiteReadsDirected t reader edge forward)
    (snapshot : IncomingIncidenceSnapshot t edge) :
    Target t reader (snapshot.near forward) := by
  cases forward with
  | false =>
    have same : edge=reader:=reading.2
    simpa only [IncomingIncidenceSnapshot.near,if_false,Bool.false_eq_true,same] using snapshot.toSpec
  | true =>
    rcases reading.1 with ⟨stamp,fn,arg,lookup,equal⟩ | ⟨stamp,body,lookup,equal⟩
    · let actual : ProperPosition t:=⟨reader,Or.inl ⟨stamp,fn,arg,lookup⟩⟩
      have fromSpec : Source t edge (some actual):=⟨.fn,_,_,equal,lookup,.fn⟩
      have same:=Source.unique snapshot.fromSpec fromSpec
      change Target t reader snapshot.fromVertex
      rw [same]
      exact Or.inl rfl
    · have size:=congrArg List.length (equal.symm.trans reading.2)
      simp at size

/-- The actual uncreated incoming occurrence transports BOTH incidences to
exactly the already supplied earlier snapshot. -/
structure IncomingIncidenceTransport
    {body argument : LTerm} {site edge oldEdge : Path}
    (currentSnapshot : IncomingIncidenceSnapshot target edge)
    (oldSnapshot : IncomingIncidenceSnapshot source oldEdge) where
  fromOrigin : BetaVertexPreimage body argument site source target currentSnapshot.fromVertex oldSnapshot.fromVertex
  toOrigin : BetaVertexPreimage body argument site source target currentSnapshot.toVertex oldSnapshot.toVertex

private theorem snapshot_transport
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (origin : BetaNodePreimage body argument site edge oldEdge)
    (lookup : target.subterm edge=some current) (uncreated : ¬BetaCreatedIncoming body site edge)
    (currentSnapshot : IncomingIncidenceSnapshot target edge)
    (oldSnapshot : IncomingIncidenceSnapshot source oldEdge) :
    Nonempty (IncomingIncidenceTransport (body:=body) (argument:=argument) (site:=site) currentSnapshot oldSnapshot) := by
  obtain ⟨fromVertex,fromSpec,fromOrigin⟩:=step.beta_incidence_source_preimage redex origin lookup uncreated currentSnapshot.fromSpec
  obtain ⟨toVertex,toSpec,toOrigin⟩:=step.beta_incidence_target_preimage redex origin currentSnapshot.toSpec
  have sameFrom:=Source.unique fromSpec oldSnapshot.fromSpec
  have sameTo:=Target.unique toSpec oldSnapshot.toSpec
  rw [sameFrom] at fromOrigin
  rw [sameTo] at toOrigin
  exact ⟨⟨fromOrigin,toOrigin⟩⟩

private theorem expansion_heads (expansion : CreatedReadingExpansion body site first last forward es ds) :
    es=first::es.tail ∧ds=forward::ds.tail := by
  cases expansion <;> exact ⟨rfl,rfl⟩

/-- The FIRST far junction and the actual two/four-edge tail are retained.
In a marked spine this firstSnapshot is EXACTLY the earlier IH snapshot. -/
structure CreatedSpineIncidenceFrame
    (body argument : LTerm) (site : Path) (middle target : LTerm)
    (first last oldReader : Path) (forward : Bool)
    (currentSnapshot : IncomingIncidenceSnapshot target edge)
    (firstSnapshot : IncomingIncidenceSnapshot middle first) where
  oldNear : Vertex middle
  oldFar : Vertex middle
  edges : List Path
  directions : List Bool
  oldNearTarget : Target middle oldReader oldNear
  nearOrigin : BetaVertexPreimage body argument site middle target (currentSnapshot.near forward) oldNear
  farOrigin : BetaVertexPreimage body argument site middle target (currentSnapshot.far forward) oldFar
  fullChase : IncidenceChase middle oldNear edges directions oldFar
  expansion : CreatedReadingExpansion body site first last forward edges directions
  nearJunction : oldNear=firstSnapshot.near forward
  tailChase : IncidenceChase middle (firstSnapshot.far forward) edges.tail directions.tail oldFar
  finalIncidence : if forward then Target middle (edges.getLastD []) oldFar else Source middle (edges.getLastD []) oldFar

private theorem make_frame
    (step : StepAt site middle target)
    (redex : middle.subterm site=some (.app beta (.lam alpha body) argument))
    (origin : BetaIncomingReadingOrigin body argument site edge reader oldReader first last)
    (reading : PrerequisiteReadsDirected target reader edge forward)
    (lookup : target.subterm edge=some current)
    (currentSnapshot : IncomingIncidenceSnapshot target edge)
    (firstSnapshot : IncomingIncidenceSnapshot middle first) :
    Nonempty (CreatedSpineIncidenceFrame body argument site middle target first last oldReader forward currentSnapshot firstSnapshot) := by
  have near:=reading_near_target reading currentSnapshot
  have far : if forward then Target target edge (currentSnapshot.far forward) else Source target edge (currentSnapshot.far forward) := by
    cases forward with
    | true => exact currentSnapshot.toSpec
    | false => exact currentSnapshot.fromSpec
  obtain ⟨oldNear,oldFar,edges,dirs,oldNearTarget,nearOrigin,walk,farOrigin,finalIncidence,expansion⟩:=
    origin.incidence_expansion step redex reading lookup near far
  obtain ⟨headEdge,headDirection⟩:=expansion_heads expansion
  have parts : oldNear=firstSnapshot.near forward ∧
      IncidenceChase middle (firstSnapshot.far forward) edges.tail dirs.tail oldFar := by
    rw [headEdge,headDirection] at walk
    cases forward with
    | true =>
      cases walk with
      | forward fromSpec toSpec rest =>
        have fromEq:=Source.unique fromSpec firstSnapshot.fromSpec
        have toEq:=Target.unique toSpec firstSnapshot.toSpec
        exact ⟨fromEq,by simpa only [IncomingIncidenceSnapshot.far,if_true,toEq] using rest⟩
    | false =>
      cases walk with
      | backward toSpec fromSpec rest =>
        have fromEq:=Target.unique toSpec firstSnapshot.toSpec
        have toEq:=Source.unique fromSpec firstSnapshot.fromSpec
        exact ⟨fromEq,by simpa only [IncomingIncidenceSnapshot.far,if_false,Bool.false_eq_true,toEq] using rest⟩
  exact ⟨⟨oldNear,oldFar,edges,dirs,oldNearTarget,nearOrigin,farOrigin,walk,expansion,parts.1,parts.2,finalIncidence⟩⟩

/-- Reindex only the proved word equality; all actual leaf data stay fixed. -/
def DirectedMarkerLeafOutput.reword
    (leaf : DirectedMarkerLeafOutput F source degree forward ps word) (same : word=other) :
    DirectedMarkerLeafOutput F source degree forward ps other :=
  {leaf with equation:=same.symm.trans leaf.equation}

private theorem formula_prefix
    (formula : ExactDirectedReadingFormula middle site degree forward firstNode lastNode marker current) :
    ∃rest,current.label.readLetters forward=firstNode.label.readLetters forward++marker::rest := by
  rcases formula with ordinary | ⟨_,_,argument,_,overlap⟩ | ⟨_,_,app,_,overlap⟩
  · exact ⟨_,ordinary⟩
  · exact ⟨_,overlap⟩
  · exact ⟨_,overlap⟩

private def safe_leaf
    (event : SelectedOldTurn F source degree pre middle target site)
    (reading : PrerequisiteReadsDirected target reader edge forward)
    (origin : BetaIncomingReadingOrigin event.body event.argument site edge reader oldReader first last)
    (lookup : target.subterm edge=some current)
    (firstLookup : middle.subterm first=some firstNode)
    (firstSafe : firstNode.label.OuterBarsSafe (fun x=>x≠degree))
    (lastLookup : middle.subterm last=some lastNode)
    (lastSourceLookup : source.subterm lastSourcePosition=some lastSourceNode)
    (lastTrace : BetaNodeHistoryPreimage event.labels last lastSourcePosition)
    (marks : marker.MarksDegree degree)
    (formula : ExactDirectedReadingFormula middle site degree forward firstNode lastNode marker current) :
    DirectedMarkerLeafOutput F source degree forward (pre++[site]) (current.label.readLetters forward) where
  pre:=pre
  middle:=middle
  target:=target
  site:=site
  event:=event
  after:=[]
  schedule:=rfl
  edge:=edge
  reader:=reader
  oldReader:=oldReader
  first:=first
  last:=last
  current:=current
  firstNode:=firstNode
  lastNode:=lastNode
  reading:=reading
  origin:=origin
  lookup:=lookup
  firstLookup:=firstLookup
  lastLookup:=lastLookup
  firstSafe:=firstSafe
  lastSourcePosition:=lastSourcePosition
  lastSourceNode:=lastSourceNode
  lastSourceLookup:=lastSourceLookup
  lastTrace:=lastTrace
  marker:=marker
  marks:=marks
  formula:=formula
  continuation:=[]
  equation:=(List.append_nil _).symm

/-- A finite geometric execution OF THIS supplied marker spine. The original
safe leaf is retained exactly by reword/extend/snoc; no same-word leaf is
reselected. This is derived output data, never a history or REP premise. -/
inductive SpineIncidenceProvenance (F : List Path) (source : LTerm) (degree : Label) (forward : Bool) :
    {ps : List Path} →{target : LTerm} →{beforeLabels : List (Option Label)} →{edge : Path} →{current : LTerm} →
    (spine : DirectedMarkerSpine F source degree forward ps target beforeLabels edge) →
    (lookup : target.subterm edge=some current) →
    DirectedMarkerLeafOutput F source degree forward ps (current.label.readLetters forward) →
    IncomingIncidenceSnapshot target edge →Type where
  | inherited {target : LTerm}
      (event : SelectedOldTurn F source degree pre middle target site)
      (lookup : target.subterm edge=some current) (oldLookup : middle.subterm oldEdge=some old)
      (origin : BetaNodePreimage event.body event.argument site edge oldEdge)
      (uncreated : ¬BetaCreatedIncoming event.body site edge) (same : current.label=old.label)
      (earlier : DirectedMarkerSpine F source degree forward pre middle beforeLabels oldEdge)
      {leaf : DirectedMarkerLeafOutput F source degree forward pre (old.label.readLetters forward)}
      {oldSnapshot : IncomingIncidenceSnapshot middle oldEdge}
      (earlierGeometry : SpineIncidenceProvenance F source degree forward earlier oldLookup leaf oldSnapshot)
      (snapshot : IncomingIncidenceSnapshot target edge)
      (transport : IncomingIncidenceTransport (body:=event.body) (argument:=event.argument) (site:=site) snapshot oldSnapshot) :
      SpineIncidenceProvenance F source degree forward
        (.inherited event lookup oldLookup origin uncreated same earlier) lookup
        ((leaf.reword (congrArg (Label.readLetters forward) same.symm)).snoc site) snapshot
  | safe {target : LTerm}
      (event : SelectedOldTurn F source degree pre middle target site)
      (reading : PrerequisiteReadsDirected target reader edge forward)
      (lookup : target.subterm edge=some current)
      (origin : BetaIncomingReadingOrigin event.body event.argument site edge reader oldMiddle first last)
      (segment : PrerequisitePrefix middle oldStart oldBefore oldMiddle)
      (beforeEq : beforeLabels=oldBefore.map middle.labelAt)
      (beforeSafe : ∀e∈oldBefore,∀node,middle.subterm e=some node →node.label.OuterBarsSafe (fun x=>x≠degree))
      (firstLookup : middle.subterm first=some firstNode)
      (firstSafe : firstNode.label.OuterBarsSafe (fun x=>x≠degree))
      (lastLookup : middle.subterm last=some lastNode)
      (lastSourceLookup : source.subterm lastSourcePosition=some lastSourceNode)
      (lastTrace : BetaNodeHistoryPreimage event.labels last lastSourcePosition)
      (marks : marker.MarksDegree degree)
      (formula : ExactDirectedReadingFormula middle site degree forward firstNode lastNode marker current)
      (snapshot : IncomingIncidenceSnapshot target edge)
      (firstSnapshot : IncomingIncidenceSnapshot middle first)
      (frame : CreatedSpineIncidenceFrame event.body event.argument site middle target first last oldMiddle forward snapshot firstSnapshot) :
      SpineIncidenceProvenance F source degree forward
        (.safe event reading lookup origin segment beforeEq beforeSafe firstLookup firstSafe lastLookup lastSourceLookup lastTrace) lookup
        (safe_leaf event reading origin lookup firstLookup firstSafe lastLookup lastSourceLookup lastTrace marks formula) snapshot
  | marked {target : LTerm}
      (event : SelectedOldTurn F source degree pre middle target site)
      (reading : PrerequisiteReadsDirected target reader edge forward)
      (lookup : target.subterm edge=some current)
      (origin : BetaIncomingReadingOrigin event.body event.argument site edge reader oldMiddle first last)
      (segment : PrerequisitePrefix middle oldStart oldBefore oldMiddle)
      (beforeEq : beforeLabels=oldBefore.map middle.labelAt)
      (beforeSafe : ∀e∈oldBefore,∀node,middle.subterm e=some node →node.label.OuterBarsSafe (fun x=>x≠degree))
      (firstLookup : middle.subterm first=some firstNode)
      (firstMarked : ¬firstNode.label.OuterBarsSafe (fun x=>x≠degree))
      (lastLookup : middle.subterm last=some lastNode)
      (lastSourceLookup : source.subterm lastSourcePosition=some lastSourceNode)
      (lastTrace : BetaNodeHistoryPreimage event.labels last lastSourcePosition)
      (earlier : DirectedMarkerSpine F source degree forward pre middle beforeLabels first)
      {leaf : DirectedMarkerLeafOutput F source degree forward pre (firstNode.label.readLetters forward)}
      {firstSnapshot : IncomingIncidenceSnapshot middle first}
      (earlierGeometry : SpineIncidenceProvenance F source degree forward earlier firstLookup leaf firstSnapshot)
      (marks : marker.MarksDegree degree)
      (formula : ExactDirectedReadingFormula middle site degree forward firstNode lastNode marker current)
      (equation : current.label.readLetters forward=firstNode.label.readLetters forward++marker::rest)
      (snapshot : IncomingIncidenceSnapshot target edge)
      (frame : CreatedSpineIncidenceFrame event.body event.argument site middle target first last oldMiddle forward snapshot firstSnapshot) :
      SpineIncidenceProvenance F source degree forward
        (.marked event reading lookup origin segment beforeEq beforeSafe firstLookup firstMarked lastLookup lastSourceLookup lastTrace earlier) lookup
        (((leaf.extend (marker::rest)).reword equation.symm).snoc site) snapshot

/-- ONE finite induction on the GIVEN actual spine; no OLD strong recursion,
earliest rerun, intermediate Matches, or caller-supplied geometry. -/
theorem DirectedMarkerSpine.incidence_leaf_output
    (spine : DirectedMarkerSpine F source degree forward ps target beforeLabels edge)
    (closed : Closed source.erase) (currentLookup : target.subterm edge=some current) :
    ∃leaf : DirectedMarkerLeafOutput F source degree forward ps (current.label.readLetters forward),
      ∃snapshot : IncomingIncidenceSnapshot target edge,
        Nonempty (SpineIncidenceProvenance F source degree forward spine currentLookup leaf snapshot) := by
  induction spine generalizing current with
  | inherited event lookup oldLookup origin uncreated same earlier ih =>
    have equal:=Option.some.inj (lookup.symm.trans currentLookup)
    cases equal
    obtain ⟨leaf,oldSnapshot,⟨earlierGeometry⟩⟩:=ih oldLookup
    have middleClosed:=event.labels.closed closed
    have targetClosed:=(History.cons event.turn (History.nil _)).closed middleClosed
    obtain ⟨snapshot⟩:=snapshot_exists targetClosed lookup
    obtain ⟨transport⟩:=snapshot_transport event.turn event.redex origin lookup uncreated snapshot oldSnapshot
    exact ⟨_,snapshot,⟨.inherited event lookup oldLookup origin uncreated same earlier earlierGeometry snapshot transport⟩⟩
  | safe event reading lookup origin segment beforeEq beforeSafe firstLookup firstSafe lastLookup lastSourceLookup lastTrace =>
    have equal:=Option.some.inj (lookup.symm.trans currentLookup)
    cases equal
    have middleClosed:=event.labels.closed closed
    have targetClosed:=(History.cons event.turn (History.nil _)).closed middleClosed
    obtain ⟨snapshot⟩:=snapshot_exists targetClosed lookup
    obtain ⟨firstSnapshot⟩:=snapshot_exists middleClosed firstLookup
    obtain ⟨frame⟩:=make_frame event.turn event.redex origin reading lookup snapshot firstSnapshot
    obtain ⟨firstNode,lastNode,marker,firstAt,lastAt,marks,formula⟩:=origin.directed_label_decomposition event.turn event.redex reading lookup
    have firstEq:=Option.some.inj (firstAt.symm.trans firstLookup)
    have lastEq:=Option.some.inj (lastAt.symm.trans lastLookup)
    subst firstNode;subst lastNode
    exact ⟨_,snapshot,⟨.safe event reading lookup origin segment beforeEq beforeSafe firstLookup firstSafe lastLookup lastSourceLookup lastTrace marks formula snapshot firstSnapshot frame⟩⟩
  | marked event reading lookup origin segment beforeEq beforeSafe firstLookup firstMarked lastLookup lastSourceLookup lastTrace earlier ih =>
    have equal:=Option.some.inj (lookup.symm.trans currentLookup)
    cases equal
    obtain ⟨leaf,firstSnapshot,⟨earlierGeometry⟩⟩:=ih firstLookup
    have middleClosed:=event.labels.closed closed
    have targetClosed:=(History.cons event.turn (History.nil _)).closed middleClosed
    obtain ⟨snapshot⟩:=snapshot_exists targetClosed lookup
    obtain ⟨frame⟩:=make_frame event.turn event.redex origin reading lookup snapshot firstSnapshot
    obtain ⟨firstNode,lastNode,marker,firstAt,lastAt,marks,formula⟩:=origin.directed_label_decomposition event.turn event.redex reading lookup
    have firstEq:=Option.some.inj (firstAt.symm.trans firstLookup)
    have lastEq:=Option.some.inj (lastAt.symm.trans lastLookup)
    subst firstNode;subst lastNode
    obtain ⟨rest,equation⟩:=formula_prefix formula
    exact ⟨_,snapshot,⟨.marked event reading lookup origin segment beforeEq beforeSafe firstLookup firstMarked lastLookup lastSourceLookup lastTrace earlier earlierGeometry marks formula equation snapshot frame⟩⟩

#print axioms DirectedMarkerSpine.incidence_leaf_output

/-- An ordered expansion packet retains its actual selected turn and the
literal finite chase; it asserts no physical path through a rewrite. -/
structure SpineCreationPacket (F : List Path) (source : LTerm) (degree : Label) (forward : Bool) where
  pre : List Path
  middle : LTerm
  target : LTerm
  site : Path
  event : SelectedOldTurn F source degree pre middle target site
  edge : Path
  reader : Path
  oldReader : Path
  first : Path
  last : Path
  current : LTerm
  lookup : target.subterm edge=some current
  reading : PrerequisiteReadsDirected target reader edge forward
  origin : BetaIncomingReadingOrigin event.body event.argument site edge reader oldReader first last
  snapshot : IncomingIncidenceSnapshot target edge
  firstSnapshot : IncomingIncidenceSnapshot middle first
  frame : CreatedSpineIncidenceFrame event.body event.argument site middle target first last oldReader forward snapshot firstSnapshot

private def pack_frame
    (event : SelectedOldTurn F source degree pre middle target site)
    (reading : PrerequisiteReadsDirected target reader edge forward)
    (origin : BetaIncomingReadingOrigin event.body event.argument site edge reader oldReader first last)
    (lookup : target.subterm edge=some current)
    (snapshot : IncomingIncidenceSnapshot target edge)
    (firstSnapshot : IncomingIncidenceSnapshot middle first)
    (frame : CreatedSpineIncidenceFrame event.body event.argument site middle target first last oldReader forward snapshot firstSnapshot) :
    SpineCreationPacket F source degree forward :=
  ⟨pre,middle,target,site,event,edge,reader,oldReader,first,last,current,lookup,reading,origin,snapshot,firstSnapshot,frame⟩

namespace SpineIncidenceProvenance
variable {F : List Path} {source : LTerm} {degree : Label} {forward : Bool}
variable {ps : List Path} {target current : LTerm} {beforeLabels : List (Option Label)} {edge : Path}
variable {spine : DirectedMarkerSpine F source degree forward ps target beforeLabels edge}
variable {lookup : target.subterm edge=some current}
variable {leaf : DirectedMarkerLeafOutput F source degree forward ps (current.label.readLetters forward)}
variable {snapshot : IncomingIncidenceSnapshot target edge}

private def event_site (_event : SelectedOldTurn F source degree pre middle target site) : Path:=site
private def word_piece {current firstNode : LTerm}
    (_equation : current.label.readLetters forward=firstNode.label.readLetters forward++marker::rest) : List Letter:=marker::rest

/-- Chronological creation packets, including the safe base event.
Proof-indexed extraction is noncomputable; no runtime algorithm is asserted. -/
noncomputable def creationFrames (geometry : SpineIncidenceProvenance F source degree forward spine lookup leaf snapshot) :
    List (SpineCreationPacket F source degree forward) := by
  induction geometry with
  | inherited _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | safe event reading lookup origin _ _ _ _ _ _ _ _ _ _ snap firstSnap frame =>
    exact [pack_frame event reading origin lookup snap firstSnap frame]
  | marked event reading lookup origin _ _ _ _ _ _ _ _ _ _ _ _ _ snap frame ih =>
    exact ih++[pack_frame event reading origin lookup snap _ frame]

/-- Every enclosing turn extends the schedule after the SAME base leaf. -/
noncomputable def afterSites (geometry : SpineIncidenceProvenance F source degree forward spine lookup leaf snapshot) : List Path := by
  induction geometry with
  | inherited event _ _ _ _ _ _ _ _ _ ih => exact ih++[event_site event]
  | safe => exact []
  | marked event _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih++[event_site event]

/-- Only marked descent adds literal continuation pieces. Inherited
schedule turns do not add letters. -/
noncomputable def continuationPieces (geometry : SpineIncidenceProvenance F source degree forward spine lookup leaf snapshot) : List (List Letter) := by
  induction geometry with
  | inherited _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | safe => exact []
  | marked _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ equation _ _ ih =>
    exact ih++[word_piece equation]

theorem afterSites_eq (geometry : SpineIncidenceProvenance F source degree forward spine lookup leaf snapshot) :
    geometry.afterSites=leaf.after := by
  induction geometry with
  | inherited _ _ _ _ _ _ _ _ _ _ ih =>
    simpa only [afterSites,DirectedMarkerLeafOutput.snoc,DirectedMarkerLeafOutput.reword] using congrArg (·++[_]) ih
  | safe => rfl
  | marked _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    simpa only [afterSites,DirectedMarkerLeafOutput.snoc,DirectedMarkerLeafOutput.reword,DirectedMarkerLeafOutput.extend] using congrArg (·++[_]) ih

theorem continuationPieces_eq (geometry : SpineIncidenceProvenance F source degree forward spine lookup leaf snapshot) :
    geometry.continuationPieces.flatten=leaf.continuation := by
  induction geometry with
  | inherited _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | safe => rfl
  | marked _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    simpa only [continuationPieces,List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil,
      DirectedMarkerLeafOutput.snoc,DirectedMarkerLeafOutput.reword,DirectedMarkerLeafOutput.extend] using congrArg (·++_) ih

/-- The chronological first frame is the SAME safe leaf's actual event and
literal coordinates, even after marked continuation and inherited turns. -/
theorem base_frame_coordinates (geometry : SpineIncidenceProvenance F source degree forward spine lookup leaf snapshot) :
    ∃packet tail,geometry.creationFrames=packet::tail ∧
      packet.pre=leaf.pre ∧packet.site=leaf.site ∧packet.edge=leaf.edge ∧
      packet.first=leaf.first ∧packet.last=leaf.last := by
  induction geometry with
  | inherited _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | safe => exact ⟨_,[],rfl,rfl,rfl,rfl,rfl,rfl⟩
  | marked event reading lookup origin _ _ _ _ _ _ _ _ _ _ _ _ _ snap frame ih =>
    obtain ⟨packet,tail,split,preEq,siteEq,edgeEq,firstEq,lastEq⟩:=ih
    let next:=pack_frame event reading origin lookup snap _ frame
    refine ⟨packet,tail++[next],?_,preEq,siteEq,edgeEq,firstEq,lastEq⟩
    exact (congrArg (fun xs=>xs++[next]) split).trans (by rfl)

end SpineIncidenceProvenance

/-- The given spine itself supplies the actual full schedule, with no
intermediate matching hypothesis. -/
theorem DirectedMarkerSpine.actual_history
    (spine : DirectedMarkerSpine F source degree forward ps target beforeLabels edge) :
    History ps source target := by
  cases spine with
  | inherited event => exact event.labels.append (.cons event.turn (.nil _))
  | safe event => exact event.labels.append (.cons event.turn (.nil _))
  | marked event => exact event.labels.append (.cons event.turn (.nil _))

/-- The schedule suffix is a real history starting at THIS same leaf target;
it is not identified with the literal word continuation. -/
theorem SpineIncidenceProvenance.actual_suffix
    {spine : DirectedMarkerSpine F source degree forward ps target beforeLabels edge}
    {lookup : target.subterm edge=some current}
    {leaf : DirectedMarkerLeafOutput F source degree forward ps (current.label.readLetters forward)}
    {snapshot : IncomingIncidenceSnapshot target edge}
    (_geometry : SpineIncidenceProvenance F source degree forward spine lookup leaf snapshot) :
    History leaf.after leaf.target target := by
  have history:=spine.actual_history
  rw [leaf.schedule] at history
  obtain ⟨middle,trailPrefix,remaining⟩:=history.split
  have same:=trailPrefix.deterministic leaf.event.labels
  subst middle
  cases remaining with
  | cons turn suffix =>
    have same:=(History.cons turn (History.nil _)).deterministic (.cons leaf.event.turn (.nil _))
    subst_vars
    exact suffix

#print axioms SpineIncidenceProvenance.afterSites_eq
#print axioms SpineIncidenceProvenance.continuationPieces_eq
#print axioms SpineIncidenceProvenance.actual_suffix
#print axioms SpineIncidenceProvenance.base_frame_coordinates
end Lamping.Lambda.Labelled
