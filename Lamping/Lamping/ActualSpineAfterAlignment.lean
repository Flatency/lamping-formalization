import Lamping.Lamping.DirectedMarkerSpineIncidence
import Lamping.Lamping.ActualCurrentAfterChains
import Lamping.Lamping.AuxiliaryEndpointAvailability

namespace Lamping.Lambda.Labelled
open SyntaxIncidence
variable {source target : LTerm}

/-- An actual nonempty AFTER starts at the far incidence of THIS reading.
The successful chain is supplied by inversion, not by completing a walk. -/
theorem PrerequisiteChain.after_snapshot
    (chain : PrerequisiteChain target reader (edge::after))
    (reading : PrerequisiteReadsDirected target reader edge forward)
    (more : after≠[]) (snapshot : IncomingIncidenceSnapshot target edge) :
    ∃ next, ActualAfterStart target reader edge next ∧
      Target target next (snapshot.far forward) ∧
      AG.EndpointChain target (snapshot.far forward) after := by
  obtain ⟨next,shape,tail⟩ := chain.after_of_read reading.1 more
  have actual : Target target next (snapshot.far forward) := by
    cases forward with
    | true =>
      rcases shape with ⟨_,_,_,_,_,same⟩ | ⟨parent,child,_,_,readerEq,_,_,edgeEq,_⟩
      · simpa only [same,IncomingIncidenceSnapshot.far,if_true] using snapshot.toSpec
      · have sizes := congrArg List.length (reading.2.symm.trans edgeEq)
        simp at sizes
    | false =>
      rcases shape with ⟨_,_,_,_,edgeEq,_⟩ | ⟨parent,child,stamp,body,readerEq,_,lookup,edgeEq,nextEq⟩
      · have sizes := congrArg List.length (edgeEq.symm.trans reading.2)
        simp at sizes
      · change Target target next snapshot.fromVertex
        cases fromEq : snapshot.fromVertex with
        | none =>
          have empty : edge=[] := by simpa only [fromEq] using snapshot.fromSpec
          have sizes := congrArg List.length (empty.symm.trans (edgeEq.trans readerEq))
          simp at sizes
        | some vertex =>
          obtain ⟨step,sub,port,split,_,_⟩ := (show Source target edge (some vertex) from by simpa only [fromEq] using snapshot.fromSpec)
          have equal : vertex.val++[step]=parent++[child] := split.symm.trans (edgeEq.trans readerEq)
          have lengths := congrArg List.length equal
          simp only [List.length_append,List.length_singleton] at lengths
          have same : vertex.val=parent := List.append_inj_left equal (by omega)
          exact Or.inl (nextEq.trans same.symm)
  refine ⟨next,shape,actual,?_⟩
  cases farEq : snapshot.far forward with
  | none => simp only [farEq,Target] at actual
  | some vertex =>
    have converted := tail.at_actual_target (by simpa only [farEq] using actual)
    simpa only [AG.EndpointChain,farEq] using converted

/-- The real old FIRST reading has the actual selected singleton after it.
Zero-edge lexical jumps are compressed using their genuine Target proof. -/
theorem BetaIncomingReadingOrigin.first_far_singleton
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (origin : BetaIncomingReadingOrigin body argument site edge reader oldReader first last)
    (reading : PrerequisiteReadsDirected target reader edge forward)
    (snapshot : IncomingIncidenceSnapshot source first) :
    AG.EndpointChain source (snapshot.far forward) [site++[.fn]] := by
  obtain ⟨oldReaderAt,jump,oldReading⟩ := origin.old_directed_reading redex reading
  have proper : ProperAt source oldReaderAt := by
    rcases oldReading.1 with ⟨stamp,fn,arg,lookup,_⟩ | ⟨stamp,body,lookup,_⟩
    · exact Or.inl ⟨stamp,fn,arg,lookup⟩
    · exact Or.inr ⟨stamp,body,lookup⟩
  let vertex : ProperPosition source := ⟨oldReaderAt,proper⟩
  have toReader : Target source oldReaderAt (some vertex) := Or.inl rfl
  have atOldReader : Target source oldReader (some vertex) := jump.target_of_no_edges rfl toReader
  have whole := (origin.old_prerequisite redex).1.at_actual_target atOldReader
  have actual : PrerequisiteChain source oldReaderAt [first,site++[.fn]] := whole
  exact (actual.after_snapshot oldReading (by simp) snapshot).choose_spec.2.2

private theorem IncomingIncidenceTransport.far_origin
    (transport : IncomingIncidenceTransport (body:=body) (argument:=argument) (site:=site) currentSnapshot oldSnapshot)
    (forward : Bool) :
    BetaVertexPreimage body argument site _ _ (currentSnapshot.far forward) (oldSnapshot.far forward) := by
  cases forward with
  | true => exact transport.toOrigin
  | false => exact transport.fromOrigin

private def IncomingIncidenceTransport.oldFar
    {currentSnapshot : IncomingIncidenceSnapshot target edge}
    {oldSnapshot : IncomingIncidenceSnapshot source oldEdge}
    (_transport : IncomingIncidenceTransport (body:=body) (argument:=argument) (site:=site) currentSnapshot oldSnapshot)
    (forward : Bool) : Vertex source := oldSnapshot.far forward

private def frameFirstFar
    (_frame : CreatedSpineIncidenceFrame body argument site middle target first last oldReader forward snapshot firstSnapshot) :
    Vertex middle := firstSnapshot.far forward

private def selectedFunction (_event : SelectedOldTurn F source degree pre middle target site) : Path := site++[.fn]

namespace SpineIncidenceProvenance
variable {F : List Path} {source : LTerm} {degree : Label} {forward : Bool}
variable {ps : List Path} {target current : LTerm} {beforeLabels : List (Option Label)} {edge : Path}
variable {spine : DirectedMarkerSpine F source degree forward ps target beforeLabels edge}
variable {lookup : target.subterm edge=some current}
variable {leaf : DirectedMarkerLeafOutput F source degree forward ps (current.label.readLetters forward)}
variable {snapshot : IncomingIncidenceSnapshot target edge}

/-- Actual successful chains indexed by the EXACT given provenance.
The marked expanded FAR and FIRST far remain separate vertices and lists. -/
noncomputable def SpineFarAlignment
    (geometry : SpineIncidenceProvenance F source degree forward spine lookup leaf snapshot) : List Path → Prop := by
  induction geometry with
  | inherited event _ _ _ _ _ _ _ snap transport ih =>
    exact fun edges => AG.EndpointChain _ (snap.far forward) edges ∧
      ∃oldEdges, AG.EndpointChain _ (transport.oldFar forward) oldEdges ∧ ih oldEdges
  | safe event reading lookup origin _ _ _ _ _ _ _ _ _ _ snap firstSnap frame =>
    exact fun edges => AG.EndpointChain _ (snap.far forward) edges ∧
      (∃oldEdges,AG.EndpointChain _ frame.oldFar oldEdges) ∧
      AG.EndpointChain _ (firstSnap.far forward) [selectedFunction event]
  | marked event reading lookup origin _ _ _ _ _ _ _ _ _ _ _ _ _ snap frame ih =>
    exact fun edges => AG.EndpointChain _ (snap.far forward) edges ∧
      (∃oldEdges,AG.EndpointChain _ frame.oldFar oldEdges) ∧
      AG.EndpointChain _ (frameFirstFar frame) [selectedFunction event] ∧ ih [selectedFunction event]

theorem align_successful_far
    (geometry : SpineIncidenceProvenance F source degree forward spine lookup leaf snapshot)
    (chain : AG.EndpointChain target (snapshot.far forward) edges) :
    geometry.SpineFarAlignment edges := by
  induction geometry generalizing edges with
  | inherited event lookup oldLookup origin uncreated same earlier earlierGeometry snap transport ih =>
    obtain ⟨oldEdges,oldChain⟩ := AG.endpoint_available_at_beta_preimage event.turn event.redex (transport.far_origin forward) chain
    exact ⟨chain,oldEdges,oldChain,ih oldChain⟩
  | safe event reading lookup origin _ _ _ _ _ _ _ _ _ _ snap firstSnap frame =>
    obtain ⟨oldEdges,oldChain⟩ := AG.endpoint_available_at_beta_preimage event.turn event.redex frame.farOrigin chain
    exact ⟨chain,⟨oldEdges,oldChain⟩,origin.first_far_singleton event.redex reading firstSnap⟩
  | marked event reading lookup origin _ _ _ _ _ _ _ _ _ _ _ _ _ snap frame ih =>
    obtain ⟨oldEdges,oldChain⟩ := AG.endpoint_available_at_beta_preimage event.turn event.redex frame.farOrigin chain
    have singleton : AG.EndpointChain _ (frameFirstFar frame) [selectedFunction event] :=
      origin.first_far_singleton event.redex reading _
    exact ⟨chain,⟨oldEdges,oldChain⟩,singleton,ih singleton⟩

end SpineIncidenceProvenance
end Lamping.Lambda.Labelled

namespace Lamping.AG
open Lambda Lambda.Labelled SyntaxIncidence
variable {source current : LTerm}
theorem ActualUnsafeMarkerCut.align_after_snapshot
    (cut : ActualUnsafeMarkerCut F ps source current degree start edges)
    (more : cut.after≠[]) (snapshot : IncomingIncidenceSnapshot current cut.edge) :
    ∃ next,ActualAfterStart current cut.reader cut.edge next ∧
      Target current next (snapshot.far cut.forward) ∧
      EndpointChain current (snapshot.far cut.forward) cut.after ∧cut.after.length<edges.length := by
  obtain ⟨next,shape,targetAt,chain⟩ := cut.remaining.after_snapshot cut.reading more snapshot
  exact ⟨next,shape,targetAt,chain,cut.after_length_lt⟩

theorem ActualUnsafeMarkerCut.spine_after_alignment
    (cut : ActualUnsafeMarkerCut F ps source current degree start edges)
    (more : cut.after≠[])
    {leaf : DirectedMarkerLeafOutput F source degree cut.forward ps (cut.node.label.readLetters cut.forward)}
    {snapshot : IncomingIncidenceSnapshot current cut.edge}
    (geometry : SpineIncidenceProvenance F source degree cut.forward cut.spine cut.lookup leaf snapshot) :
    ∃ next,ActualAfterStart current cut.reader cut.edge next ∧
      Target current next (snapshot.far cut.forward) ∧
      EndpointChain current (snapshot.far cut.forward) cut.after ∧
      cut.after.length<edges.length ∧geometry.SpineFarAlignment cut.after := by
  obtain ⟨next,shape,targetAt,chain,length⟩ := cut.align_after_snapshot more snapshot
  exact ⟨next,shape,targetAt,chain,length,geometry.align_successful_far chain⟩
end Lamping.AG

