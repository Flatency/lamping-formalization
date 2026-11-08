import Lamping.Lamping.InheritedForwardBetaPieces
import Lamping.Checks.DirectedMarkerSpineIncidence

namespace Lamping.Checks.InheritedForwardHeadsChecks
open Graph Lambda Lambda.Labelled AG
open PairedCurrentChainSourceLabelsChecks.NoninitialDistinct
open DirectedMarkerSpineIncidenceChecks.DistinctInherited

private theorem frame_bound
    {spine : DirectedMarkerSpine F source degree forward ps target before edge}
    {lookup : target.subterm edge=some node}
    {leaf : DirectedMarkerLeafOutput F source degree forward ps (node.label.readLetters forward)}
    {snapshot : IncomingIncidenceSnapshot target edge}
    (geometry : SpineIncidenceProvenance F source degree forward spine lookup leaf snapshot) :
    geometry.creationFrames.length≤ps.length := by
  induction geometry with
  | inherited => simp_all only [SpineIncidenceProvenance.creationFrames,List.length_append,List.length_singleton];omega
  | safe => simp only [SpineIncidenceProvenance.creationFrames,List.length_cons,List.length_nil,List.length_append];omega
  | marked => simp_all only [SpineIncidenceProvenance.creationFrames,List.length_append,List.length_singleton];omega

abbrev createdFunction : LTerm := WrappedSuccessfulChains.contractRoot left

def firstEvent : SelectedOldTurn F source (.atom 6) [] source middle [.fn] where
  markedBefore := Marked.mark F source.erase
  markedAfter := markedBeforeLast
  beforeOld := .nil _
  reduction := .appL (.redRoot _ _ _)
  member := by decide
  labels := .nil _
  turn := firstStep
  beta := left.label
  body := body
  argument := argument
  redex := rfl

def firstSpine : DirectedMarkerSpine F source (.atom 6) true [[.fn]] middle [] [.fn] :=
  .safe firstEvent
    (show PrerequisiteReadsDirected middle [] [.fn] true from ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩)
    (by rfl : middle.subterm [.fn]=some createdFunction)
    (.resultFunction rfl rfl)
    (oldStart:=[]) (oldBefore:=[]) .refl rfl (by intro e h;cases h)
    (by rfl : source.subterm [.fn]=some left)
    ((LTerm.outerBarsSafe_iff _ _).mp sourceSafe _ (LTerm.label_mem_of_subterm (by rfl : source.subterm [.fn]=some left)))
    (by rfl : source.subterm [.fn,.fn,.body]=some body)
    (by rfl : source.subterm [.fn,.fn,.body]=some body) (.nil _ _)

def finalSpine : DirectedMarkerSpine F source (.atom 6) true [[.fn],[.arg]] current [] [.fn] :=
  .inherited lastEvent
    (by rfl : current.subterm [.fn]=some createdFunction)
    (by rfl : middle.subterm [.fn]=some createdFunction)
    (.context (by rintro ⟨rest,eq⟩;cases eq)) (by decide) rfl firstSpine

/-- This is the SAME explicit inherited geometry, not an arbitrary output
with its single-frame fact asserted by a caller. -/
theorem actual_inherited_geometry : ∃leaf snapshot,
    ∃geometry : SpineIncidenceProvenance F source (.atom 6) true finalSpine
      (by rfl : current.subterm [.fn]=some createdFunction) leaf snapshot,
      geometry.creationFrames.length=1 ∧leaf.after≠[] ∧leaf.continuation=[] ∧
      UncreatedNodeHistoryPreimage geometry.actual_suffix [.fn] leaf.edge := by
  obtain ⟨leaf,oldSnapshot,⟨firstGeometry⟩⟩ := firstSpine.incidence_leaf_output sourceClosed
    (by rfl : middle.subterm [.fn]=some createdFunction)
  have upper := frame_bound firstGeometry
  obtain ⟨packet,rest,frames,_⟩ := firstGeometry.base_frame_coordinates
  have sizes := congrArg List.length frames
  have firstSingle : firstGeometry.creationFrames.length=1 := by
    simp only [List.length_cons] at sizes
    change firstGeometry.creationFrames.length≤1 at upper
    omega
  obtain ⟨_,snapshot,_⟩ := finalSpine.incidence_leaf_output sourceClosed
    (by rfl : current.subterm [.fn]=some createdFunction)
  have origin : BetaNodePreimage lastEvent.body lastEvent.argument [.arg] [.fn] [.fn] :=
    .context (by rintro ⟨rest,eq⟩;cases eq)
  have uncreated : ¬BetaCreatedIncoming lastEvent.body [.arg] [.fn] := by decide
  obtain ⟨oldFrom,fromSpec,fromOrigin⟩ := secondStep.beta_incidence_source_preimage
    lastEvent.redex origin (by rfl : current.subterm [.fn]=some createdFunction) uncreated snapshot.fromSpec
  obtain ⟨oldTo,toSpec,toOrigin⟩ := secondStep.beta_incidence_target_preimage lastEvent.redex origin snapshot.toSpec
  have fromEq := SyntaxIncidence.Source.unique fromSpec oldSnapshot.fromSpec
  have toEq := SyntaxIncidence.Target.unique toSpec oldSnapshot.toSpec
  rw [fromEq] at fromOrigin
  rw [toEq] at toOrigin
  let geometry := SpineIncidenceProvenance.inherited lastEvent
    (by rfl : current.subterm [.fn]=some createdFunction)
    (by rfl : middle.subterm [.fn]=some createdFunction) origin uncreated rfl
    firstSpine firstGeometry snapshot ⟨fromOrigin,toOrigin⟩
  have single : geometry.creationFrames.length=1 := by
    simpa only [geometry,SpineIncidenceProvenance.creationFrames] using firstSingle
  obtain ⟨continuation,trace⟩ := geometry.single_creation_suffix single
  refine ⟨_,snapshot,geometry,single,?_,continuation,trace⟩
  change leaf.after++[[.arg]]≠[]
  intro empty
  have size := congrArg List.length empty
  simp only [List.length_append,List.length_cons,List.length_nil] at size
  omega

theorem actual_noninitial_history : INIT original ∧¬INIT source ∧
    History [[],[.fn],[.arg]] original current ∧
    PrerequisiteChain current [] [[.fn],[.fn,.fn]] ∧
    current.subterm [.fn]=some createdFunction :=
  ⟨initial,sourceNotInit,prefixHistory.append labels,.app rfl (by intros;intro h;cases h) (.redex_app rfl),rfl⟩

/-- Direct complete physical consumer on this nonINIT/two-OLD/inherited
suffix fixture. A physical site realization and SOURCE REP remain honest
conditions; sameleaf selfpair is explicit, not distinct-chain Joint truth. -/
theorem actual_inherited_complete_pieces
    {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
    {kept : K→Graph.Label signature} {i : Nat}
    (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V)) {root : B}
    (matching : Matches site.net root source.erase) (inputs : RootInputs site.net root)
    {boundary : B→Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {heights : B→Int} (balance : IndexedLevelBalance site.net heights) (rootDepth : heights root=0)
    (transparency : Transparency site.net root)
    {endpoint : Marked}
    (relative : Marked.RelativeHistory [[.fn],[.arg]]
      (Marked.mark (site.betaSyntaxFiber root source.erase) source.erase) endpoint)
    (normal : Marked.Normal endpoint)
    (sourceSelection : OccurrenceFragmentSelection source site.net root)
    (representation : ChainRepresentationInvariant sourceClosed sourceSelection)
    (leftSelection rightSelection : OccurrenceFragmentSelection current site.reduce root) :
    ∃edge : BetaEdge site.net,SiteBetaGeometry site edge ∧∃block,
      block≠[] ∧
      BetaPathResidual site edge
        ((leftSelection ⟨[.fn],rfl⟩).fragment.segments.map (plugEnd _ _).invFun) block ∧
      BetaPathResidual site edge
        ((rightSelection ⟨[.fn],rfl⟩).fragment.segments.map (plugEnd _ _).invFun) block ∧
      (leftSelection ⟨[.fn],rfl⟩).fragment.segments=(rightSelection ⟨[.fn],rfl⟩).fragment.segments := by
  obtain ⟨leaf,snapshot,geometry,single,_nonempty,_continuation,_trace⟩ := actual_inherited_geometry
  obtain ⟨localTarget,_localHistory,edge,selection,siteGeometry,ln,rn,_leftLookup,_rightLookup,
      evaluations,nonempty,_rightNonempty,leftResidual,rightResidual,pieces⟩ :=
    site.beta_single_creation_forward_pieces sourceClosed matching inputs flow positive balance rootDepth transparency
      relative normal labels finalSpine finalSpine rfl rfl leaf leaf geometry geometry single single rfl rfl
      (show PrerequisiteReadsDirected current [] [.fn] true from ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩)
      (show PrerequisiteReadsDirected current [] [.fn] true from ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩)
      selected sourceSafe prefixHistory initial sourceSelection representation rfl
      (leftSelection ⟨[.fn],rfl⟩) (rightSelection ⟨[.fn],rfl⟩)
  exact ⟨edge,siteGeometry,selection.evalLabel edge ln.label,nonempty,
    leftResidual,evaluations ▸ rightResidual,pieces⟩

#print axioms actual_inherited_geometry
#print axioms actual_noninitial_history
#print axioms actual_inherited_complete_pieces
end Lamping.Checks.InheritedForwardHeadsChecks
