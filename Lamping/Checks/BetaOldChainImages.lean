import Lamping.Lamping.BetaOldChainImages
import Lamping.Checks.UniformOldChainIncidencePreimages
namespace Lamping.Checks.BetaOldChainImages
open AG Graph Lambda Lambda.Labelled OldChainBetaFixture

/-- A real I(I I) beta presentation, two arbitrary physical selectors,
and a genuinely nonempty target chain consume the complete image theorem.
The global operational ancestry locks the SAME old ARG/FUNCTION chain. -/
theorem actual_ordered_physical_image
    (presentation : PhysicalCorridorPresentation net (.beta 0) app lam (.inl ()) (.inl ()))
    (sourceSelection : OccurrenceFragmentSelection initial presentation.site.net (.inl ()))
    (targetSelection : OccurrenceFragmentSelection result presentation.site.reduce (.inl ())) :
    ∃ edge : BetaEdge presentation.site.net,SiteBetaGeometry presentation.site edge ∧
      BetaAtomicBlockResiduals presentation.site edge (canonicalChainImage targetSelection targetChain)
        (canonicalChainImage sourceSelection oldChain) ∧
      ChainIncidenceIsomorphic (chainSyntaxIncidence result (history.closed closed) [[.fn]])
        (chainSyntaxIncidence initial closed [[.arg,.fn]]) := by
  have matching := presentation.sourceIso.matches (encode_closed_matches term closed 0)
  have inputs := presentation.sourceIso.rootInputs (encode_closed_independence term closed 0).rootInputs
  obtain ⟨originalFlow⟩ := encode_flowBalance term 0
  have flow := presentation.sourceIso.flowBalance originalFlow
  obtain ⟨originalBalance⟩ := encode_indexed_balance term 0
  have balance := presentation.sourceIso.indexed_balance originalBalance
  have transparency := presentation.sourceIso.transparency (encode_closed_transparency term closed 0)
  have selected (path : Path) (member : path∈([[]] : List Path)) :
      initial.degreeAt path=some (Labelled.Label.atom 1) := by
    have same := List.mem_singleton.mp member
    subst path;rfl
  obtain ⟨edge,geometry,images⟩ := presentation.site.beta_marker_free_chain_images (source:=initial) closed matching
    inputs flow rfl balance rfl transparency (relative presentation) (by simp [endpoint,Marked.Normal]) history
      complete.complete.1 (DegreeAligned.initial initial [[]]) selected sourceSelection targetSelection
  obtain ⟨oldStart,oldEdges,actualOld,startTrace,edgeTraces,incidence,blocks⟩ := images targetChain marker_free
  obtain ⟨knownStart,knownEdges,_knownIncidence⟩ := actual_same_ordered_incidence
  have sameStart := startTrace.unique knownStart
  have sameEdges := edgeTraces.unique knownEdges
  subst oldStart
  subst oldEdges
  exact ⟨edge,geometry,blocks,incidence⟩

/-- Initial representation is supplied by the actual encoding, not by an
oracle. The two real target chains start at different APP/lambda nodes and
read the same nonempty FUNCTION edge, as unpointed REP requires. -/
theorem actual_marker_free_pair
    (presentation : PhysicalCorridorPresentation net (.beta 0) app lam (.inl ()) (.inl ()))
    (targetSelection : OccurrenceFragmentSelection result presentation.site.reduce (.inl ())) :
    ∃ sourceSelection : OccurrenceFragmentSelection initial presentation.site.net (.inl ()),
      JointRepresentation (current:=initial) closed sourceSelection ∧
      (SameChainRepresentation targetSelection targetChain (PrerequisiteChain.redex_lam (t:=result) (p:=[]) rfl) ↔
        ChainIncidenceIsomorphic (chainSyntaxIncidence result (history.closed closed) [[.fn]])
          (chainSyntaxIncidence result (history.closed closed) [[.fn]])) := by
  have originalMatches : Matches net (.inl ()) initial.erase := encode_closed_matches term closed 0
  have matching := presentation.sourceIso.matches originalMatches
  obtain ⟨originalSelection,initialJoint⟩ := encode_initial_joint_realization initial closed (init_is_INIT term) 0
  obtain ⟨sourceSelection⟩ := matching.occurrence_fragment_selection closed
  have joint := (presentation.sourceIso.joint_representation originalMatches closed originalSelection sourceSelection).mpr initialJoint
  have inputs := presentation.sourceIso.rootInputs (encode_closed_independence term closed 0).rootInputs
  obtain ⟨originalFlow⟩ := encode_flowBalance term 0
  have flow := presentation.sourceIso.flowBalance originalFlow
  obtain ⟨originalBalance⟩ := encode_indexed_balance term 0
  have balance := presentation.sourceIso.indexed_balance originalBalance
  have transparency := presentation.sourceIso.transparency (encode_closed_transparency term closed 0)
  have selected (path : Path) (member : path∈([[]] : List Path)) :
      initial.degreeAt path=some (Labelled.Label.atom 1) := by
    have same := List.mem_singleton.mp member
    subst path;rfl
  refine ⟨sourceSelection,joint,?_⟩
  exact presentation.site.beta_marker_free_rep (source:=initial) closed matching inputs flow rfl balance rfl transparency
    (relative presentation) (by simp [endpoint,Marked.Normal]) history complete.complete.1
      (DegreeAligned.initial initial [[]]) selected sourceSelection targetSelection joint.1 targetChain
        (PrerequisiteChain.redex_lam (t:=result) (p:=[]) rfl) marker_free marker_free

/-- A fully closed witness: the real corridor supplies the presentation,
proved beta matching supplies a genuine target selector, and initial
representation supplies the source selector. No selector oracle is input. -/
theorem actual_nonempty_instance :
    ∃ presentation : PhysicalCorridorPresentation net (.beta 0) app lam (.inl ()) (.inl ()),
      ∃ sourceSelection : OccurrenceFragmentSelection initial presentation.site.net (.inl ()),
      ∃ targetSelection : OccurrenceFragmentSelection result presentation.site.reduce (.inl ()),
      ∃ edge : BetaEdge presentation.site.net,
        SiteBetaGeometry presentation.site edge ∧JointRepresentation (current:=initial) closed sourceSelection ∧
        BetaAtomicBlockResiduals presentation.site edge (canonicalChainImage targetSelection targetChain)
          (canonicalChainImage sourceSelection oldChain) ∧
        canonicalChainImage targetSelection targetChain≠[] ∧
        SameChainRepresentation targetSelection targetChain (PrerequisiteChain.redex_lam (t:=result) (p:=[]) rfl) := by
  obtain ⟨presentation⟩ := actual_presentation
  have matching : Matches presentation.site.net (.inl ()) initial.erase :=
    presentation.sourceIso.matches (encode_closed_matches term closed 0)
  have inputs := presentation.sourceIso.rootInputs (encode_closed_independence term closed 0).rootInputs
  obtain ⟨originalFlow⟩ := encode_flowBalance term 0
  have flow := presentation.sourceIso.flowBalance originalFlow
  obtain ⟨originalBalance⟩ := encode_indexed_balance term 0
  have balance := presentation.sourceIso.indexed_balance originalBalance
  have transparency := presentation.sourceIso.transparency (encode_closed_transparency term closed 0)
  have targetMatches := presentation.site.beta_complete_matches (init_is_INIT term) closed matching inputs flow rfl
    balance rfl transparency (relative presentation) (by simp [endpoint,Marked.Normal]) history
  obtain ⟨targetSelection⟩ := targetMatches.occurrence_fragment_selection (history.closed closed)
  obtain ⟨sourceSelection,joint,pair⟩ := actual_marker_free_pair presentation targetSelection
  obtain ⟨edge,geometry,blocks,_incidence⟩ := actual_ordered_physical_image presentation sourceSelection targetSelection
  exact ⟨presentation,sourceSelection,targetSelection,edge,geometry,joint,blocks,
    canonicalChainImage_nonempty targetSelection targetChain,pair.mpr ⟨ChainIncidenceIso.refl _⟩⟩

#print axioms PrerequisiteChain.reading_ne_nil
#print axioms BetaAtomicBlockResiduals.equality_iff
#print axioms PathSite.beta_marker_free_chain_images
#print axioms PathSite.beta_marker_free_rep
#print axioms actual_ordered_physical_image
#print axioms actual_marker_free_pair
#print axioms actual_nonempty_instance
end Lamping.Checks.BetaOldChainImages

