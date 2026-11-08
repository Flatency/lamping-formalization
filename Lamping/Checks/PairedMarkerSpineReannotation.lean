import Lamping.Lamping.PairedMarkerSpineReannotation
import Lamping.Checks.DirectedMarkerSpineIncidence
namespace Lamping.Checks.PairedMarkerSpineReannotationChecks
open Lambda Lambda.Labelled
open DirectedMarkerSpineIncidenceChecks

namespace Nested
open UniformOldNodeLabelSuffixChecks
open DirectedMarkerSpineIncidenceChecks.Nested

theorem forward_multiple_frames : ∃leaf snapshot,
    ∃g : SpineIncidenceProvenance family sourceWrapped (.atom 10) true forwardSpine
      (by rfl : targetForward.subterm [.fn]=some target) leaf snapshot,
      2≤g.creationFrames.length ∧leaf.after≠[] ∧leaf.continuation≠[] := by
  obtain ⟨leaf,snapshot,⟨g⟩,nonempty⟩:=forward_nonempty
  have multiple:=g.multiple_of_continuation nonempty
  exact ⟨leaf,snapshot,g,multiple,g.after_nonempty_of_multiple multiple,nonempty⟩

theorem reverse_multiple_frames : ∃leaf snapshot,
    ∃g : SpineIncidenceProvenance family sourceWrapped (.atom 10) false reverseSpine
      (by rfl : targetReverse.subterm [.fn]=some reverseResult) leaf snapshot,
      2≤g.creationFrames.length ∧leaf.after≠[] ∧leaf.continuation≠[] := by
  obtain ⟨leaf,snapshot,⟨g⟩,nonempty⟩:=reverse_nonempty
  have multiple:=g.multiple_of_continuation nonempty
  exact ⟨leaf,snapshot,g,multiple,g.after_nonempty_of_multiple multiple,nonempty⟩

theorem forward_reannotated : ∃leaf snapshot,
    ∃g : SpineIncidenceProvenance family sourceWrapped (.atom 10) true forwardSpine
      (by rfl : targetForward.subterm [.fn]=some target) leaf snapshot,
    ∃localTarget,∃localHistory : History [[.fn],[.fn]] (initLabels sourceWrapped.erase) localTarget,
    ∃pair : PairedSpineReannotation g localHistory (erase_initLabels sourceWrapped.erase).symm,
      2≤g.creationFrames.length ∧leaf.after≠[] ∧pair.localTailPieces≠[] ∧
      localTarget.subterm [.fn]=some pair.current ∧
      pair.current.label.readLetters true=pair.base.current.label.readLetters true++pair.localTailPieces.flatten ∧
      pair.frames.map Sigma.fst=g.creationFrames ∧pair.localTailPieces.length+1=g.creationFrames.length := by
  obtain ⟨leaf,snapshot,g,multiple,after,_⟩:=forward_multiple_frames
  obtain ⟨localTarget,history,_⟩:=lift_history labelsForward.betaHistory (initLabels sourceWrapped.erase) (erase_initLabels _)
  obtain ⟨pair⟩:=g.paired_reannotation history (erase_initLabels _).symm
  exact ⟨leaf,snapshot,g,localTarget,history,pair,multiple,after,pair.tails_nonempty multiple,
    pair.currentLookup,pair.wordFold,pair.frameAlignment,pair.tail_count⟩

theorem reverse_reannotated : ∃leaf snapshot,
    ∃g : SpineIncidenceProvenance family sourceWrapped (.atom 10) false reverseSpine
      (by rfl : targetReverse.subterm [.fn]=some reverseResult) leaf snapshot,
    ∃localTarget,∃localHistory : History [[.fn,.arg],[.fn]] (initLabels sourceWrapped.erase) localTarget,
    ∃pair : PairedSpineReannotation g localHistory (erase_initLabels sourceWrapped.erase).symm,
      2≤g.creationFrames.length ∧leaf.after≠[] ∧pair.localTailPieces≠[] ∧
      localTarget.subterm [.fn]=some pair.current ∧
      pair.current.label.readLetters false=pair.base.current.label.readLetters false++pair.localTailPieces.flatten ∧
      pair.frames.map Sigma.fst=g.creationFrames ∧pair.localTailPieces.length+1=g.creationFrames.length := by
  obtain ⟨leaf,snapshot,g,multiple,after,_⟩:=reverse_multiple_frames
  obtain ⟨localTarget,history,_⟩:=lift_history labelsReverse.betaHistory (initLabels sourceWrapped.erase) (erase_initLabels _)
  obtain ⟨pair⟩:=g.paired_reannotation history (erase_initLabels _).symm
  exact ⟨leaf,snapshot,g,localTarget,history,pair,multiple,after,pair.tails_nonempty multiple,
    pair.currentLookup,pair.wordFold,pair.frameAlignment,pair.tail_count⟩
end Nested

namespace DistinctInherited
open PairedCurrentChainSourceLabelsChecks.NoninitialDistinct
open DirectedMarkerSpineIncidenceChecks.DistinctInherited

private theorem actual_snapshot (closed : Closed t.erase) (lookup : t.subterm edge=some node) :
    Nonempty (IncomingIncidenceSnapshot t edge) := by
  let actual : SyntaxIncidence.Edge t:=⟨edge,by rw [←LTerm.erase_subterm,lookup];rfl⟩
  obtain ⟨fromVertex,fromSpec⟩:=SyntaxIncidence.source_total t actual
  obtain ⟨toVertex,toSpec⟩:=SyntaxIncidence.target_total t closed actual
  exact ⟨⟨fromVertex,toVertex,fromSpec,toSpec⟩⟩

private theorem actual_transport
    (step : StepAt site middle target)
    (redex : middle.subterm site=some (.app beta (.lam alpha body) arg))
    (origin : BetaNodePreimage body arg site edge oldEdge)
    (lookup : target.subterm edge=some node) (uncreated : ¬BetaCreatedIncoming body site edge)
    (snap : IncomingIncidenceSnapshot target edge) (oldSnap : IncomingIncidenceSnapshot middle oldEdge) :
    Nonempty (IncomingIncidenceTransport (body:=body) (argument:=arg) (site:=site) snap oldSnap) := by
  obtain ⟨fromVertex,fromSpec,fromOrigin⟩:=step.beta_incidence_source_preimage redex origin lookup uncreated snap.fromSpec
  obtain ⟨toVertex,toSpec,toOrigin⟩:=step.beta_incidence_target_preimage redex origin snap.toSpec
  have fromEq:=SyntaxIncidence.Source.unique fromSpec oldSnap.fromSpec
  have toEq:=SyntaxIncidence.Target.unique toSpec oldSnap.toSpec
  rw [fromEq] at fromOrigin
  rw [toEq] at toOrigin
  exact ⟨⟨fromOrigin,toOrigin⟩⟩

def actual_origin : BetaNodePreimage lastEvent.body lastEvent.argument [.arg] leftStart leftStart :=
  .context (by rintro ⟨relative,impossible⟩;cases impossible)

theorem actual_reannotated_inheritance : ∃leaf snapshot,
    ∃g : SpineIncidenceProvenance F source (.atom 6) false inheritedSpine
      (by rfl : current.subterm leftStart=some newArgument) leaf snapshot,
    ∃localTarget,∃localHistory : History [[.fn],[.arg]] (initLabels source.erase) localTarget,
    ∃pair : PairedSpineReannotation g localHistory (erase_initLabels source.erase).symm,
      pair.inherited≠[] ∧pair.inherited.map Sigma.fst=g.inheritedSteps ∧
      localTarget.subterm leftStart=some pair.current ∧
      pair.current.label.readLetters false=pair.base.current.label.readLetters false++pair.localTailPieces.flatten := by
  obtain ⟨oldLeaf,oldSnapshot,⟨oldGeometry⟩⟩:=earlier.incidence_leaf_output sourceClosed rfl
  obtain ⟨snapshot⟩:=actual_snapshot (labels.closed sourceClosed)
    (by rfl : current.subterm leftStart=some newArgument)
  obtain ⟨transport⟩:=actual_transport secondStep lastEvent.redex actual_origin
    (by rfl : current.subterm leftStart=some newArgument) (by decide) snapshot oldSnapshot
  let g:=SpineIncidenceProvenance.inherited lastEvent rfl rfl actual_origin (by decide) rfl earlier oldGeometry snapshot transport
  obtain ⟨localTarget,history,_⟩:=lift_history labels.betaHistory (initLabels source.erase) (erase_initLabels _)
  obtain ⟨pair⟩:=g.paired_reannotation history (erase_initLabels _).symm
  have stepsNonempty : g.inheritedSteps≠[] := by simp [g,SpineIncidenceProvenance.inheritedSteps]
  have nonempty : pair.inherited≠[] := by
    intro empty
    apply stepsNonempty
    rw [←pair.inheritedAlignment,empty,List.map_nil]
  exact ⟨_,snapshot,g,localTarget,history,pair,nonempty,pair.inheritedAlignment,pair.currentLookup,pair.wordFold⟩
end DistinctInherited

#print axioms SpineReannotation.vertex_origin
#print axioms SpineReannotation.chase
#print axioms SpineReannotation.expansion
#print axioms SpineReannotation.snapshot
#print axioms SpineIncidenceProvenance.continuation_count
#print axioms SpineIncidenceProvenance.schedule_count
#print axioms DirectedMarkerSpineIncidenceChecks.Nested.same_original_different_schedules
#print axioms SpineReannotation.source_reannotate
#print axioms SpineReannotation.target_reannotate
#print axioms SpineReannotation.frame
#print axioms paired_spine_creation_frame
#print axioms paired_spine_inherited_event
#print axioms SpineIncidenceProvenance.paired_reannotation
#print axioms PairedSpineReannotation.tail_count
#print axioms Nested.forward_multiple_frames
#print axioms Nested.reverse_multiple_frames
#print axioms Nested.forward_reannotated
#print axioms Nested.reverse_reannotated
#print axioms DistinctInherited.actual_reannotated_inheritance
end Lamping.Checks.PairedMarkerSpineReannotationChecks
