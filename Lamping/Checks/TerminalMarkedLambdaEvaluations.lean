import Lamping.Lamping.TerminalMarkedLambdaEvaluations
import Lamping.Checks.TerminalLambdaLastAtom

namespace Lamping.Checks.TerminalMarkedLambdaEvaluationsChecks
open Graph Lambda Lambda.Labelled AG

private theorem local_lambda_lookup
    {source current localTarget : LTerm}
    (labels : History ps source current)
    (localHistory : History ps (initLabels source.erase) localTarget)
    (lookup : current.subterm p=some (.lam stamp body)) :
    ∃localStamp localBody,localTarget.subterm p=some (.lam localStamp localBody) := by
  have same := SpineReannotation.history_erase labels localHistory (erase_initLabels source.erase).symm
  obtain ⟨node,atNode,erased⟩ := SpineReannotation.paired_lookup same lookup
  cases node with
  | var => cases erased
  | app => cases erased
  | lam a b => exact ⟨a,b,atNode⟩

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}

namespace RootOverlap
open DirectedReadingDecompositionChecks
open PairedCurrentChainSourceLabelsChecks.Terminal

theorem actual_complete_marked_q0
    (matching : Matches g root source.erase)
    (sourceSelection : OccurrenceFragmentSelection source g root)
    (sourceJoint : JointRepresentation closed sourceSelection)
    (selection : SourceEdgeSelection (initLabels source.erase) g root)
    (physical : BetaEdge g) :
    PrerequisiteChain target [] [[.fn]] ∧PrerequisiteChain target [.fn] [[.fn]] ∧
      result.label.readLetters true=[.atom 1,.over (.atom 2),.atom 3,.under (.atom 2),.atom 4] ∧
      result.label.readLetters false=[.atom 4,.under (.atom 2),.atom 3,.over (.atom 2),.atom 1] ∧
      selection.evalLabel physical result.label=selection.evalLabel physical result.label := by
  have marked : ¬result.label.OuterBarsSafe (fun x=>x≠Label.atom 2) :=
    step.created_label_not_safe (by rfl) (current:=result) rfl (Or.inl rfl)
  have value := terminal_marked_lambda_evaluations initial (.nil source) closed old history selected
    sourceSafe history (lp:=[]) (rp:=[]) (by rfl) (by rfl) rfl marked (by rfl) (by rfl)
    matching sourceSelection sourceJoint selection physical
  exact ⟨successful_function,successful_context,actual_overlap_words.1,actual_overlap_words.2,value⟩

theorem original_parent_start_negative :
    ¬∃es fs,PrerequisiteChain source [] es ∧PrerequisiteChain source [.fn,.arg] fs ∧
      es.map source.labelAt=fs.map source.labelAt := no_complete_old_label_match
end RootOverlap

namespace CP53
open SingleUnsafeCopyFunctionAppInputsChecks

theorem actual_distinct_safe_not_marked :
    leftHead++[.fn]≠rightHead++[.fn] ∧
    target.labelAt (leftHead++[.fn])=some (.atom 17) ∧
    target.labelAt (rightHead++[.fn])=some (.atom 17) ∧
    (Label.atom 17).OuterBarsSafe (fun d=>d≠Label.atom 6) ∧
    ¬¬(Label.atom 17).OuterBarsSafe (fun d=>d≠Label.atom 6) :=
  ⟨by decide,rfl,rfl,trivial,fun bad=>bad trivial⟩

theorem actual_one_local_history : History [[.fn],[.arg]] (initLabels source.erase)
    TerminalLambdaLastAtomChecks.CP53.localTarget := TerminalLambdaLastAtomChecks.CP53.localHistory
end CP53

namespace Nested
open UniformOldNodeLabelSuffixChecks
open DirectedMarkerSpineIncidenceChecks.Nested

theorem forward_complete_given_local_node
    (matching : Matches g root sourceWrapped.erase)
    (sourceSelection : OccurrenceFragmentSelection sourceWrapped g root)
    (sourceJoint : JointRepresentation sourceClosed sourceSelection)
    (selection : SourceEdgeSelection (initLabels sourceWrapped.erase) g root)
    (physical : BetaEdge g) :
    ∃leaf snapshot,
    ∃geometry : SpineIncidenceProvenance family sourceWrapped (.atom 10) true forwardSpine
      (by rfl : targetForward.subterm [.fn]=some target) leaf snapshot,
    ∃localTarget,∃localHistory : History [[.fn],[.fn]] (initLabels sourceWrapped.erase) localTarget,
    ∃pair : PairedSpineReannotation geometry localHistory (erase_initLabels sourceWrapped.erase).symm,
      2≤geometry.creationFrames.length ∧leaf.after≠[] ∧pair.localTailPieces≠[] ∧
      localTarget.subterm [.fn]=some pair.current ∧
      pair.current.label.readLetters true=pair.base.current.label.readLetters true++pair.localTailPieces.flatten ∧
      selection.evalLabel physical pair.current.label=selection.evalLabel physical pair.current.label := by
  obtain ⟨leaf,snapshot,geometry,localTarget,localHistory,pair,multiple,after,tails,atPair,word,_frames,_count⟩ :=
    PairedMarkerSpineReannotationChecks.Nested.forward_reannotated
  obtain ⟨a,l,b,arg,redex⟩ : ∃a l b arg,targetForward.subterm []=some (.app a (.lam l b) arg) := ⟨_,_,_,_,rfl⟩
  have atLambda : targetForward.subterm [.fn]=some (.lam l b) := by
    change targetForward.subterm (([] : Path)++[.fn])=_
    rw [LTerm.subterm_append,redex];rfl
  have equal : (.lam l b : LTerm)=target := Option.some.inj (atLambda.symm.trans (by rfl))
  have marked : ¬l.OuterBarsSafe (fun x=>x≠Label.atom 10) := by
    simpa only [←equal,LTerm.label] using forwardMarked
  obtain ⟨localStamp,localBody,localAt⟩ := local_lambda_lookup labelsForward localHistory atLambda
  have value := terminal_marked_lambda_evaluations initial globalPrefix sourceClosed oldForward labelsForward
    selected sourceSafe localHistory redex redex rfl marked localAt localAt
    matching sourceSelection sourceJoint selection physical
  have sameNode : pair.current=.lam localStamp localBody := Option.some.inj (atPair.symm.trans localAt)
  have actual : selection.evalLabel physical pair.current.label=selection.evalLabel physical pair.current.label := by
    exact Eq.mp (congrArg (fun t : LTerm=>selection.evalLabel physical t.label=
      selection.evalLabel physical t.label) sameNode.symm) value
  exact ⟨leaf,snapshot,geometry,localTarget,localHistory,pair,multiple,after,tails,atPair,word,actual⟩

theorem reverse_complete_given_local_node
    (matching : Matches g root sourceWrapped.erase)
    (sourceSelection : OccurrenceFragmentSelection sourceWrapped g root)
    (sourceJoint : JointRepresentation sourceClosed sourceSelection)
    (selection : SourceEdgeSelection (initLabels sourceWrapped.erase) g root)
    (physical : BetaEdge g) :
    ∃leaf snapshot,
    ∃geometry : SpineIncidenceProvenance family sourceWrapped (.atom 10) false reverseSpine
      (by rfl : targetReverse.subterm [.fn]=some reverseResult) leaf snapshot,
    ∃localTarget,∃localHistory : History [[.fn,.arg],[.fn]] (initLabels sourceWrapped.erase) localTarget,
    ∃pair : PairedSpineReannotation geometry localHistory (erase_initLabels sourceWrapped.erase).symm,
      2≤geometry.creationFrames.length ∧leaf.after≠[] ∧pair.localTailPieces≠[] ∧
      localTarget.subterm [.fn]=some pair.current ∧
      pair.current.label.readLetters false=pair.base.current.label.readLetters false++pair.localTailPieces.flatten ∧
      selection.evalLabel physical pair.current.label=selection.evalLabel physical pair.current.label := by
  obtain ⟨leaf,snapshot,geometry,localTarget,localHistory,pair,multiple,after,tails,atPair,word,_frames,_count⟩ :=
    PairedMarkerSpineReannotationChecks.Nested.reverse_reannotated
  obtain ⟨a,l,b,arg,redex⟩ : ∃a l b arg,targetReverse.subterm []=some (.app a (.lam l b) arg) := ⟨_,_,_,_,rfl⟩
  have atLambda : targetReverse.subterm [.fn]=some (.lam l b) := by
    change targetReverse.subterm (([] : Path)++[.fn])=_
    rw [LTerm.subterm_append,redex];rfl
  have equal : (.lam l b : LTerm)=reverseResult := Option.some.inj (atLambda.symm.trans (by rfl))
  have marked : ¬l.OuterBarsSafe (fun x=>x≠Label.atom 10) := by
    simpa only [←equal,LTerm.label] using reverseMarked
  obtain ⟨localStamp,localBody,localAt⟩ := local_lambda_lookup labelsReverse localHistory atLambda
  have value := terminal_marked_lambda_evaluations initial globalPrefix sourceClosed oldReverse labelsReverse
    selected sourceSafe localHistory redex redex rfl marked localAt localAt
    matching sourceSelection sourceJoint selection physical
  have sameNode : pair.current=.lam localStamp localBody := Option.some.inj (atPair.symm.trans localAt)
  have actual : selection.evalLabel physical pair.current.label=selection.evalLabel physical pair.current.label := by
    exact Eq.mp (congrArg (fun t : LTerm=>selection.evalLabel physical t.label=
      selection.evalLabel physical t.label) sameNode.symm) value
  exact ⟨leaf,snapshot,geometry,localTarget,localHistory,pair,multiple,after,tails,atPair,word,actual⟩
end Nested
end

#print axioms terminal_marked_lambda_evaluations
#print axioms RootOverlap.actual_complete_marked_q0
#print axioms RootOverlap.original_parent_start_negative
#print axioms CP53.actual_distinct_safe_not_marked
#print axioms CP53.actual_one_local_history
#print axioms Nested.forward_complete_given_local_node
#print axioms Nested.reverse_complete_given_local_node
end Lamping.Checks.TerminalMarkedLambdaEvaluationsChecks