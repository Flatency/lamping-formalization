import Lamping.Lamping.BetaUncreatedFragmentResiduals
import Lamping.Checks.BetaFiberDegrees
import Lamping.Checks.Soundness
namespace Lamping.Checks.BetaUncreatedFragmentResiduals
open AG Graph Lambda Lambda.Labelled
private def compound : Labelled.Label := (Labelled.Label.atom 9).concat (Labelled.Label.atom 10).over
private def source : LTerm := .app (.atom 9)
  (.lam (.atom 9) (.var (.atom 9) 0)) (.lam compound (.var compound 0))
private abbrev target := LTerm.contract (.atom 9) (.atom 9)
  (.var (.atom 9) 0) (.lam compound (.var compound 0))
private def turn : StepAt [] source target := .root _ _ _ _
private def labels : History [[]] source target := .cons turn (.nil _)
private theorem closed : Closed source.erase := ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
private theorem matching : Matches actualBetaSite.net (.inl ()) source.erase :=
  betaEncodingIso.matches (encode_closed_matches identityApp closed 0)
private theorem relative : Marked.RelativeHistory [[]]
    (Marked.mark (actualBetaSite.betaSyntaxFiber (.inl ()) source.erase) source.erase) (.lam (.var 0)) := by
  change Marked.RelativeHistory [[]]
    (if ([] : Path)∈actualBetaSite.betaSyntaxFiber (.inl ()) source.erase then
      .red [[]] (.var 0) (.lam (.var 0)) else .app [[]] (.lam (.var 0)) (.lam (.var 0))) (.lam (.var 0))
  have member : []∈actualBetaSite.betaSyntaxFiber (.inl ()) source.erase := BetaFiberDegrees.actual_root_member
  rw [if_pos member]
  exact .cons (.root _ _ _) (.nil _)
private theorem normal : Marked.Normal (.lam (.var 0)) := by simp [Marked.Normal]
private def whole : ParallelStep [[]] source.erase target.erase := by
  refine ⟨[[]],.lam (.var 0),(Marked.completeOld_iff _ _).mpr ⟨?_,True.intro⟩,rfl⟩
  change Marked.RelativeHistory [[]] (.red [[]] (.var 0) (.lam (.var 0))) (.lam (.var 0))
  exact .cons (.root _ _ _) (.nil _)
private def oldVariable : Position source.erase := ⟨[.arg,.body],rfl⟩
private def newVariable : Position target.erase := ⟨[.body],rfl⟩

/-- Both selectors are arbitrary. The source label is compound and the
target parent is created, but its actual kept port supplies the exact cut.
The old coordinate is locked by the original GLOBAL operational trace. -/
theorem actual_copied_variable_fragment
    (sourceSelection : OccurrenceFragmentSelection source actualBetaSite.net (.inl ()))
    (targetSelection : OccurrenceFragmentSelection target actualBetaSite.reduce (.inl ())) :
    ∃ edge : BetaEdge actualBetaSite.net,SiteBetaGeometry actualBetaSite edge ∧
      BetaPathResidual actualBetaSite edge
        ((targetSelection newVariable).fragment.segments.map (plugEnd _ _).invFun)
        (sourceSelection oldVariable).fragment.segments := by
  have inputs := betaEncodingIso.rootInputs (encode_closed_independence identityApp closed 0).rootInputs
  obtain ⟨initialBalance⟩ := encode_indexed_balance identityApp 0
  have balance := betaEncodingIso.indexed_balance initialBalance
  have transparency := betaEncodingIso.transparency (encode_closed_transparency identityApp closed 0)
  have selected (path : Path) (member : path∈([[]] : List Path)) :
      source.degreeAt path=some (Labelled.Label.atom 9) := by
    have equal := List.mem_singleton.mp member
    subst path;rfl
  obtain ⟨edge,geometry,all⟩ := actualBetaSite.beta_uncreated_child_residuals closed matching inputs
    SoundnessBetaAncestor.actualFlow rfl balance rfl transparency relative normal labels whole.complete.1
      (DegreeAligned.initial source [[]]) selected
  let child := targetSelection newVariable
  have occurrence : SourceSubterm [] .external target [.body] [target.label] (.lamBody target.label)
      (.var compound 0) := .body .nil
  obtain ⟨_environment,context,term⟩ := child.occurrence.same_occurrence occurrence
  have fromEq : (sourceEdge child.environment child.context child.term).fromPort=child.context := by
    cases child.term <;> rfl
  have role : SourceDeparture target .body (sourceEdge child.environment child.context child.term).fromPort := by
    rw [fromEq,context]
    exact .body
  have safe : child.term.label.OuterBarsSafe (fun payload=>payload≠Labelled.Label.atom 9) := by
    rw [term]
    change Labelled.Label.atom 10≠Labelled.Label.atom 9
    decide
  obtain ⟨oldPosition,oldNode,_oldLookup,trace,residual⟩ := all [] .body target rfl child role safe
  have origin : BetaNodePreimage (.var (.atom 9) 0) (.lam compound (.var compound 0))
      [] [.body] [.arg,.body] := .copied (q:=[]) (relative:=[.body]) rfl rfl
  have known : BetaNodeHistoryPreimage labels [.body] [.arg,.body] :=
    .one (step:=turn) rfl origin (.nil target [.body])
  have samePosition := trace.unique known
  subst oldPosition
  exact ⟨edge,geometry,residual (sourceSelection oldVariable)⟩

/-- The actual fragment has no beta reconnection block: its original
source empty syntax word is consumed by the existing atomic theorem. -/
theorem actual_copied_variable_is_exterior
    (sourceSelection : OccurrenceFragmentSelection source actualBetaSite.net (.inl ()))
    (targetSelection : OccurrenceFragmentSelection target actualBetaSite.reduce (.inl ())) :
    ∃ edge : BetaEdge actualBetaSite.net,SiteBetaGeometry actualBetaSite edge ∧
      ∃ exterior,
        (targetSelection newVariable).fragment.segments.map (plugEnd _ _).invFun=List.map Sum.inl exterior ∧
        (sourceSelection oldVariable).fragment.segments=List.map actualBetaSite.outsideEnd exterior := by
  obtain ⟨edge,geometry,residual⟩ := actual_copied_variable_fragment sourceSelection targetSelection
  obtain ⟨exterior,raw,old⟩ := residual.atomic_exterior actualBetaSite geometry
    (sourceSelection oldVariable).fragment.emptyWord
  exact ⟨edge,geometry,exterior,raw,old⟩

#print axioms LTerm.sourceTrail_single_child_evaluation
#print axioms PathSite.beta_uncreated_child_residuals
#print axioms actual_copied_variable_fragment
#print axioms actual_copied_variable_is_exterior
end Lamping.Checks.BetaUncreatedFragmentResiduals

