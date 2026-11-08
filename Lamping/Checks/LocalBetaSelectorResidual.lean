import Lamping.Lamping.LocalBetaSelectorResidual
import Lamping.Checks.BetaFiberDegrees
import Lamping.Checks.Soundness
namespace Lamping.Checks.LocalBetaSelectorResidual
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

theorem actual_source_compound_is_not_atom (n : Nat) : compound≠Labelled.Label.atom n := by
  intro impossible
  cases impossible

/-- A genuinely non-INIT global annotation and its SAME actual schedule
supply both the actual selected target path's whole residual and the
terminal local evaluator's equality with an arbitrary GLOBAL old fragment.
The original global history locks that fragment's coordinate. -/
theorem actual_global_selector_and_old_fragment
    (globalSelection : OccurrenceFragmentSelection source actualBetaSite.net (.inl ())) (requested : Context) :
    ∃ localTarget,∃ _localLabels : History [[]] (initLabels source.erase) localTarget,
      ∃ edge : BetaEdge actualBetaSite.net,
      ∃ selection : SourceEdgeSelection (initLabels source.erase) actualBetaSite.net (.inl ()),
      ∃ access : RootAccess actualBetaSite.reduce (.inl ()),∃ localSub old output,
        localTarget.erase=target.erase ∧localTarget.subterm [.body]=some localSub ∧
        accessWord actualBetaSite.reduce access.val=[.body] ∧
        localTarget.sourceTrail selection.atomWord edge.principal edge.reverseRoute [.body]=some old ∧
        BetaPathResidual actualBetaSite edge (access.val.map (plugEnd _ _).invFun) old ∧
        Labelling actualBetaSite.reduce access.val requested output ∧
        selection.evalLabel edge localSub.label=(globalSelection oldVariable).fragment.segments := by
  have inputs := betaEncodingIso.rootInputs (encode_closed_independence identityApp closed 0).rootInputs
  obtain ⟨initialBalance⟩ := encode_indexed_balance identityApp 0
  have balance := betaEncodingIso.indexed_balance initialBalance
  have transparency := betaEncodingIso.transparency (encode_closed_transparency identityApp closed 0)
  obtain ⟨localTarget,localLabels,sameErase,targetMatching,edge,selection,_geometry,all⟩ :=
    actualBetaSite.beta_local_selector_residuals closed matching inputs SoundnessBetaAncestor.actualFlow rfl
      balance rfl transparency relative normal labels
  let position : Position target.erase := ⟨[.body],rfl⟩
  obtain ⟨access,word,_shape⟩ := Matches.observation _ targetMatching position
  obtain ⟨localSub,localLookup,_sameSub,finish,trail,output,_node,_port,evaluation,residual,assignment,_ending,_proper⟩ :=
    all (p:=[.body]) (sub:=.var compound 0) rfl access word requested
  have selected (path : Path) (member : path∈([[]] : List Path)) :
      source.degreeAt path=some (Labelled.Label.atom 9) := by
    have equal := List.mem_singleton.mp member
    subst path;rfl
  have safe : compound.OuterBarsSafe (fun payload=>payload≠Labelled.Label.atom 9) := by
    change Labelled.Label.atom 10≠Labelled.Label.atom 9
    decide
  obtain ⟨oldPosition,oldNode,_oldLookup,trace,block⟩ :=
    selection.marker_free_local_evaluation (source:=source) (edge:=[.body]) matching whole.complete.1
      (DegreeAligned.initial source [[]]) labels localLabels selected
      (current:=.var compound 0) (localCurrent:=localSub) rfl localLookup safe edge
  have origin : BetaNodePreimage (.var (.atom 9) 0) (.lam compound (.var compound 0))
      [] [.body] [.arg,.body] := .copied (q:=[]) (relative:=[.body]) rfl rfl
  have known : BetaNodeHistoryPreimage labels [.body] [.arg,.body] :=
    .one (step:=turn) rfl origin (.nil target [.body])
  have samePosition := trace.unique known
  subst oldPosition
  exact ⟨localTarget,localLabels,edge,selection,access,localSub,trail.edges,output,sameErase,localLookup,word,
    evaluation,residual,assignment,block (globalSelection oldVariable)⟩

#print axioms PathSite.beta_local_selector_residuals
#print axioms actual_source_compound_is_not_atom
#print axioms actual_global_selector_and_old_fragment
end Lamping.Checks.LocalBetaSelectorResidual

