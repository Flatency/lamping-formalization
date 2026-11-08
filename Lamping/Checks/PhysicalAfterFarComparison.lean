import Lamping.Lamping.PhysicalAfterFarComparison
import Lamping.Checks.ActualAfterRepresentation
import Lamping.Checks.SynchronizedUnsafeCuts

namespace Lamping.Checks.PhysicalAfterFarComparisonChecks
open AG Graph Lambda Lambda.Labelled SyntaxIncidence FanSuccessfulChains

private theorem snapshot {t : LTerm} (closed : Closed t.erase)
    (lookup : t.subterm edge=some node) : Nonempty (IncomingIncidenceSnapshot t edge) := by
  let actual : Edge t := ⟨edge,by rw [←LTerm.erase_subterm,lookup];rfl⟩
  obtain ⟨origin,fromSpec⟩ := source_total t actual
  obtain ⟨destination,toSpec⟩ := target_total t closed actual
  exact ⟨⟨origin,destination,fromSpec,toSpec⟩⟩

private theorem fanOld : Marked.RelativeOldHistory [[.fn]] [[.fn]]
    (Marked.mark [[.fn]] original.erase) FanSuccessfulReachable.endpoint :=
  .cons (.appL (.redRoot _ _ _)) (by decide) (.nil _)
private theorem fanSelected (name : Path) (member : name∈([[.fn]] : List Path)) :
    original.degreeAt name=some (.atom 2) := by
  have eq := List.mem_singleton.mp member;subst name;rfl

/-- Actual different starts and SAME physical corridor; the genuine AFTERiso
is supplied from the real equal three-edge tails, not an inverse theorem. -/
theorem actual_fan_after_three
    (selection : OccurrenceFragmentSelection current
      FanSuccessfulReachable.concrete.site.reduce (.inl ())) :
    right≠rightVar ∧
    ∃lc : ActualUnsafeMarkerCut [[.fn]] [[.fn]] original current (.atom 2) right rightEdges,
    ∃rc : ActualUnsafeMarkerCut [[.fn]] [[.fn]] original current (.atom 2) rightVar rightEdges,
      lc.before=[] ∧rc.before=[] ∧lc.after=rightEdges.tail ∧rc.after=rightEdges.tail ∧
      ∃ls rs,∃lo : CanonicalAfterFarOutput actualHistory lc ls,
      ∃ro : CanonicalAfterFarOutput actualHistory rc rs,
        CanonicalFarFullComparison sourceClosed lo ro ∧
        lc.after.length=3 ∧rc.after.length=3 := by
  obtain ⟨different,physical,lc,rc,lb,rb,la,ra,ll,rl,_rest⟩ :=
    ActualAfterRepresentationChecks.actual_distinct_start_nonempty_after selection
  obtain ⟨ls⟩ := snapshot targetClosed lc.lookup
  obtain ⟨rs⟩ := snapshot targetClosed rc.lookup
  have lm : lc.after≠[] := by rw [la];decide
  have rm : rc.after≠[] := by rw [ra];decide
  obtain ⟨lo⟩ := lc.canonical_far_output actualHistory sourceClosed lm ls
  obtain ⟨ro⟩ := rc.canonical_far_output actualHistory sourceClosed rm rs
  have labelsEq : lc.after.map current.labelAt=rc.after.map current.labelAt := by rw [la,ra]
  obtain ⟨afterIso⟩ := actual_chain_iso_of_labels actualHistory initial targetClosed
    lo.currentChain ro.currentChain labelsEq
  have ordinal : lc.before.length=rc.before.length := by rw [lb,rb]
  have comparison := actual_physical_after_far_comparison initial (.nil original) sourceClosed
    fanOld actualHistory fanSelected (initial.outerBarsSafe _) FanSuccessfulReachable.beta_matches
    selection right_lambda_chain right_variable_chain physical lc rc ordinal ls rs lo ro afterIso
  exact ⟨different,lc,rc,lb,rb,la,ra,ls,rs,lo,ro,comparison,ll,rl⟩

/-- Honest selfpair at ordinal one of the real five-READ body chain. -/
theorem actual_nonzero_cut_selfpair
    (selection : OccurrenceFragmentSelection current
      FanSuccessfulReachable.concrete.site.reduce (.inl ())) :
    ∃lc : ActualUnsafeMarkerCut [[.fn]] [[.fn]] original current (.atom 2) rightBody rightBodyEdges,
    ∃rc : ActualUnsafeMarkerCut [[.fn]] [[.fn]] original current (.atom 2) rightBody rightBodyEdges,
      lc.before=[rightVar] ∧rc.before=[rightVar] ∧lc.edge=right ∧rc.edge=right ∧
      ∃ls rs,∃lo : CanonicalAfterFarOutput actualHistory lc ls,
      ∃ro : CanonicalAfterFarOutput actualHistory rc rs,
        CanonicalFarFullComparison sourceClosed lo ro ∧
        lc.before.length=1 ∧rc.before.length=1 ∧lc.after.length=3 ∧rc.after.length=3 := by
  obtain ⟨_vector,lc,rc,lb,rb,le,re,la,ra,bl,br,ll,rl⟩ :=
    SynchronizedUnsafeCutsChecks.actual_first_unsafe_one
  obtain ⟨ls⟩ := snapshot targetClosed lc.lookup
  obtain ⟨rs⟩ := snapshot targetClosed rc.lookup
  have lm : lc.after≠[] := by rw [la];decide
  have rm : rc.after≠[] := by rw [ra];decide
  obtain ⟨lo⟩ := lc.canonical_far_output actualHistory sourceClosed lm ls
  obtain ⟨ro⟩ := rc.canonical_far_output actualHistory sourceClosed rm rs
  have labelsEq : lc.after.map current.labelAt=rc.after.map current.labelAt := by rw [la,ra]
  obtain ⟨afterIso⟩ := actual_chain_iso_of_labels actualHistory initial targetClosed
    lo.currentChain ro.currentChain labelsEq
  have physical : SameChainRepresentation selection right_body_chain right_body_chain := rfl
  have ordinal : lc.before.length=rc.before.length := by rw [lb,rb]
  have comparison := actual_physical_after_far_comparison initial (.nil original) sourceClosed
    fanOld actualHistory fanSelected (initial.outerBarsSafe _) FanSuccessfulReachable.beta_matches
    selection right_body_chain right_body_chain physical lc rc ordinal ls rs lo ro afterIso
  exact ⟨lc,rc,lb,rb,le,re,ls,rs,lo,ro,comparison,bl,br,ll,rl⟩

#print axioms actual_fan_after_three
#print axioms actual_nonzero_cut_selfpair
end Lamping.Checks.PhysicalAfterFarComparisonChecks
