import Lamping.Lamping.MultiedgeAfterFarComparison
import Lamping.Checks.SynchronizedUnsafeCuts
import Lamping.Checks.ParentCanonicalFarComparison
namespace Lamping.Checks.MultiedgeAfterFarComparisonChecks
open Graph Lambda Lambda.Labelled AG SyntaxIncidence

private theorem snapshot {t : LTerm} (closed : Closed t.erase)
    (lookup : t.subterm edge=some node) : Nonempty (IncomingIncidenceSnapshot t edge) := by
  let actual : Edge t := ⟨edge,by rw [←LTerm.erase_subterm,lookup];rfl⟩
  obtain ⟨origin,fromSpec⟩ := source_total t actual
  obtain ⟨destination,toSpec⟩ := target_total t closed actual
  exact ⟨⟨origin,destination,fromSpec,toSpec⟩⟩

section Fan
open FanSuccessfulChains
private theorem fanOld : Marked.RelativeOldHistory [[.fn]] [[.fn]]
    (Marked.mark [[.fn]] original.erase) FanSuccessfulReachable.endpoint :=
  .cons (.appL (.redRoot _ _ _)) (by decide) (.nil _)
private theorem fanSelected (name : Path) (member : name∈([[.fn]] : List Path)) :
    original.degreeAt name=some (.atom 2) := by
  have eq := List.mem_singleton.mp member;subst name;rfl

/-- The actual different starts share AFTER3; its iso is supplied from these
literal real AFTER lists, never from a whole-parent inverse theorem. -/
theorem actual_fan_after_three :
    right≠rightVar ∧
    ∃lc : ActualUnsafeMarkerCut [[.fn]] [[.fn]] original current (.atom 2) right rightEdges,
    ∃rc : ActualUnsafeMarkerCut [[.fn]] [[.fn]] original current (.atom 2) rightVar rightEdges,
      lc.after=rightEdges.tail ∧rc.after=rightEdges.tail ∧
      ∃ls rs,∃lo : CanonicalAfterFarOutput actualHistory lc ls,
      ∃ro : CanonicalAfterFarOutput actualHistory rc rs,
        CanonicalFarFullComparison sourceClosed lo ro ∧
        lc.after.length=3 ∧rc.after.length=3 := by
  obtain ⟨different,_four,lc,rc,_lb,_rb,_le,_re,la,ra⟩ :=
    SynchronizedUnsafeCutsChecks.actual_first_unsafe_zero
  obtain ⟨ls⟩ := snapshot targetClosed lc.lookup
  obtain ⟨rs⟩ := snapshot targetClosed rc.lookup
  have lm : lc.after≠[] := by rw [la];decide
  have rm : rc.after≠[] := by rw [ra];decide
  obtain ⟨lo⟩ := lc.canonical_far_output actualHistory sourceClosed lm ls
  obtain ⟨ro⟩ := rc.canonical_far_output actualHistory sourceClosed rm rs
  have labelsEq : lc.after.map current.labelAt=rc.after.map current.labelAt := by rw [la,ra]
  obtain ⟨afterIso⟩ := actual_chain_iso_of_labels actualHistory initial targetClosed
    lo.currentChain ro.currentChain labelsEq
  have comparison := canonical_multiedge_after_far_comparison initial (.nil original) sourceClosed
    fanOld actualHistory fanSelected (initial.outerBarsSafe _) lc rc ls rs lo ro afterIso (by rw [la];decide)
  exact ⟨different,lc,rc,la,ra,ls,rs,lo,ro,comparison,by rw [la];rfl,by rw [ra];rfl⟩
end Fan

section Noninitial
open ParentCanonicalFarComparisonChecks.MultipleAfter

private theorem sourceNotInitial : ¬INIT source := by
  intro init
  obtain ⟨a,b,arg,atLeft⟩ := LTerm.degreeAt_redex (selected left (by simp [F]))
  obtain ⟨c,d,arg',atRight⟩ := LTerm.degreeAt_redex (selected right (by simp [F]))
  have ll : source.subterm (left++[.fn])=some (.lam (.atom 8) b) := by
    rw [LTerm.subterm_append,atLeft];rfl
  have rr : source.subterm (right++[.fn])=some (.lam (.atom 8) d) := by
    rw [LTerm.subterm_append,atRight];rfl
  have coordinates := LTerm.subterm_label_injective source init.2 ll rr rfl
  exact (by decide : left++[.fn]≠right++[.fn]) coordinates

/-- The nonINIT prefix and true binder-zero-jump AFTER2 are kept. The old
comparison packet is used only for its cuts/snapshots; its good is discarded,
and fresh canonical outputs plus a direct tail-label iso feed the NEW top. -/
theorem actual_noninitial_after_two :
    ¬INIT source ∧History [[.fn,.body,.arg,.fn,.body],[.fn,.body]] original source ∧
    ∃lc : ActualUnsafeMarkerCut F [left,right] source target (.atom 8) leftStart es,
    ∃rc : ActualUnsafeMarkerCut F [left,right] source target (.atom 8) rightStart fs,
      lc.after=[leftHead++[.fn],[.fn]] ∧rc.after=[rightHead++[.fn],[.fn]] ∧
      ∃ls rs,∃lo : CanonicalAfterFarOutput event.final_history lc ls,
      ∃ro : CanonicalAfterFarOutput event.final_history rc rs,
        CanonicalFarFullComparison sourceClosed lo ro ∧
        lc.after.length=2 ∧rc.after.length=2 ∧
        PrerequisiteChain target (leftHead++[.fn]) [[.fn]] ∧
        PrerequisiteChain target (rightHead++[.fn]) [[.fn]] := by
  obtain ⟨lc,rc,_lb,_rb,la,ra,ls,rs,_oldLeft,_oldRight,_discardedOldGood⟩ :=
    actual_two_edge_after_source_comparison
  have lm : lc.after≠[] := by rw [la];decide
  have rm : rc.after≠[] := by rw [ra];decide
  obtain ⟨lo⟩ := lc.canonical_far_output event.final_history sourceClosed lm ls
  obtain ⟨ro⟩ := rc.canonical_far_output event.final_history sourceClosed rm rs
  have labelsEq : lc.after.map target.labelAt=rc.after.map target.labelAt := by rw [la,ra];rfl
  obtain ⟨afterIso⟩ := actual_chain_iso_of_labels (prefixHistory.append event.final_history)
    initial targetClosed lo.currentChain ro.currentChain labelsEq
  have comparison := canonical_multiedge_after_far_comparison initial prefixHistory sourceClosed
    event.final_old event.final_history selected sourceSafe lc rc ls rs lo ro afterIso (by rw [la];decide)
  exact ⟨sourceNotInitial,prefixHistory,lc,rc,la,ra,ls,rs,lo,ro,comparison,
    by rw [la];rfl,by rw [ra];rfl,leftJump,rightJump⟩
end Noninitial

#print axioms actual_fan_after_three
#print axioms actual_noninitial_after_two
end Lamping.Checks.MultiedgeAfterFarComparisonChecks

