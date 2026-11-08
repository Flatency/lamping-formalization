import Lamping.Lamping.GivenParentCanonicalFarComparison
import Lamping.Checks.ParentCanonicalFarComparison
import Lamping.Checks.NormalFalseCanonicalOriginalComparison

namespace Lamping.Checks.GivenParentCanonicalFarComparisonChecks
open Graph Lambda Lambda.Labelled AG SyntaxIncidence

namespace CP53
open SingleUnsafeCopyFunctionAppInputsChecks

/-- Preserve the SAME returned CP53 cuts, snapshots and safe geometries.
The NEW top receives actual wholeIso, never old good or an after-kind profile. -/
theorem actual_noninitial_given_outputs :
    ∃out : SingleUnsafeCopyFunctionAppInputs event sourceClosed leftStart rightStart [.fn] [.arg] es fs,
      out.left.before=[leftStart] ∧out.right.before=[rightStart] ∧
      out.left.after=[leftHead++[.fn]] ∧out.right.after=[rightHead++[.fn]] ∧
      ∃left : CanonicalAfterFarOutput event.final_history out.left out.leftSnapshot,
      ∃right : CanonicalAfterFarOutput event.final_history out.right out.rightSnapshot,
        CanonicalFarFullComparison sourceClosed left right ∧
        out.left.forward=true ∧out.right.forward=true ∧
        out.leftGeometry.creationFrames.length=1 ∧out.rightGeometry.creationFrames.length=1 := by
  obtain ⟨out,lb,rb,_le,_re,la,ra,_rest⟩ := actual_final_safe_leaves
  obtain ⟨left⟩ := out.left.canonical_far_output event.final_history sourceClosed
    out.leftAfterNonempty out.leftSnapshot
  obtain ⟨right⟩ := out.right.canonical_far_output event.final_history sourceClosed
    out.rightAfterNonempty out.rightSnapshot
  obtain ⟨iso⟩ := currentIso
  have good := actual_given_parent_canonical_far_comparison initial prefixHistory sourceClosed
    event.final_old event.final_history selected sourceSafe out.left out.right
    out.leftAfterNonempty out.rightAfterNonempty out.leftSnapshot out.rightSnapshot left right iso
  exact ⟨out,lb,rb,la,ra,left,right,good,out.leftTrue,out.rightTrue,out.leftSingle,out.rightSingle⟩

theorem actual_history_distinct_starts :
    INIT original ∧History [[.arg,.fn,.body],[],[.fn],[.arg]] original target ∧
    leftStart≠rightStart ∧¬INIT source ∧es.length=3 ∧fs.length=3 :=
  ⟨initial,prefixHistory.append event.final_history,by decide,sourceNotInit,rfl,rfl⟩
end CP53

namespace MultipleAfter
open ParentCanonicalFarComparisonChecks.MultipleAfter

/-- The canonical objects are fixed before the NEW call. The existing
two-edge AFTER fixture is all-safe, not an opposite-branch witness. -/
theorem actual_given_two_edge_afters :
    ∃lc : ActualUnsafeMarkerCut F [left,right] source target (.atom 8) leftStart es,
    ∃rc : ActualUnsafeMarkerCut F [left,right] source target (.atom 8) rightStart fs,
      lc.before=[leftStart] ∧rc.before=[rightStart] ∧
      lc.after=[leftHead++[.fn],[.fn]] ∧rc.after=[rightHead++[.fn],[.fn]] ∧
      ∃ls rs,∃lo : CanonicalAfterFarOutput event.final_history lc ls,
      ∃ro : CanonicalAfterFarOutput event.final_history rc rs,
        CanonicalFarFullComparison sourceClosed lo ro ∧lc.after.length=2 ∧rc.after.length=2 := by
  obtain ⟨lc,rc,lb,rb,la,ra,ls,rs,lo,ro,_priorGood⟩ := actual_two_edge_after_source_comparison
  obtain ⟨iso⟩ := currentIso
  have lm : lc.after≠[] := by rw [la];decide
  have rm : rc.after≠[] := by rw [ra];decide
  have good := actual_given_parent_canonical_far_comparison initial prefixHistory sourceClosed
    event.final_old event.final_history selected sourceSafe lc rc lm rm ls rs lo ro iso
  exact ⟨lc,rc,lb,rb,la,ra,ls,rs,lo,ro,good,by rw [la];rfl,by rw [ra];rfl⟩

theorem actual_variable_zero_jump :
    PrerequisiteChain target (leftHead++[.fn]) [[.fn]] ∧
    PrerequisiteChain target (rightHead++[.fn]) [[.fn]] ∧
    leftHead++[.fn]≠([.fn] : Path) ∧rightHead++[.fn]≠([.fn] : Path) := actual_zero_jump_tail
end MultipleAfter

namespace CP57
open SafeLastCopyArgumentAuxInputsChecks
open FalseCopyFirstSafeLabelsChecks

/-- GIVEN early and late geometries/recents survive the comparison. No
new canonical_recent_last_output replaces their actual witness provenance. -/
theorem actual_same_given_cross_prefix_context :
    ∃el esnap,
    ∃eg : SpineIncidenceProvenance F source (.atom 6) false earlyCut.spine earlyCut.lookup el esnap,
    ∃er : RecentSpineFrame eg,
    ∃ll lsnap,
    ∃lg : SpineIncidenceProvenance F source (.atom 6) false lateCut.spine lateCut.lookup ll lsnap,
    ∃lr : RecentSpineFrame lg,
    ∃left : CanonicalAfterFarOutput event.final_history earlyCut esnap,
    ∃right : CanonicalAfterFarOutput event.final_history lateCut lsnap,
      CanonicalFarFullComparison sourceClosed left right ∧
      er.packet.pre=[] ∧er.packet.site=[.fn] ∧er.suffixSites=[[.arg]] ∧
      lr.packet.pre=[[.fn]] ∧lr.packet.site=[.arg] ∧lr.suffixSites=[] := by
  obtain ⟨el,esnap,eg,er,ll,lsnap,lg,lr,left,right,_priorComparison,
    ep,et,ef,lp,lt,lf,_rest⟩ := NormalFalseCanonicalOriginalComparisonChecks.actual_given_cross_prefix_aux
  obtain ⟨iso⟩ := actual_chain_iso_of_labels (prefixHistory.append event.final_history) initial
    targetClosed earlyChain leftChain (by rfl)
  have good := actual_given_parent_canonical_far_comparison initial prefixHistory sourceClosed
    event.final_old event.final_history selected sourceSafe earlyCut lateCut (by decide) (by decide)
    esnap lsnap left right iso
  exact ⟨el,esnap,eg,er,ll,lsnap,lg,lr,left,right,good,ep,et,ef,lp,lt,lf⟩

/-- FALSE equality is literal reader equality; the NEW general uniqueness
does not add an orientation premise or replace the given cuts. -/
theorem false_cut_unique
    (other : ActualUnsafeMarkerCut F [[.fn],[.arg]] source target (.atom 6) earlyHead earlyEdges) :
    earlyCut=other := earlyCut.nonterminal_unique other (by decide)
end CP57

namespace Terminal
open DirectedReadingDecompositionChecks
open PairedCurrentChainSourceLabelsChecks.Terminal

theorem retained_actual_terminal_boundary :
    (∃left : ActualUnsafeMarkerCut [[.fn]] [[.fn]] source target (.atom 2) [] [[.fn]],
      ∃right : ActualUnsafeMarkerCut [[.fn]] [[.fn]] source target (.atom 2) [.fn] [[.fn]],
        left.after=[] ∧right.after=[] ∧left.forward≠right.forward) ∧
    (¬∃es fs,PrerequisiteChain source [] es ∧PrerequisiteChain source [.fn,.arg] fs ∧
      es.map source.labelAt=fs.map source.labelAt) :=
  CanonicalAfterFarComparisonChecks.TerminalBoundary.actual_terminal_opposite_not_full_source_match
end Terminal

#print axioms ActualUnsafeMarkerCut.nonterminal_unique
#print axioms CanonicalAfterFarOutput.source_data_unique
#print axioms actual_given_parent_canonical_far_comparison
#print axioms CP53.actual_noninitial_given_outputs
#print axioms CP53.actual_history_distinct_starts
#print axioms MultipleAfter.actual_given_two_edge_afters
#print axioms MultipleAfter.actual_variable_zero_jump
#print axioms CP57.actual_same_given_cross_prefix_context
#print axioms CP57.false_cut_unique
#print axioms Terminal.retained_actual_terminal_boundary
end Lamping.Checks.GivenParentCanonicalFarComparisonChecks
