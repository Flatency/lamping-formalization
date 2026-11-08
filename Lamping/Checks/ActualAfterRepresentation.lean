import Lamping.Lamping.ActualAfterRepresentation
import Lamping.Checks.FanSuccessfulReachable
import Lamping.Checks.BoundedAfterPhysicalComparison

namespace Lamping.Checks.ActualAfterRepresentationChecks
open AG Graph Lambda Lambda.Labelled FanSuccessfulChains

private theorem cut_at_head
    {start : Path}
    (cut : ActualUnsafeMarkerCut [[.fn]] [[.fn]] original current (.atom 2) start rightEdges) :
    cut.before=[] ∧cut.after=rightEdges.tail := by
  have notSafe := BoundedAfterPhysicalComparisonChecks.Physical.rightUnsafe
  cases front : cut.before with
  | nil =>
    have split := cut.split
    rw [front,List.nil_append] at split
    exact ⟨rfl,(List.cons.inj split).2.symm⟩
  | cons head rest =>
    have split := cut.split
    rw [front,List.cons_append] at split
    have same : right=head := (List.cons.inj split).1
    have member : right∈cut.before := by rw [front,same];exact List.mem_cons_self
    exact False.elim (notSafe (cut.safeBefore right member))

theorem actual_distinct_start_nonempty_after
    (selection : OccurrenceFragmentSelection current
      FanSuccessfulReachable.concrete.site.reduce (.inl ())) :
    right≠rightVar ∧
    SameChainRepresentation selection right_lambda_chain right_variable_chain ∧
    ∃left : ActualUnsafeMarkerCut [[.fn]] [[.fn]] original current (.atom 2) right rightEdges,
      ∃rightCut : ActualUnsafeMarkerCut [[.fn]] [[.fn]] original current (.atom 2) rightVar rightEdges,
        left.before=[] ∧rightCut.before=[] ∧
        left.after=rightEdges.tail ∧rightCut.after=rightEdges.tail ∧
        left.after.length=3 ∧rightCut.after.length=3 ∧
        (left.after=[] ↔rightCut.after=[]) ∧
        ∃(leftNext rightNext : Path)
          (leftAfter : PrerequisiteChain current leftNext left.after)
          (rightAfter : PrerequisiteChain current rightNext rightCut.after),
          ActualAfterStart current left.reader left.edge leftNext ∧
          ActualAfterStart current rightCut.reader rightCut.edge rightNext ∧
          SameChainRepresentation selection leftAfter rightAfter ∧
          left.after.length<rightEdges.length ∧rightCut.after.length<rightEdges.length ∧
          max left.after.length rightCut.after.length<max rightEdges.length rightEdges.length := by
  have physical : SameChainRepresentation selection right_lambda_chain right_variable_chain := rfl
  rcases actual_first_unsafe_marker_leaves initial (.nil original)
      BoundedAfterPhysicalComparisonChecks.Physical.old actualHistory
      BoundedAfterPhysicalComparisonChecks.Physical.selected (initial.outerBarsSafe _) targetClosed
      right_lambda_chain right_variable_chain (ChainIncidenceIso.refl _) with all | cuts
  · exact False.elim (BoundedAfterPhysicalComparisonChecks.Physical.rightUnsafe
      (all.1 right (by simp [rightEdges])))
  · obtain ⟨left,rc,_len,_lt,_rt,_ld,_rd,_front,_head,_back,_tails,_signs⟩ := cuts
    obtain ⟨lb,la⟩ := cut_at_head left
    obtain ⟨rb,ra⟩ := cut_at_head rc
    have before : left.before.length=rc.before.length := by rw [lb,rb]
    have more : left.after≠[] := by rw [la];decide
    obtain ⟨_rm,_al,ln,rn,lc,rr,lg,rg,eq,ll,rl,mm⟩ :=
      actual_cut_after_same_representation selection right_lambda_chain right_variable_chain physical left rc before more
    have cases := actual_cut_after_representation_cases selection right_lambda_chain right_variable_chain physical left rc before
    exact ⟨by decide,physical,left,rc,lb,rb,la,ra,by rw [la];rfl,by rw [ra];rfl,
      cases.2.1,ln,rn,lc,rr,lg,rg,eq,ll,rl,mm⟩

#print axioms actual_distinct_start_nonempty_after
end Lamping.Checks.ActualAfterRepresentationChecks
