import Lamping.Lamping.PhysicalReadingRoles
import Lamping.Checks.ActualAfterRepresentation

namespace Lamping.Checks.PhysicalReadingRolesChecks
open AG Graph Lambda Lambda.Labelled SyntaxIncidence FanSuccessfulChains

theorem actual_nonterminal_zero_jump_roles
    (selection : OccurrenceFragmentSelection current
      FanSuccessfulReachable.concrete.site.reduce (.inl ())) :
    right≠rightVar ∧
      ∃left : ActualUnsafeMarkerCut [[.fn]] [[.fn]] original current (.atom 2) right rightEdges,
        ∃rightCut : ActualUnsafeMarkerCut [[.fn]] [[.fn]] original current (.atom 2) rightVar rightEdges,
          left.before=[] ∧rightCut.before=[] ∧
          left.after.length=3 ∧rightCut.after.length=3 ∧
          left.after≠[] ∧rightCut.after≠[] ∧left.forward=rightCut.forward ∧
          ∃ (leftSnapshot : IncomingIncidenceSnapshot current left.edge)
            (rightSnapshot : IncomingIncidenceSnapshot current rightCut.edge)
            (leftFar : CanonicalAfterFarOutput actualHistory left leftSnapshot)
            (rightFar : CanonicalAfterFarOutput actualHistory rightCut rightSnapshot),
            ∃kind : Bool,
              ProperKind current leftFar.currentProper kind ∧
              ProperKind current rightFar.currentProper kind := by
  obtain ⟨different,physical,left,rightCut,lb,rb,_la,_ra,ll,rl,_rest⟩ :=
    ActualAfterRepresentationChecks.actual_distinct_start_nonempty_after selection
  have before : left.before.length=rightCut.before.length := by rw [lb,rb]
  have more : left.after≠[] := by intro empty;rw [empty] at ll;cases ll
  obtain ⟨rm,direction,ls,rs,lf,rf,kind,lk,rk⟩ := actual_parent_cut_physical_reading_roles
    FanSuccessfulReachable.beta_matches sourceClosed actualHistory selection right_lambda_chain right_variable_chain
    physical left rightCut before more
  exact ⟨different,left,rightCut,lb,rb,ll,rl,more,rm,direction,ls,rs,lf,rf,kind,lk,rk⟩

#print axioms actual_nonterminal_zero_jump_roles
end Lamping.Checks.PhysicalReadingRolesChecks
