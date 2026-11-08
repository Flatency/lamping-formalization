import Lamping.Lamping.BetaFiberFamilies
import Lamping.Checks.BetaFiberDegrees
import Lamping.Lamping.InitialFullIndependence
import Lamping.Lamping.InitialTransparency
namespace Lamping.Checks.BetaFiberFamilies
open AG Graph Lambda Lambda.Labelled
private abbrev current := initLabels identityApp
private theorem closed : Closed current.erase := ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
private abbrev prior := ParallelHistory.nil current.erase

/-- A real physical beta site supplies its actual labelled target and SAME
old-fiber schedule. All source semantics and REP are constructed internally. -/
theorem actual_physical_beta_projects_complete_family :
    ∃ next : LTerm,∃ step : ParallelStep
      (actualBetaSite.betaSyntaxFiber (.inl ()) current.erase) current.erase next.erase,
      History step.paths current next ∧Matches actualBetaSite.reduce (.inl ()) next.erase ∧
      CompleteFamilyStep prior step ∧CompleteDerivation (prior.append (.single step)) := by
  have matching : Matches actualBetaSite.net (.inl ()) current.erase :=
    betaEncodingIso.matches (encode_closed_matches identityApp closed 0)
  obtain ⟨selection,joint,_degrees⟩ := BetaFiberDegrees.actual_fiber_iff_lambda_degree
  obtain ⟨flow⟩ := encode_flowBalance identityApp 0
  obtain ⟨balance⟩ := encode_indexed_balance identityApp 0
  have inputs := betaEncodingIso.rootInputs (encode_closed_independence identityApp closed 0).rootInputs
  have transparent := betaEncodingIso.transparency (encode_closed_transparency identityApp closed 0)
  have positive : actualBetaSite.betaSyntaxFiber (.inl ()) current.erase≠[] := by
    intro empty
    have member := BetaFiberDegrees.actual_root_member
    rw [empty] at member
    cases member
  obtain ⟨next,step,labelled,newMatches,completeFamily⟩ :=
    actualBetaSite.beta_nonempty_family_projection (init_is_INIT identityApp) closed prior (.nil current)
      matching inputs (betaEncodingIso.flowBalance flow) rfl (betaEncodingIso.indexed_balance balance) rfl
      transparent selection joint.1 positive
  refine ⟨next,step,labelled,newMatches,completeFamily,?_⟩
  exact actualBetaSite.beta_extend_complete_derivation (init_is_INIT identityApp) closed prior (.nil current)
    (.nil _) matching selection joint.1 positive step

/-- An empty physical fiber can never be silently promoted to a nonempty
CompleteFamilyStep, regardless of its complete-development schedule. -/
theorem empty_fiber_is_not_a_family_step {m t u : Term} (history : ParallelHistory m t)
    (step : ParallelStep [] t u) : ¬CompleteFamilyStep history step := by
  intro complete
  exact complete.nonempty rfl

#print axioms PathSite.beta_fiber_iff_historical_family
#print axioms PathSite.beta_complete_family_step
#print axioms PathSite.beta_extend_complete_derivation
#print axioms PathSite.beta_nonempty_family_projection
#print axioms actual_physical_beta_projects_complete_family
#print axioms empty_fiber_is_not_a_family_step
end Lamping.Checks.BetaFiberFamilies
