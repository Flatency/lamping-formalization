import Lamping.Lamping.BetaFiberDegrees
import Lamping.Checks.JointRepresentationTransport
import Lamping.Checks.DegreeFamily
namespace Lamping.Checks.BetaFiberDegrees
open AG Graph Lambda Lambda.Labelled
private abbrev current := initLabels identityApp
private theorem closed : Closed current.erase := ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
private def redex : RedexOcc current.erase := ⟨[],_,rfl,True.intro⟩
private theorem matching : Matches actualBetaSite.net (.inl ()) current.erase :=
  betaEncodingIso.matches (encode_closed_matches identityApp closed 0)

/-- Reuse the independently checked real two-segment source fragment, then
recover membership by the NEW literal connection/principal/pair reflection. -/
theorem actual_root_member : []∈actualBetaSite.betaSyntaxFiber (.inl ()) current.erase := by
  obtain ⟨appId,body,arg,lookup,fragment,principal,_length⟩ :=
    DegreeFamily.P06SelectedDegreePhysical.actual_selected_degree_has_the_fixed_principal
  obtain ⟨source⟩ := matching.actual_redex_access redex
  obtain ⟨env,port,atParent⟩ := SourceSubterm.of_lookup current lookup [] .external
  let occurrence : OccurrenceFragment current actualBetaSite.net (.inl ()) [.fn] :=
    ⟨.lam (.atom 1) body,env,.appFn appId,atParent.append (.fn .nil),fragment⟩
  have literal := source.occurrence_fragment_segments matching lookup occurrence
  have same : source.connection.edges=Paths.encodedBetaOccurrence.principal := literal.symm.trans principal
  have pair := source.connection.beta_pair_of_principal Paths.encodedBetaOccurrence same
  exact (source.physical_selection_iff actualBetaSite.net (.inl ()) current.erase
    (.inr (.inl ())) (.inr (.inr ())) matching).mpr pair

/-- Actual initial semantics and nontrivial carrier transport supply REP;
no representation/fiber/degree oracle is supplied to the conditional top. -/
theorem actual_fiber_iff_lambda_degree :
    ∃ selection : OccurrenceFragmentSelection current actualBetaSite.net (.inl ()),
      JointRepresentation closed selection ∧
      ∀ candidate : RedexOcc current.erase,
        candidate.val∈actualBetaSite.betaSyntaxFiber (.inl ()) current.erase ↔
          current.degreeAt candidate.val=some (.atom 1) := by
  obtain ⟨_source,selection,_initial,joint,_mapped⟩ :=
    JointRepresentationTransport.actual_beta_carrier_joint
  refine ⟨selection,joint,?_⟩
  intro candidate
  exact actualBetaSite.beta_fiber_iff_degree closed matching selection joint.1 redex actual_root_member candidate

#print axioms PathSite.beta_fiber_iff_degree
#print axioms actual_root_member
#print axioms actual_fiber_iff_lambda_degree
end Lamping.Checks.BetaFiberDegrees
