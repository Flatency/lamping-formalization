import Lamping.Lamping.JointRepresentationTransport
import Lamping.Lamping.InitialJointRepresentation
import Lamping.Lamping.BetaEncodingIso
namespace Lamping.Checks.JointRepresentationTransport
open AG Graph Lambda Lambda.Labelled
private abbrev current := initLabels identityApp
private theorem closed : Closed current.erase :=
  ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩

/-- A concrete closed I I encoding and its genuine five-node carrier
renaming supply both selectors and the source invariant internally. -/
theorem actual_beta_carrier_joint :
    ∃ source : OccurrenceFragmentSelection current identityAppNet (.inl ()),
    ∃ target : OccurrenceFragmentSelection current actualBetaSite.net (.inl ()),
      JointRepresentation closed source ∧JointRepresentation closed target ∧
      ∀ p,(target p).fragment.segments=(source p).fragment.segments.map betaEncodingIso.ends := by
  have matching : Matches identityAppNet (.inl ()) current.erase :=
    encode_closed_matches identityApp ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩ 0
  obtain ⟨source,initial⟩ := encode_initial_joint_realization current closed (init_is_INIT identityApp) 0
  obtain ⟨target⟩ := (betaEncodingIso.matches matching).occurrence_fragment_selection closed
  refine ⟨source,target,initial,?_,?_⟩
  · exact (betaEncodingIso.joint_representation matching closed source target).mpr initial
  · intro p
    exact betaEncodingIso.occurrence_fragment_segments matching (source p) (target p)

#print axioms NetIso.occurrence_fragment_segments
#print axioms NetIso.occurrence_fragment_equality
#print axioms NetIso.chain_representation
#print axioms NetIso.joint_representation
#print axioms actual_beta_carrier_joint
end Lamping.Checks.JointRepresentationTransport
