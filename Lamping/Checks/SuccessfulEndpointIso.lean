import Lamping.Lamping.SuccessfulEndpointIso
import Lamping.Checks.FamilyRepresentation
namespace Lamping.Checks.SuccessfulEndpointIsoChecks
open AG Graph Lambda Lambda.Labelled FamilyRepresentation

-- The already constructed two-edge ARG chain, without an invented empty chain.
theorem actual_argument_reflexive :
    SuccessfulEndpointIso term actual_closed argumentLambdaVertex argumentLambdaVertex :=
  SuccessfulEndpointIso.refl_of_chain argument_chain

theorem actual_argument_partial_iff :
    SuccessfulEndpointIso term actual_closed argumentLambdaVertex argumentLambdaVertex ↔
      PartialEndpointIso term actual_closed argumentLambdaVertex argumentLambdaVertex :=
  SuccessfulEndpointIso.iff_partial_of_left_available argument_endpoint_has_actual_chain

theorem external_has_no_success (current : LTerm) (closed : Closed current.erase)
    (vertex : SyntaxIncidence.Vertex current) :
    ¬SuccessfulEndpointIso current closed none vertex := by
  intro relation
  obtain ⟨es,chain⟩ := relation.left_available
  exact chain

theorem identity_root_not_reflexive :
    ¬SuccessfulEndpointIso identity (by change 0<1;decide) identityRootVertex identityRootVertex := by
  intro relation
  exact identity_endpoint_is_undefined relation.left_available

theorem old_undefined_status_is_not_success :
    PartialEndpointIso identity (by change 0<1;decide) none identityRootVertex ∧
    ¬SuccessfulEndpointIso identity (by change 0<1;decide) none identityRootVertex :=
  ⟨external_and_identity_root_have_same_partial_status.1,external_has_no_success _ _ _⟩

theorem no_global_reflexivity :
    ¬∀ vertex : SyntaxIncidence.Vertex identity,
      SuccessfulEndpointIso identity (by change 0<1;decide) vertex vertex := by
  intro allVertices
  exact identity_root_not_reflexive (allVertices identityRootVertex)

-- Use the actual old endpoint chain as availability, then compose genuine
-- successes; trans does not add a no-chain branch during this round-trip.
theorem actual_round_trip :
    SuccessfulEndpointIso term actual_closed argumentLambdaVertex argumentLambdaVertex :=
  actual_argument_reflexive.trans actual_argument_reflexive.symm

#print axioms actual_argument_reflexive
#print axioms actual_argument_partial_iff
#print axioms external_has_no_success
#print axioms identity_root_not_reflexive
#print axioms old_undefined_status_is_not_success
#print axioms no_global_reflexivity
#print axioms actual_round_trip
end Lamping.Checks.SuccessfulEndpointIsoChecks

#print axioms Lamping.AG.SuccessfulEndpointIso.left_available
#print axioms Lamping.AG.SuccessfulEndpointIso.refl_of_chain
#print axioms Lamping.AG.SuccessfulEndpointIso.symm
#print axioms Lamping.AG.SuccessfulEndpointIso.trans
#print axioms Lamping.AG.SuccessfulEndpointIso.to_partial
#print axioms Lamping.AG.SuccessfulEndpointIso.iff_partial_of_left_available
