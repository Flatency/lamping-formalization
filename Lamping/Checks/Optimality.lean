import Lamping.Lamping.Optimality

namespace Lamping.Checks.Optimality
open Lamping.Lambda Lamping.AG.Readback

private def identity : Term := .lam (.var 0)
private def identityApplication : Term := .app identity identity
private def duplicateIdentity : Term := .app (.lam (.app (.var 0) (.var 0))) identity

private theorem identityClosed : Closed identity :=
  Nat.zero_lt_succ 0

private theorem identityApplicationClosed : Closed identityApplication :=
  ⟨identityClosed, identityClosed⟩

private theorem duplicateIdentityClosed : Closed duplicateIdentity :=
  ⟨⟨Nat.zero_lt_succ 0, Nat.zero_lt_succ 0⟩, identityClosed⟩

private theorem identityNormal : BetaNF identity :=
  (betaNF_iff_redexPositions_nil identity).2 rfl

private theorem identityHasNF : HasNF identity :=
  ⟨identity, .refl identity, identityNormal⟩

private theorem identityApplicationHasNF : HasNF identityApplication :=
  ⟨identity, .cons (Beta.root (.var 0) identity) (.refl identity), identityNormal⟩

private theorem duplicateIdentityHasNF : HasNF duplicateIdentity :=
  ⟨identity, .cons (Beta.root (.app (.var 0) (.var 0)) identity)
    (.cons (Beta.root (.var 0) identity) (.refl identity)), identityNormal⟩

#eval
  (decide ((normalizeNeededGraph identity identityClosed identityHasNF).val.term = identity),
   decide ((normalizeNeededGraph identityApplication identityApplicationClosed
     identityApplicationHasNF).val.term = identity),
   decide ((normalizeNeededGraph duplicateIdentity duplicateIdentityClosed
     duplicateIdentityHasNF).val.term = identity))

#print axioms Lamping.Lambda.CompleteDerivation.wholeFamilyCopyUnitPlan_minimal
#print axioms Lamping.Lambda.CompleteDerivation.familyRoundEnumeration
#print axioms Lamping.AG.ExposureScheduling.finiteAuxExposure
#print axioms Lamping.AG.ExposureScheduling.FiniteAuxExposure.programBetaRecipe
#print axioms Lamping.AG.ExposureScheduling.computedGivenFamilyStage
#print axioms Lamping.AG.ExposureScheduling.finiteCompleteHistoryExecutable
#print axioms Lamping.AG.Readback.normalizeNeededGraph
#print axioms Lamping.AG.Readback.normalizeNeededGraph_reduces
#print axioms Lamping.AG.Readback.normalizeNeededGraph_spec
#print axioms Lamping.AG.Readback.normalizeNeededGraph_family_optimal

end Lamping.Checks.Optimality
