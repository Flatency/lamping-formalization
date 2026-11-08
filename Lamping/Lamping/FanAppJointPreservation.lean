import Lamping.Lamping.FanAppChainRepresentationReflection
import Lamping.Lamping.FanAppAuxiliaryPreservation
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.fanAction .app i j lt) kept (B:=B) (W:=W) (V:=V))
/-- Conditional one-event Joint preservation, using the SAME actual selections
and explicit SOURCE IH in both clauses. No actual SOURCE Joint truth is asserted. -/
theorem PathSite.fan_app_joint_representation_preserve
    {current : LTerm} {root : B} {boundary : B→Bool}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (inputs : RootInputs site.net root) (principal : SiteActionPrincipal site)
    (closed : Closed current.erase)
    (source : OccurrenceFragmentSelection current site.net root)
    (target : OccurrenceFragmentSelection current site.reduce root)
    (sourceJoint : JointRepresentation closed source) : JointRepresentation closed target :=
  ⟨site.fan_app_chain_invariant_preserve sourceMatches targetMatches flow positive inputs principal
      closed source target sourceJoint.1,
    site.fan_app_auxiliary_separation_preserve sourceMatches targetMatches flow positive inputs principal
      closed source target sourceJoint⟩
end
end Lamping.AG
#print axioms Lamping.AG.PathSite.fan_app_joint_representation_preserve