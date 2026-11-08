import Lamping.Lamping.UnaryOccurrenceDispatcher
import Lamping.Lamping.SuccessfulChainRepresentationTransport
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))
theorem PathSite.unary_chain_representation
    (action : IsAction s)
    (unary : s.active≠.fan)
    {directions : B→Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase)
    (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site)
    (source : OccurrenceFragmentSelection current site.net root)
    (target : OccurrenceFragmentSelection current site.reduce root)
    (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right) :
    SameChainRepresentation target first second ↔SameChainRepresentation source first second := by
  apply successful_chain_representation_transport source target
  intro a b leftNonroot rightNonroot
  exact site.unary_nonroot_occurrence_equality action unary flow root positive
    sourceMatches targetMatches principal leftNonroot rightNonroot
    (source a) (target a) (source b) (target b)

theorem PathSite.unary_chain_invariant
    (action : IsAction s)
    (unary : s.active≠.fan)
    {directions : B→Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (closed : Closed current.erase)
    (sourceMatches : Matches site.net root current.erase)
    (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site)
    (source : OccurrenceFragmentSelection current site.net root)
    (target : OccurrenceFragmentSelection current site.reduce root) :
    ChainRepresentationInvariant closed target ↔ChainRepresentationInvariant closed source := by
  apply successful_chain_invariant_transport closed source target
  intro a b leftNonroot rightNonroot
  exact site.unary_nonroot_occurrence_equality action unary flow root positive
    sourceMatches targetMatches principal leftNonroot rightNonroot
    (source a) (target a) (source b) (target b)

/-- This is local invariance of the corrected successful-domain Aux proposition for a unary
action. It asserts neither the proposition at the source nor fan-lambda
preservation, and preserves the current successful-chain endpoint domain. -/
theorem PathSite.unary_auxiliary_separation
    (action : IsAction s)
    (unary : s.active≠.fan)
    {directions : B→Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (closed : Closed current.erase)
    (sourceMatches : Matches site.net root current.erase)
    (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site)
    (source : OccurrenceFragmentSelection current site.net root)
    (target : OccurrenceFragmentSelection current site.reduce root) :
    AuxiliarySeparation closed target ↔AuxiliarySeparation closed source := by
  have pieces (a b : SyntaxIncidence.Edge current) :
      (target a).fragment.segments=(target b).fragment.segments ↔
      (source a).fragment.segments=(source b).fragment.segments :=
    site.unary_occurrence_equality action unary flow root positive sourceMatches targetMatches
      principal (source a) (target a) (source b) (target b)
  constructor
  · intro invariant a b first second label distinct
    exact invariant a b first second label (fun same=>distinct ((pieces a b).mp same))
  · intro invariant a b first second label distinct
    exact invariant a b first second label (fun same=>distinct ((pieces a b).mpr same))

theorem PathSite.unary_joint_representation
    (action : IsAction s)
    (unary : s.active≠.fan)
    {directions : B→Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (closed : Closed current.erase)
    (sourceMatches : Matches site.net root current.erase)
    (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site)
    (source : OccurrenceFragmentSelection current site.net root)
    (target : OccurrenceFragmentSelection current site.reduce root) :
    JointRepresentation closed target ↔JointRepresentation closed source := by
  exact and_congr
    (site.unary_chain_invariant action unary flow root positive closed sourceMatches targetMatches
      principal source target)
    (site.unary_auxiliary_separation action unary flow root positive closed sourceMatches targetMatches
      principal source target)
end
end Lamping.AG

#print axioms Lamping.AG.PathSite.unary_chain_representation
#print axioms Lamping.AG.PathSite.unary_chain_invariant
#print axioms Lamping.AG.PathSite.unary_auxiliary_separation
#print axioms Lamping.AG.PathSite.unary_joint_representation
