import Lamping.Lamping.CancellationJointRepresentation
namespace Lamping.Checks.CancellationJointRepresentation
open AG Graph Lambda Lambda.Labelled
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))

/-- Forward use returns both target clauses; source and target matching and
flow remain explicit. This is not a closed reachable crossing fixture. -/
theorem both_target_clauses (cancel : IsCancellation s) {boundary : B → Bool}
    (flow : FlowBalance site.net boundary) (root : B) (positive : boundary root=true)
    {current : LTerm} (closed : Closed current.erase)
    (sourceMatches : Matches site.net root current.erase)
    (targetMatches : Matches site.reduce root current.erase)
    (source : OccurrenceFragmentSelection current site.net root)
    (target : OccurrenceFragmentSelection current site.reduce root)
    (old : JointRepresentation closed source) :
    ChainRepresentationInvariant closed target ∧AuxiliarySeparation closed target :=
  (site.cancellation_joint_representation cancel flow root positive closed
    sourceMatches targetMatches source target).mpr old
end
#print axioms PathSite.cancellation_chain_representation
#print axioms PathSite.cancellation_joint_representation
#print axioms both_target_clauses
end Lamping.Checks.CancellationJointRepresentation
