import Lamping.Lamping.SuccessfulChainRepresentationTransport
import Lamping.Lamping.FanControlOccurrenceComparison
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {op : Op} {i j : Nat} {lt : i<j}
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Label signature}
variable (site : PathSite (.fanAction op i j lt) kept (B:=B) (W:=W) (V:=V))

theorem PathSite.fan_control_chain_representation
    (control : op=.fan ∨op=.cro ∨op=.bra)
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
  exact site.fan_control_nonroot_occurrence_equality control flow root positive
    sourceMatches targetMatches principal leftNonroot rightNonroot
    (source a) (target a) (source b) (target b)

theorem PathSite.fan_control_chain_invariant
    (control : op=.fan ∨op=.cro ∨op=.bra)
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
  exact site.fan_control_nonroot_occurrence_equality control flow root positive
    sourceMatches targetMatches principal leftNonroot rightNonroot
    (source a) (target a) (source b) (target b)
end
end Lamping.AG
