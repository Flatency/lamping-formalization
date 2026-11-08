import Lamping.Lamping.FanControlRootComparison
import Lamping.Lamping.FanControlChainRepresentation
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {op : Op} {i j : Nat} {lt : i<j}
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Label signature}
variable (site : PathSite (.fanAction op i j lt) kept (B:=B) (W:=W) (V:=V))

/-- This is local invariance of the existing Aux proposition for a control
passive node. It asserts neither the proposition at the source nor fan-lambda
preservation, and changes no undefined-endpoint semantics. -/
theorem PathSite.fan_control_auxiliary_separation
    (control : op=.fan ∨op=.cro ∨op=.bra)
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
    site.fan_control_occurrence_equality control flow root positive sourceMatches targetMatches
      principal (source a) (target a) (source b) (target b)
  constructor
  · intro invariant a b first second label distinct
    exact invariant a b first second label (fun same=>distinct ((pieces a b).mp same))
  · intro invariant a b first second label distinct
    exact invariant a b first second label (fun same=>distinct ((pieces a b).mpr same))

theorem PathSite.fan_control_joint_representation
    (control : op=.fan ∨op=.cro ∨op=.bra)
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
    (site.fan_control_chain_invariant control flow root positive closed sourceMatches targetMatches
      principal source target)
    (site.fan_control_auxiliary_separation control flow root positive closed sourceMatches targetMatches
      principal source target)
end
end Lamping.AG
