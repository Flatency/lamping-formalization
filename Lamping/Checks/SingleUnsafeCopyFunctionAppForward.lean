import Lamping.Lamping.SingleUnsafeCopyFunctionAppForward
import Lamping.Checks.SingleUnsafeCopyFunctionAppInputs

namespace Lamping.Checks.SingleUnsafeCopyFunctionAppForwardChecks
open Graph Lambda Lambda.Labelled AG
open SingleUnsafeCopyFunctionAppInputsChecks

/-- Actual distinct three-READ chains, with nonempty BEFORE, AFTER and OLD
prefix. Physical realization and SOURCE chain REP are honest hypotheses. -/
theorem actual_distinct_full_ordered_forward
    {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
    {kept : K→Graph.Label signature} {i : Nat}
    (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V)) {root : B}
    (matching : Matches site.net root source.erase) (inputs : RootInputs site.net root)
    {boundary : B→Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {heights : B→Int} (balance : IndexedLevelBalance site.net heights) (rootDepth : heights root=0)
    (transparency : Transparency site.net root)
    {endpoint : Marked}
    (relative : Marked.RelativeHistory [[.fn],[.arg]]
      (Marked.mark (site.betaSyntaxFiber root source.erase) source.erase) endpoint)
    (normal : Marked.Normal endpoint)
    (sourceSelection : OccurrenceFragmentSelection source site.net root)
    (representation : ChainRepresentationInvariant sourceClosed sourceSelection)
    (targetSelection : OccurrenceFragmentSelection target site.reduce root) :
    SameChainRepresentation targetSelection leftChain rightChain := by
  obtain ⟨iso⟩ := currentIso
  exact site.beta_single_unsafe_copy_function_app_forward sourceClosed initial prefixHistory event selected sourceSafe
    (leftParent:=[.fn]) (rightParent:=[.arg]) (by rfl) (by rfl)
    leftLookup rightLookup leftChain rightChain iso
    (by decide) (by decide)
    leftOtherSafe rightOtherSafe leftFirstSafe rightFirstSafe
    matching inputs flow positive balance rootDepth transparency relative normal sourceSelection representation
    targetSelection

#print axioms PathSite.beta_single_unsafe_copy_function_app_forward
#print axioms actual_distinct_full_ordered_forward
end Lamping.Checks.SingleUnsafeCopyFunctionAppForwardChecks
