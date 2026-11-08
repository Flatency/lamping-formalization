import Lamping.Lamping.SafeLastCopyArgumentBetaPieces
import Lamping.Checks.SafeLastCopyArgumentAuxInputs

namespace Lamping.Checks.SafeLastCopyArgumentBetaPiecesChecks
open Graph Lambda Lambda.Labelled AG
open SafeLastCopyArgumentAuxInputsChecks

/-- One original INIT, genuinely nonempty relative OLD prefix, unsafe
middle but safe LAST, and distinct actual CURRENT copied ARG positions. -/
theorem actual_nonempty_distinct_context : INIT original ∧
    ([[.fn]] : List Path)≠[] ∧
    History [[.arg,.fn,.body],[],[.fn],[.arg]] original target ∧
    (∃node,middle.subterm [.fn,.fn,.arg]=some node ∧
      ¬node.label.OuterBarsSafe (fun x=>x≠Label.atom 6)) ∧
    target.subterm leftStart=some newK ∧target.subterm rightStart=some newK ∧
    leftStart≠rightStart ∧PrerequisiteChain target leftStart es ∧
    PrerequisiteChain target rightStart fs :=
  ⟨initial,actual_nonempty_relative_prefix,prefixHistory.append event.final_history,middleUnsafe,
    leftLookup,rightLookup,by decide,leftChain,rightChain⟩

/-- Direct complete high theorem at two DISTINCT ARG positions after the
actual nonempty event prefix. No SOURCE Joint or physical realization is
fabricated from the syntactic fixture; these are explicit conditions. -/
theorem actual_nonempty_distinct_complete_pieces
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
    (representation : JointRepresentation sourceClosed sourceSelection)
    (leftSelection rightSelection : OccurrenceFragmentSelection target site.reduce root) :
    ∃edge : BetaEdge site.net,SiteBetaGeometry site edge ∧∃block,
      block≠[] ∧
      BetaPathResidual site edge
        ((leftSelection ⟨leftStart,rfl⟩).fragment.segments.map (plugEnd _ _).invFun) block ∧
      BetaPathResidual site edge
        ((rightSelection ⟨rightStart,rfl⟩).fragment.segments.map (plugEnd _ _).invFun) block ∧
      (leftSelection ⟨leftStart,rfl⟩).fragment.segments=
        (rightSelection ⟨rightStart,rfl⟩).fragment.segments := by
  obtain ⟨iso⟩ := currentIso
  obtain ⟨localTarget,_localHistory,edge,selection,geometry,ln,rn,_leftLocal,_rightLocal,
      evaluations,nonempty,_rightNonempty,leftResidual,rightResidual,pieces⟩ :=
    site.beta_safe_last_copy_argument_pieces sourceClosed initial prefixHistory event selected
      (leftParent:=[.fn]) (rightParent:=[.arg]) (by rfl) (by rfl)
      leftLookup rightLookup leftChain rightChain iso leftAfterSafe rightAfterSafe leftLastSafe rightLastSafe
      matching inputs flow positive balance rootDepth transparency relative normal sourceSelection representation
      (leftSelection ⟨leftStart,rfl⟩) (rightSelection ⟨rightStart,rfl⟩)
  exact ⟨edge,geometry,selection.evalLabel edge ln.label,nonempty,leftResidual,
    evaluations ▸ rightResidual,pieces⟩

#print axioms actual_nonempty_distinct_context
#print axioms actual_nonempty_distinct_complete_pieces
end Lamping.Checks.SafeLastCopyArgumentBetaPiecesChecks
