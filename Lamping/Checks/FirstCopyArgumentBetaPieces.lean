import Lamping.Lamping.FirstCopyArgumentBetaPieces
import Lamping.Checks.FirstCopyArgumentAuxInputs

namespace Lamping.Checks.FirstCopyArgumentBetaPiecesChecks
open Graph Lambda Lambda.Labelled AG
open FirstCopyArgumentAuxInputsChecks

/-- The SAME original INIT has a genuine nonempty prefix before this FIRST
relative event. The two current copied lambda positions are distinct. -/
theorem actual_distinct_context : INIT original ∧¬INIT source ∧
    History [[.fn,.body],[]] original target ∧
    target.subterm leftStart=some newK ∧target.subterm rightStart=some newK ∧
    leftStart≠rightStart ∧PrerequisiteChain target leftStart es ∧
    PrerequisiteChain target rightStart fs :=
  ⟨initial,sourceNotInit,prefixHistory.append event.final_history,leftLookup,rightLookup,
    by decide,leftChain,rightChain⟩

/-- Directly consume the complete NEW physical theorem at DISTINCT actual
ARG positions, arbitrary target selectors. Physical site/normal fibre and
SOURCE Joint remain honest hypotheses, not a claimed concrete realization. -/
theorem actual_distinct_complete_pieces
    {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
    {kept : K→Graph.Label signature} {i : Nat}
    (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V)) {root : B}
    (matching : Matches site.net root source.erase) (inputs : RootInputs site.net root)
    {boundary : B→Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {heights : B→Int} (balance : IndexedLevelBalance site.net heights) (rootDepth : heights root=0)
    (transparency : Transparency site.net root)
    {endpoint : Marked}
    (relative : Marked.RelativeHistory [[]]
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
    site.beta_first_copy_argument_pieces sourceClosed initial prefixHistory event selected
      (by rfl : event.argument=.lam (.atom 11) (.var (.atom 12) 0))
      (leftParent:=[.fn]) (rightParent:=[.arg]) (by rfl) (by rfl)
      leftLookup rightLookup leftChain rightChain iso leftAfterSafe rightAfterSafe
      matching inputs flow positive balance rootDepth transparency relative normal sourceSelection representation
      (leftSelection ⟨leftStart,rfl⟩) (rightSelection ⟨rightStart,rfl⟩)
  exact ⟨edge,geometry,selection.evalLabel edge ln.label,nonempty,leftResidual,
    evaluations ▸ rightResidual,pieces⟩

#print axioms actual_distinct_context
#print axioms actual_distinct_complete_pieces
end Lamping.Checks.FirstCopyArgumentBetaPiecesChecks
