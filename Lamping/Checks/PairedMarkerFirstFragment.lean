import Lamping.Lamping.PairedMarkerFirstFragment
import Lamping.Checks.PairedMarkerLeafGeometry
namespace Lamping.Checks.PairedMarkerFirstFragmentChecks
open Graph Lambda Lambda.Labelled AG BetaBeforeBlockImagesChecks

/-- Actual initial graph, arbitrary legal selectors: ONE producer supplies
the marked child residual, active principal, and source FIRST fragment. The
FIRST correspondence to a separately constructed source chain is not claimed. -/
theorem actual_same_producer_first_fragment
    (sourceSelection : OccurrenceFragmentSelection source site.net (.inl ()))
    (targetSelection : OccurrenceFragmentSelection target site.reduce (.inl ())) :
    ∃ localTarget,History [[.fn]] (initLabels source.erase) localTarget ∧
      ∃ edge : BetaEdge site.net,∃ selection : SourceEdgeSelection (initLabels source.erase) site.net (.inl ()),
        SiteBetaGeometry site edge ∧
        ∃ leaf : DirectedMarkerLeafOutput [[.fn]] source (.atom 2) true [[.fn]] functionTerm.label.letters,
          ∃ paired : PairedMarkerEventGeometry leaf (initLabels source.erase) localTarget,
            selection.evalLabel edge paired.alpha=edge.principal ∧
            ∃ position : Position source.erase,∃ oldNode,
              source.subterm position.val=some oldNode ∧
              BetaNodeHistoryPreimage leaf.event.labels leaf.first position.val ∧
              selection.evalLabel edge paired.firstNode.label=(sourceSelection position).fragment.segments ∧
              accessWord site.net (selection.evalLabel edge paired.firstNode.label)=[] ∧
              selection.evalLabel edge paired.firstNode.label≠[] ∧
              ∃ newPosition : Position target.erase,newPosition.val=[.fn] ∧
                ∃ localChild,localTarget.subterm [.fn]=some localChild ∧
                  BetaPathResidual site edge
                    ((targetSelection newPosition).fragment.segments.map (plugEnd _ _).invFun)
                    (selection.evalLabel edge localChild.label) := by
  obtain ⟨localTarget,localHistory,edge,selection,geometry,leaf,paired,active,localChild,lookup,_nonempty,residual⟩ :=
    PairedMarkerLeafGeometryChecks.Physical.actual_same_producer_active_geometry targetSelection
  have matching := FunctionWrappedReachable.concrete.sourceIso.matches
    (encode_closed_matches FunctionWrappedReachable.term FunctionWrappedReachable.closed 0)
  obtain ⟨position,oldNode,oldLookup,trace,first,emptyWord,nonempty⟩ :=
    paired_marker_first_fragment leaf paired matching selected sourceSelection selection edge
  exact ⟨localTarget,localHistory,edge,selection,geometry,leaf,paired,active,position,oldNode,
    oldLookup,trace,first,emptyWord,nonempty,⟨[.fn],rfl⟩,rfl,localChild,lookup,residual⟩

#print axioms actual_same_producer_first_fragment
end Lamping.Checks.PairedMarkerFirstFragmentChecks
