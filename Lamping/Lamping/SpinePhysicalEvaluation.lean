import Lamping.Lamping.PairedMarkerSpineReannotation
import Lamping.Lamping.PairedMarkerDirectedEvaluation
import Lamping.Lamping.BetaChainEvaluatedResiduals

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

private theorem interpret_flatten (atoms : Nat → List (Endpoint g))
    (overWord underWord : List (Endpoint g)) (forward : Bool) (pieces : List (List Letter)) :
    interpretReadLetters atoms overWord underWord forward pieces.flatten=
      (pieces.map (interpretReadLetters atoms overWord underWord forward)).flatten := by
  induction pieces with
  | nil => rfl
  | cons word pieces ih =>
    rw [List.flatten_cons,interpretReadLetters_append,List.map_cons,List.flatten_cons,ih]
end

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Graph.Label signature} {i : Nat}
variable {site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V)}

/-- The SAME whole-chain producer's actual member is the local CURRENT
node of the GIVEN spine. Its full oriented value retains every frame tail. -/
theorem EvaluatedChainResiduals.spine_head_physical_fold
    {root : B} {source target localTarget : LTerm} {ps F : List Path}
    {degree : Lambda.Labelled.Label} {forward : Bool} {start : Path} {es : List Path}
    {chain : PrerequisiteChain target start es} (member : {p : Path // p∈es})
    {beforeLabels : List (Option Lambda.Labelled.Label)} {current : LTerm}
    {spine : DirectedMarkerSpine F source degree forward ps target beforeLabels member.val}
    {lookup : target.subterm member.val=some current}
    {leaf : DirectedMarkerLeafOutput F source degree forward ps (current.label.readLetters forward)}
    {snapshot : IncomingIncidenceSnapshot target member.val}
    (geometry : SpineIncidenceProvenance F source degree forward spine lookup leaf snapshot)
    (localHistory : History ps (initLabels source.erase) localTarget)
    {edge : BetaEdge site.net}
    {selection : SourceEdgeSelection (initLabels source.erase) site.net root}
    {targetSelection : OccurrenceFragmentSelection target site.reduce root}
    (evaluation : EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection chain) :
    ∃paired : PairedSpineReannotation geometry localHistory (erase_initLabels source.erase).symm,
      evaluation.node member=paired.current ∧
      orientPhysical forward (selection.evalLabel edge (evaluation.node member).label)=
        orientPhysical forward (selection.evalLabel edge paired.base.current.label)++
          (paired.localTailPieces.map
            (interpretReadLetters selection.atomWord edge.principal edge.reverseRoute forward)).flatten ∧
      ExactPhysicalDirectedFormula selection edge paired.base.middle leaf.site paired.base.alpha forward
        paired.base.firstNode paired.base.lastNode paired.base.marker paired.base.current := by
  obtain ⟨paired⟩ := geometry.paired_reannotation localHistory (erase_initLabels source.erase).symm
  have same : evaluation.node member=paired.current :=
    Option.some.inj ((evaluation.lookup member).symm.trans paired.currentLookup)
  have interpreted := congrArg
    (interpretReadLetters selection.atomWord edge.principal edge.reverseRoute forward) paired.wordFold
  have full : orientPhysical forward (selection.evalLabel edge (evaluation.node member).label)=
      orientPhysical forward (selection.evalLabel edge paired.base.current.label)++
        (paired.localTailPieces.map
          (interpretReadLetters selection.atomWord edge.principal edge.reverseRoute forward)).flatten := by
    rw [same]
    simpa only [interpretReadLetters_append,interpret_flatten,SourceEdgeSelection.interpret_read_label]
      using interpreted
  exact ⟨paired,same,full,exact_directed_formula_physical selection edge paired.base.formula⟩

/-- Obtain ONE real producer, use its successful WHOLE-chain member, and
decompose that actual local head. No singleton head chain or target REP is assumed. -/
theorem PathSite.beta_spine_head_physical_fold
    (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
    {root : B} {source target : LTerm} {ps F : List Path} {marked : Marked}
    {degree : Lambda.Labelled.Label} {forward : Bool} {start : Path} {es : List Path}
    (closed : Closed source.erase) (matching : Matches site.net root source.erase)
    (inputs : RootInputs site.net root)
    {boundary : B→Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {heights : B→Int} (balance : IndexedLevelBalance site.net heights) (rootDepth : heights root=0)
    (transparency : Transparency site.net root)
    (relative : Marked.RelativeHistory ps (Marked.mark (site.betaSyntaxFiber root source.erase) source.erase) marked)
    (normal : Marked.Normal marked) (history : History ps source target)
    (targetSelection : OccurrenceFragmentSelection target site.reduce root)
    (chain : PrerequisiteChain target start es) (member : {p : Path // p∈es})
    {beforeLabels : List (Option Lambda.Labelled.Label)} {current : LTerm}
    {spine : DirectedMarkerSpine F source degree forward ps target beforeLabels member.val}
    {lookup : target.subterm member.val=some current}
    {leaf : DirectedMarkerLeafOutput F source degree forward ps (current.label.readLetters forward)}
    {snapshot : IncomingIncidenceSnapshot target member.val}
    (geometry : SpineIncidenceProvenance F source degree forward spine lookup leaf snapshot) :
    ∃localTarget,∃localHistory : History ps (initLabels source.erase) localTarget,
      ∃edge : BetaEdge site.net,
        ∃selection : SourceEdgeSelection (initLabels source.erase) site.net root,
          SiteBetaGeometry site edge ∧
          ∃evaluation : EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection chain,
            ∃paired : PairedSpineReannotation geometry localHistory (erase_initLabels source.erase).symm,
              evaluation.node member=paired.current ∧
              orientPhysical forward (selection.evalLabel edge (evaluation.node member).label)=
                orientPhysical forward (selection.evalLabel edge paired.base.current.label)++
                  (paired.localTailPieces.map
                    (interpretReadLetters selection.atomWord edge.principal edge.reverseRoute forward)).flatten ∧
              ExactPhysicalDirectedFormula selection edge paired.base.middle leaf.site paired.base.alpha forward
                paired.base.firstNode paired.base.lastNode paired.base.marker paired.base.current ∧
              BetaPathResidual site edge
                ((targetSelection (actualChainPosition chain member)).fragment.segments.map (plugEnd _ _).invFun)
                (selection.evalLabel edge (evaluation.node member).label) ∧
              selection.evalLabel edge (evaluation.node member).label≠[] := by
  obtain ⟨localTarget,localHistory,_erase,_targetMatching,edge,selection,siteGeometry,all⟩ :=
    site.beta_evaluated_chain_residuals closed matching inputs flow positive balance rootDepth transparency
      relative normal history targetSelection
  obtain ⟨evaluation⟩ := all chain
  obtain ⟨paired,same,full,formula⟩ := evaluation.spine_head_physical_fold member geometry localHistory
  exact ⟨localTarget,localHistory,edge,selection,siteGeometry,evaluation,paired,same,full,formula,
    evaluation.residual member,evaluation.nonempty member⟩

end
#print axioms EvaluatedChainResiduals.spine_head_physical_fold
#print axioms PathSite.beta_spine_head_physical_fold
end Lamping.AG
