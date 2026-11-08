import Lamping.Lamping.InheritedForwardHeads
import Lamping.Lamping.SameEventBetaPieces

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

private theorem map_injective {A C : Type} {f : A→C} (injective : Function.Injective f)
    {xs ys : List A} (same : xs.map f=ys.map f) : xs=ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => cases same
    | cons y ys =>
      obtain ⟨head,tail⟩ := List.cons.inj same
      rw [injective head,ih tail]

private theorem actual_function_departure
    {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} {root : B}
    (lookup : target.subterm p=some (.app stamp fn arg))
    (child : OccurrenceFragment target g root (p++[.fn])) :
    SourceDeparture (.app stamp fn arg) .fn
      (sourceEdge child.environment child.context child.term).fromPort := by
  obtain ⟨env,ctx,outer⟩ := SourceSubterm.of_lookup target lookup [] .external
  have actual : SourceSubterm [] .external target (p++[.fn]) env (.appFn stamp) fn :=
    outer.append (.fn .nil)
  have context := (child.occurrence.same_occurrence actual).2.1
  have fromEq : (sourceEdge child.environment child.context child.term).fromPort=child.context := by
    cases child.term <;> rfl
  rw [fromEq,context]
  exact .fn

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Graph.Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))

/-- SAME actual TRUE creation, followed by genuinely uncreated inherited
turns. ONE producer gives complete CURRENT pieces, without a final-event
restriction or cancellation of an unknown continuation. -/
theorem PathSite.beta_single_creation_forward_pieces
    {root : B} {source target : LTerm} {ps F : List Path} {marked : Marked}
    {leftEdge rightEdge leftReader rightReader : Path} {leftNode rightNode : LTerm}
    {leftBefore rightBefore : List (Option Lambda.Labelled.Label)}
    (closed : Closed source.erase) (matching : Matches site.net root source.erase)
    (inputs : RootInputs site.net root)
    {boundary : B→Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {heights : B→Int} (balance : IndexedLevelBalance site.net heights) (rootDepth : heights root=0)
    (transparency : Transparency site.net root)
    (relative : Marked.RelativeHistory ps (Marked.mark (site.betaSyntaxFiber root source.erase) source.erase) marked)
    (normal : Marked.Normal marked) (history : History ps source target)
    (leftSpine : DirectedMarkerSpine F source degree true ps target leftBefore leftEdge)
    (rightSpine : DirectedMarkerSpine F source degree true ps target rightBefore rightEdge)
    (leftLookup : target.subterm leftEdge=some leftNode)
    (rightLookup : target.subterm rightEdge=some rightNode)
    (left : DirectedMarkerLeafOutput F source degree true ps (leftNode.label.readLetters true))
    (right : DirectedMarkerLeafOutput F source degree true ps (rightNode.label.readLetters true))
    {leftSnapshot : IncomingIncidenceSnapshot target leftEdge}
    {rightSnapshot : IncomingIncidenceSnapshot target rightEdge}
    (leftGeometry : SpineIncidenceProvenance F source degree true leftSpine leftLookup left leftSnapshot)
    (rightGeometry : SpineIncidenceProvenance F source degree true rightSpine rightLookup right rightSnapshot)
    (leftSingle : leftGeometry.creationFrames.length=1)
    (rightSingle : rightGeometry.creationFrames.length=1)
    (samePre : left.pre=right.pre) (sameSite : left.site=right.site)
    (leftRead : PrerequisiteReadsDirected target leftReader leftEdge true)
    (rightRead : PrerequisiteReadsDirected target rightReader rightEdge true)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (prefixHistory : History prior original source) (initial : INIT original)
    (sourceSelection : OccurrenceFragmentSelection source site.net root)
    (representation : ChainRepresentationInvariant closed sourceSelection)
    (sameWord : leftNode.label.readLetters true=rightNode.label.readLetters true)
    (leftChild : OccurrenceFragment target site.reduce root (leftReader++[.fn]))
    (rightChild : OccurrenceFragment target site.reduce root (rightReader++[.fn])) :
    ∃localTarget,History ps (initLabels source.erase) localTarget ∧
      ∃edge : BetaEdge site.net,∃selection : SourceEdgeSelection (initLabels source.erase) site.net root,
        SiteBetaGeometry site edge ∧
        ∃ln rn,localTarget.subterm (leftReader++[.fn])=some ln ∧
          localTarget.subterm (rightReader++[.fn])=some rn ∧
          selection.evalLabel edge ln.label=selection.evalLabel edge rn.label ∧
          selection.evalLabel edge ln.label≠[] ∧selection.evalLabel edge rn.label≠[] ∧
          BetaPathResidual site edge (leftChild.fragment.segments.map (plugEnd _ _).invFun)
            (selection.evalLabel edge ln.label) ∧
          BetaPathResidual site edge (rightChild.fragment.segments.map (plugEnd _ _).invFun)
            (selection.evalLabel edge rn.label) ∧
          leftChild.fragment.segments=rightChild.fragment.segments := by
  obtain ⟨localTarget,localHistory,_erase,_targetMatches,edge,selection,geometry,all⟩ :=
    site.beta_evaluated_child_residuals closed matching inputs flow positive balance rootDepth transparency
      relative normal history
  obtain ⟨lp⟩ := paired_marker_leaf_geometry left localHistory (erase_initLabels source.erase).symm
  obtain ⟨rp⟩ := paired_marker_leaf_geometry right localHistory (erase_initLabels source.erase).symm
  have heads := paired_marker_same_event_forward_evaluations left right lp rp samePre sameSite matching
    selected sourceSafe prefixHistory initial closed sourceSelection representation selection edge sameWord
  obtain ⟨la,lf,larg,leftParent,leftCoordinate⟩ := leftRead.forward_parent
  obtain ⟨ra,rf,rarg,rightParent,rightCoordinate⟩ := rightRead.forward_parent
  obtain ⟨lc,atLeft,_leftErase,leftNonempty,leftResidual⟩ :=
    all leftReader .fn _ leftParent leftChild (actual_function_departure leftParent leftChild)
  obtain ⟨rc,atRight,_rightErase,rightNonempty,rightResidual⟩ :=
    all rightReader .fn _ rightParent rightChild (actual_function_departure rightParent rightChild)
  have leftAtEdge : localTarget.subterm leftEdge=some lc := by rw [leftCoordinate];exact atLeft
  have rightAtEdge : localTarget.subterm rightEdge=some rc := by rw [rightCoordinate];exact atRight
  have leftTrace := (leftGeometry.single_creation_suffix leftSingle).2.reannotate
    (otherLabels:=lp.suffix) lp.targetErase.symm
  have rightTrace := (rightGeometry.single_creation_suffix rightSingle).2.reannotate
    (otherLabels:=rp.suffix) rp.targetErase.symm
  obtain ⟨lo,loLookup,leftLabel⟩ := leftTrace.source_label leftAtEdge
  obtain ⟨ro,roLookup,rightLabel⟩ := rightTrace.source_label rightAtEdge
  have leftOld := Option.some.inj (loLookup.symm.trans lp.lookup)
  have rightOld := Option.some.inj (roLookup.symm.trans rp.lookup)
  have leftLocal : lc.label=lp.current.label := leftLabel.symm.trans (congrArg LTerm.label leftOld)
  have rightLocal : rc.label=rp.current.label := rightLabel.symm.trans (congrArg LTerm.label rightOld)
  have evaluations : selection.evalLabel edge lc.label=selection.evalLabel edge rc.label := by
    rw [leftLocal,rightLocal];exact heads
  have raw := leftResidual.target_unique site geometry rightResidual evaluations
  have pieces := map_injective (plugEnd _ _).symm.injective raw
  exact ⟨localTarget,localHistory,edge,selection,geometry,lc,rc,atLeft,atRight,evaluations,
    leftNonempty,rightNonempty,leftResidual,rightResidual,pieces⟩
end

#print axioms PathSite.beta_single_creation_forward_pieces
end Lamping.AG
