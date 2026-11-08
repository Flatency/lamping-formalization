import Lamping.Lamping.SameEventForwardHeads

namespace Lamping.Lambda.Labelled
variable {source target : LTerm}

private theorem nil_endpoints (h : History [] t u) : t=u := by cases h;rfl

theorem DirectedMarkerLeafOutput.final_target
    (leaf : DirectedMarkerLeafOutput F source degree forward ps word)
    (labels : History ps source target) (last : leaf.after=[]) : leaf.target=target := by
  have actual : History ps source leaf.target := by
    have schedule : ps=leaf.pre++[leaf.site] := by
      simpa only [last] using leaf.schedule
    exact Eq.mp (congrArg (fun qs : List Path => History qs source leaf.target) schedule.symm)
      (leaf.event.labels.append (.cons leaf.event.turn (.nil _)))
  exact actual.deterministic labels

theorem PairedMarkerEventGeometry.final_target
    {leaf : DirectedMarkerLeafOutput F source degree forward ps word}
    (paired : PairedMarkerEventGeometry leaf localSource localTarget)
    (last : leaf.after=[]) : paired.target=localTarget := by
  have suffix : History [] paired.target localTarget := by rw [←last];exact paired.suffix
  exact nil_endpoints suffix

theorem PrerequisiteReadsDirected.forward_parent
    (reading : PrerequisiteReadsDirected target reader edge true) :
    ∃stamp fn arg,target.subterm reader=some (.app stamp fn arg) ∧edge=reader++[.fn] := by
  rcases reading.1 with app|lam
  · exact app
  · obtain ⟨stamp,body,lookup,equal⟩ := lam
    have same : reader=reader++[.fn] := equal.symm.trans reading.2
    have sizes := congrArg List.length same
    simp at sizes
end Lamping.Lambda.Labelled

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

/-- ONE actual development producer, SAME final event, TRUE reading. The two
actual child residuals share its edge and selector; complete head equality
therefore identifies these literal target pieces. SOURCE REP is an IH. -/
theorem PathSite.beta_same_event_forward_pieces
    {root : B} {source target : LTerm} {ps F : List Path} {marked : Marked}
    (closed : Closed source.erase) (matching : Matches site.net root source.erase)
    (inputs : RootInputs site.net root)
    {boundary : B→Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {heights : B→Int} (balance : IndexedLevelBalance site.net heights) (rootDepth : heights root=0)
    (transparency : Transparency site.net root)
    (relative : Marked.RelativeHistory ps (Marked.mark (site.betaSyntaxFiber root source.erase) source.erase) marked)
    (normal : Marked.Normal marked) (history : History ps source target)
    (left : DirectedMarkerLeafOutput F source degree true ps leftWord)
    (right : DirectedMarkerLeafOutput F source degree true ps rightWord)
    (samePre : left.pre=right.pre) (sameSite : left.site=right.site)
    (leftLast : left.after=[]) (rightLast : right.after=[])
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (prefixHistory : History prior original source) (initial : INIT original)
    (sourceSelection : OccurrenceFragmentSelection source site.net root)
    (representation : ChainRepresentationInvariant closed sourceSelection)
    (sameWord : leftWord=rightWord)
    (leftChild : OccurrenceFragment target site.reduce root (left.reader++[.fn]))
    (rightChild : OccurrenceFragment target site.reduce root (right.reader++[.fn])) :
    ∃localTarget,History ps (initLabels source.erase) localTarget ∧
      ∃edge : BetaEdge site.net,∃selection : SourceEdgeSelection (initLabels source.erase) site.net root,
        SiteBetaGeometry site edge ∧
        ∃lp : PairedMarkerEventGeometry left (initLabels source.erase) localTarget,
          ∃rp : PairedMarkerEventGeometry right (initLabels source.erase) localTarget,
            selection.evalLabel edge lp.current.label=selection.evalLabel edge rp.current.label ∧
            selection.evalLabel edge lp.current.label≠[] ∧selection.evalLabel edge rp.current.label≠[] ∧
            BetaPathResidual site edge (leftChild.fragment.segments.map (plugEnd _ _).invFun)
              (selection.evalLabel edge lp.current.label) ∧
            BetaPathResidual site edge (rightChild.fragment.segments.map (plugEnd _ _).invFun)
              (selection.evalLabel edge rp.current.label) ∧
            leftChild.fragment.segments=rightChild.fragment.segments := by
  obtain ⟨localTarget,localHistory,_erase,_targetMatching,edge,selection,geometry,all⟩ :=
    site.beta_evaluated_child_residuals closed matching inputs flow positive balance rootDepth transparency
      relative normal history
  obtain ⟨lp⟩ := paired_marker_leaf_geometry left localHistory (erase_initLabels source.erase).symm
  obtain ⟨rp⟩ := paired_marker_leaf_geometry right localHistory (erase_initLabels source.erase).symm
  have heads := paired_marker_same_event_forward_evaluations left right lp rp samePre sameSite matching
    selected sourceSafe prefixHistory initial closed sourceSelection representation selection edge sameWord
  obtain ⟨la,lf,larg,leftParent,leftEdge⟩ := left.reading.forward_parent
  obtain ⟨ra,rf,rarg,rightParent,rightEdge⟩ := right.reading.forward_parent
  rw [left.final_target history leftLast] at leftParent
  rw [right.final_target history rightLast] at rightParent
  obtain ⟨lc,atLeft,_leftErase,leftNonempty,leftResidual⟩ :=
    all left.reader .fn _ leftParent leftChild (actual_function_departure leftParent leftChild)
  obtain ⟨rc,atRight,_rightErase,rightNonempty,rightResidual⟩ :=
    all right.reader .fn _ rightParent rightChild (actual_function_departure rightParent rightChild)
  have lpLookup : localTarget.subterm (left.reader++[.fn])=some lp.current := by
    have atFinal := Eq.mp (congrArg (fun t : LTerm => t.subterm left.edge=some lp.current)
      (lp.final_target leftLast)) lp.lookup
    exact Eq.mp (congrArg (fun p : Path => localTarget.subterm p=some lp.current) leftEdge) atFinal
  have rpLookup : localTarget.subterm (right.reader++[.fn])=some rp.current := by
    have atFinal := Eq.mp (congrArg (fun t : LTerm => t.subterm right.edge=some rp.current)
      (rp.final_target rightLast)) rp.lookup
    exact Eq.mp (congrArg (fun p : Path => localTarget.subterm p=some rp.current) rightEdge) atFinal
  have lcEq := Option.some.inj (atLeft.symm.trans lpLookup)
  have rcEq := Option.some.inj (atRight.symm.trans rpLookup)
  subst lc
  subst rc
  have raw := leftResidual.target_unique site geometry rightResidual heads
  have pieces := map_injective (plugEnd _ _).symm.injective raw
  exact ⟨localTarget,localHistory,edge,selection,geometry,lp,rp,heads,leftNonempty,rightNonempty,
    leftResidual,rightResidual,pieces⟩
end

#print axioms DirectedMarkerLeafOutput.final_target
#print axioms PairedMarkerEventGeometry.final_target
#print axioms PrerequisiteReadsDirected.forward_parent
#print axioms PathSite.beta_same_event_forward_pieces
end Lamping.AG
