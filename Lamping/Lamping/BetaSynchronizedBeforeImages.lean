import Lamping.Lamping.BetaBeforeBlockImages
import Lamping.Lamping.MarkerSourceChainRepresentation
import Lamping.Lamping.ActualUnsafeMarkerLeaves
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Graph.Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))

/-- Two actual same-direction cuts share ONE physical beta edge producer.
The source REP is an induction hypothesis. No old-chain iso or physical
BEFORE equality is supplied; both are conclusions of the actual producers. -/
theorem PathSite.beta_synchronized_before_images
    {root : B} {source target original : LTerm} {ps prior F : List Path} {marked n : Marked}
    {degree : Labelled.Label}
    (closed : Closed source.erase) (matching : Matches site.net root source.erase)
    (inputs : RootInputs site.net root)
    {boundary : B→Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {heights : B→Int} (balance : IndexedLevelBalance site.net heights) (rootDepth : heights root=0)
    (transparency : Transparency site.net root)
    (relative : Marked.RelativeHistory ps (Marked.mark (site.betaSyntaxFiber root source.erase) source.erase) marked)
    (normal : Marked.Normal marked) (history : History ps source target)
    (old : Marked.RelativeOldHistory F ps (Marked.mark F source.erase) n)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (prefixHistory : History prior original source) (initial : INIT original)
    (sourceSelection : OccurrenceFragmentSelection source site.net root)
    (targetSelection : OccurrenceFragmentSelection target site.reduce root)
    (representation : ChainRepresentationInvariant closed sourceSelection)
    (leftChain : PrerequisiteChain target leftStart es) (rightChain : PrerequisiteChain target rightStart fs)
    (left : ActualUnsafeMarkerCut F ps source target degree leftStart es)
    (right : ActualUnsafeMarkerCut F ps source target degree rightStart fs)
    (sameBefore : left.before.map target.labelAt=right.before.map target.labelAt)
    (sameHead : target.labelAt left.edge=target.labelAt right.edge)
    (sameDirection : left.forward=right.forward) :
    (canonicalChainImage targetSelection leftChain).take left.before.length=
      (canonicalChainImage targetSelection rightChain).take right.before.length := by
  obtain ⟨edge,geometry,allChildren⟩ := site.beta_uncreated_child_residuals closed matching inputs flow positive
    balance rootDepth transparency relative normal history old (DegreeAligned.initial source F) selected
  have leftBeforeSafe : ∀p∈left.before,∀node,target.subterm p=some node →
      node.label.OuterBarsSafe (fun x=>x≠degree) := by
    intro p member node atNode
    exact left.safeBefore p member node.label (by simp only [LTerm.labelAt,atNode,Option.map_some])
  have rightBeforeSafe : ∀p∈right.before,∀node,target.subterm p=some node →
      node.label.OuterBarsSafe (fun x=>x≠degree) := by
    intro p member node atNode
    exact right.safeBefore p member node.label (by simp only [LTerm.labelAt,atNode,Option.map_some])
  have rightReading : PrerequisiteReadsDirected target right.reader right.edge left.forward := by
    rw [sameDirection];exact right.reading
  obtain ⟨ls,lbs,lr,lf,lname,ln,lmarker,lrest,lchosen,lat,lsafe,lchain,lprefix,lread,lbefore,lmarks,lword,
      _lstart,lorigins,lresiduals⟩ := site.beta_before_block_images_at_read history old selected sourceSafe
    sourceSelection targetSelection edge allChildren leftChain left.split left.segment left.reading
      left.lookup left.marked leftBeforeSafe
  obtain ⟨rs,rbs,rr,rf,rname,rn,rmarker,rrest,rchosen,rat,rsafe,rchain,rprefix,rread,rbefore,rmarks,rword,
      _rstart,rorigins,rresiduals⟩ := site.beta_before_block_images_at_read history old selected sourceSafe
    sourceSelection targetSelection edge allChildren rightChain right.split right.segment rightReading
      right.lookup right.marked rightBeforeSafe
  let leftSource : MarkerSourceChain F source degree left.forward (left.before.map target.labelAt)
      (left.node.label.readLetters left.forward) :=
    ⟨ls,lbs,lr,lf,lname,ln,lmarker,lrest,lchosen,lat,lsafe,lprefix,lread,lchain,lbefore,lmarks,lword⟩
  let rightSource : MarkerSourceChain F source degree left.forward (right.before.map target.labelAt)
      (right.node.label.readLetters left.forward) :=
    ⟨rs,rbs,rr,rf,rname,rn,rmarker,rrest,rchosen,rat,rsafe,rprefix,rread,rchain,rbefore,rmarks,rword⟩
  have leftAt : target.labelAt left.edge=some left.node.label := by
    simp only [LTerm.labelAt,left.lookup,Option.map_some]
  have rightAt : target.labelAt right.edge=some right.node.label := by
    simp only [LTerm.labelAt,right.lookup,Option.map_some]
  have labelEqual : left.node.label=right.node.label :=
    Option.some.inj (leftAt.symm.trans (sameHead.trans rightAt))
  have wordEqual : left.node.label.readLetters left.forward=right.node.label.readLetters left.forward :=
    congrArg (fun label : Labelled.Label=>label.readLetters left.forward) labelEqual
  have sourceWhole := marker_source_chain_representation leftSource rightSource prefixHistory initial closed
    selected sameBefore wordEqual sourceSelection representation
  change canonicalChainImage sourceSelection lchain=canonicalChainImage sourceSelection rchain at sourceWhole
  have sourceTakes := congrArg (fun blocks : List (List (Endpoint site.net))=>blocks.take left.before.length) sourceWhole
  have length : left.before.length=right.before.length := by
    simpa only [List.length_map] using congrArg List.length sameBefore
  rw [←length] at rresiduals ⊢
  exact (lresiduals.equality_iff site geometry rresiduals).mpr sourceTakes
end
#print axioms PathSite.beta_synchronized_before_images
end Lamping.AG
