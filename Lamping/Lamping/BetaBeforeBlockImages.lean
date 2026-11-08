import Lamping.Lamping.BetaOldChainImages
import Lamping.Lambda.EarliestReadingMarker
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {term : LTerm} {g : Net signature N B W} {root : B}
private def prefixImages (selection : OccurrenceFragmentSelection term g root)
    (es : List Path) (valid : ∀p∈es,(subtermAt term.erase p).isSome) : List (List (Endpoint g)) :=
  es.attach.map (fun p=>(selection ⟨p.val,valid p.val p.property⟩).fragment.segments)
private theorem prefixImages_length (selection : OccurrenceFragmentSelection term g root)
    (valid : ∀p∈es,(subtermAt term.erase p).isSome) :
    (prefixImages selection es valid).length=es.length := by
  simp only [prefixImages,List.length_map,List.length_attach]
private theorem prefixImages_append (selection : OccurrenceFragmentSelection term g root)
    (valid : ∀p∈es++rest,(subtermAt term.erase p).isSome) :
    prefixImages selection (es++rest) valid=
      prefixImages selection es (fun p hp=>valid p (List.mem_append_left _ hp))++
      prefixImages selection rest (fun p hp=>valid p (List.mem_append_right _ hp)) := by
  simp only [prefixImages,List.attach_append,List.map_append,List.map_map,Function.comp_def]
private theorem chain_valid (chain : PrerequisiteChain term start es) (inside : p∈es) :
    (subtermAt term.erase p).isSome := by
  rcases chain.eligible inside with ⟨parent,stamp,fn,arg,equal,lookup⟩ |⟨stamp,body,lookup⟩
  · have actual : term.subterm p=some fn := by
      rw [equal,LTerm.subterm_append,lookup];cases fn <;> rfl
    rw [←LTerm.erase_subterm,actual];rfl
  · rw [←LTerm.erase_subterm,lookup];rfl
private theorem canonical_take_prefix (selection : OccurrenceFragmentSelection term g root)
    (chain : PrerequisiteChain term start es) (split : es=before++rest)
    (valid : ∀p∈before,(subtermAt term.erase p).isSome) :
    (canonicalChainImage selection chain).take before.length=prefixImages selection before valid := by
  subst es
  change (prefixImages selection (before++rest) (fun _ hp=>chain_valid chain hp)).take before.length=_
  rw [prefixImages_append]
  have length : (prefixImages selection before valid).length=before.length := prefixImages_length selection valid
  change (prefixImages selection before valid++_).take before.length=_
  rw [←length,List.take_left]
end

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Graph.Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
private theorem slots_length {labels : History ps source target}
    (origins : BetaEdgeHistoryPreimages labels es oldEs) : es.length=oldEs.length := by
  induction origins with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

private theorem prefix_residuals {source target : LTerm} {ps : List Path}
    {labels : History ps source target} {edge : BetaEdge site.net} {root : B}
    (sourceSelection : OccurrenceFragmentSelection source site.net root)
    (targetSelection : OccurrenceFragmentSelection target site.reduce root)
    (origins : BetaEdgeHistoryPreimages labels es oldEs)
    (targetValid : ∀p∈es,(subtermAt target.erase p).isSome)
    (sourceValid : ∀p∈oldEs,(subtermAt source.erase p).isSome)
    (residual : ∀p (hp : p∈es) q (hq : q∈oldEs),BetaNodeHistoryPreimage labels p q →
      BetaPathResidual site edge
        ((targetSelection ⟨p,targetValid p hp⟩).fragment.segments.map (plugEnd _ _).invFun)
        (sourceSelection ⟨q,sourceValid q hq⟩).fragment.segments) :
    BetaAtomicBlockResiduals site edge
      (prefixImages targetSelection es targetValid) (prefixImages sourceSelection oldEs sourceValid) := by
  induction origins with
  | nil => exact .nil
  | @cons p q es oldEs trace tail ih =>
    simp only [prefixImages,List.attach_cons,List.map_cons,List.map_map,Function.comp_def]
    apply BetaAtomicBlockResiduals.cons
      (residual p List.mem_cons_self q List.mem_cons_self trace)
      (sourceSelection ⟨q,sourceValid q List.mem_cons_self⟩).fragment.emptyWord
    exact ih (fun p hp=>targetValid p (List.mem_cons_of_mem _ hp))
      (fun q hq=>sourceValid q (List.mem_cons_of_mem _ hq))
      (fun p hp q hq ht=>residual p (List.mem_cons_of_mem _ hp) q (List.mem_cons_of_mem _ hq) ht)
end

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Graph.Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))

/-- Fixed-edge kernel at a supplied ACTUAL directed reading. The local child
residual function is the conclusion of beta_uncreated_child_residuals. This
separates one common-edge choice from any number of genuine BEFORE cuts. -/
theorem PathSite.beta_before_block_images_at_read
    {root : B} {source target current : LTerm} {ps F : List Path} {n : Marked}
    {degree : Labelled.Label}
    (history : History ps source target)
    (old : Marked.RelativeOldHistory F ps (Marked.mark F source.erase) n)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (sourceSelection : OccurrenceFragmentSelection source site.net root)
    (targetSelection : OccurrenceFragmentSelection target site.reduce root)
    (edge : BetaEdge site.net)
    (allChildren : ∀ (p : Path) (step : Step) (parentTerm : LTerm),target.subterm p=some parentTerm →
      ∀ child : OccurrenceFragment target site.reduce root (p++[step]),
        SourceDeparture parentTerm step (sourceEdge child.environment child.context child.term).fromPort →
        child.term.label.OuterBarsSafe (fun payload=>payload≠degree) →
        ∃ oldPosition oldNode,source.subterm oldPosition=some oldNode ∧
          BetaNodeHistoryPreimage history (p++[step]) oldPosition ∧
          ∀ oldFragment : OccurrenceFragment source site.net root oldPosition,
            BetaPathResidual site edge (child.fragment.segments.map (plugEnd _ _).invFun)
              oldFragment.fragment.segments)
    (targetChain : PrerequisiteChain target start es)
    (split : es=before++(chosen::after))
    (segment : PrerequisitePrefix target start before middle)
    (directed : PrerequisiteReadsDirected target middle chosen forward)
    (lookup : target.subterm chosen=some current)
    (chosenMarked : ¬current.label.OuterBarsSafe (fun x=>x≠degree))
    (safeBefore : ∀p∈before,∀node,target.subterm p=some node →
      node.label.OuterBarsSafe (fun x=>x≠degree)) :
    ∃sourceStart sourceBefore sourceReader sourceFirst name sourceNode marker rest,
      name∈F ∧source.subterm sourceFirst=some sourceNode ∧
      sourceNode.label.OuterBarsSafe (fun x=>x≠degree) ∧
      ∃sourceChain : PrerequisiteChain source sourceStart (sourceBefore++[sourceFirst,name++[.fn]]),
        PrerequisitePrefix source sourceStart sourceBefore sourceReader ∧
        PrerequisiteReadsDirected source sourceReader sourceFirst forward ∧
        before.map target.labelAt=sourceBefore.map source.labelAt ∧
        marker.MarksDegree degree ∧
        current.label.readLetters forward=sourceNode.label.readLetters forward++marker::rest ∧
        BetaNodeHistoryPreimage history start sourceStart ∧
        BetaEdgeHistoryPreimages history before sourceBefore ∧
        BetaAtomicBlockResiduals site edge
          ((canonicalChainImage targetSelection targetChain).take before.length)
          ((canonicalChainImage sourceSelection sourceChain).take before.length) := by
  obtain ⟨_spine,s,sb,r,f,name,node,marker,rest,chosenName,atNode,nodeSafe,sourcePrefix,sourceReads,
    sourceChain,labelMap,markerMarked,equation,startTrace,origins⟩ :=
    old.earliest_marker_prefix_with_before_origins history selected sourceSafe segment directed lookup chosenMarked safeBefore
  have targetValid : ∀p∈before,(subtermAt target.erase p).isSome := by
    intro p hp
    apply chain_valid targetChain
    rw [split];exact List.mem_append_left _ hp
  have sourceValid : ∀p∈sb,(subtermAt source.erase p).isSome := by
    intro p hp
    exact chain_valid sourceChain (List.mem_append_left _ hp)
  have residual : ∀p (hp : p∈before) q (hq : q∈sb),BetaNodeHistoryPreimage history p q →
      BetaPathResidual site edge
        ((targetSelection ⟨p,targetValid p hp⟩).fragment.segments.map (plugEnd _ _).invFun)
        (sourceSelection ⟨q,sourceValid q hq⟩).fragment.segments := by
    intro p hp q hq desired
    let child := targetSelection ⟨p,targetValid p hp⟩
    have safe := safeBefore p hp child.term child.occurrence.lookup
    rcases child.occurrence.last_departure with ⟨empty,_⟩ |
      ⟨parent,step,parentTerm,childSplit,atParent,role⟩
    · have inside : p∈es := by rw [split];exact List.mem_append_left _ hp
      exact False.elim (targetChain.reading_ne_nil inside empty)
    · have departure : SourceDeparture parentTerm step
          (sourceEdge child.environment child.context child.term).fromPort := by
        cases child.term <;> exact role
      change p=parent++[step] at childSplit
      subst p
      obtain ⟨oldPosition,oldNode,oldLookup,trace,physical⟩ :=
        allChildren parent step parentTerm atParent child departure safe
      have same := trace.unique desired
      subst oldPosition
      exact physical (sourceSelection ⟨q,sourceValid q hq⟩)
  have blocks := prefix_residuals site sourceSelection targetSelection origins targetValid sourceValid residual
  have targetTake := canonical_take_prefix targetSelection targetChain split targetValid
  have sourceTake := canonical_take_prefix sourceSelection sourceChain rfl sourceValid
  have length := slots_length origins
  have physical : BetaAtomicBlockResiduals site edge
      ((canonicalChainImage targetSelection targetChain).take before.length)
      ((canonicalChainImage sourceSelection sourceChain).take before.length) := by
    rw [targetTake,length,sourceTake]
    exact blocks
  exact ⟨s,sb,r,f,name,node,marker,rest,chosenName,atNode,nodeSafe,sourceChain,
    sourcePrefix,sourceReads,labelMap,markerMarked,equation,startTrace,origins,physical⟩

/-- Actual successful-chain BEFORE images use the same returned original
prefix and occurrence ancestry. The unread suffix is wholly unrestricted. -/
theorem PathSite.beta_before_block_images
    {root : B} {source target current : LTerm} {ps F : List Path} {marked n : Marked}
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
    (sourceSelection : OccurrenceFragmentSelection source site.net root)
    (targetSelection : OccurrenceFragmentSelection target site.reduce root)
    (targetChain : PrerequisiteChain target start es)
    (split : es=before++(chosen::after))
    (lookup : target.subterm chosen=some current)
    (chosenMarked : ¬current.label.OuterBarsSafe (fun x=>x≠degree))
    (safeBefore : ∀p∈before,∀node,target.subterm p=some node →
      node.label.OuterBarsSafe (fun x=>x≠degree)) :
    ∃edge : BetaEdge site.net,SiteBetaGeometry site edge ∧
      ∃sourceStart sourceBefore sourceReader sourceFirst name sourceNode marker rest,∃forward : Bool,
        name∈F ∧source.subterm sourceFirst=some sourceNode ∧
        sourceNode.label.OuterBarsSafe (fun x=>x≠degree) ∧
        ∃sourceChain : PrerequisiteChain source sourceStart (sourceBefore++[sourceFirst,name++[.fn]]),
          PrerequisitePrefix source sourceStart sourceBefore sourceReader ∧
          PrerequisiteReadsDirected source sourceReader sourceFirst forward ∧
          before.map target.labelAt=sourceBefore.map source.labelAt ∧
          marker.MarksDegree degree ∧
          current.label.readLetters forward=sourceNode.label.readLetters forward++marker::rest ∧
          BetaNodeHistoryPreimage history start sourceStart ∧
          BetaEdgeHistoryPreimages history before sourceBefore ∧
          BetaAtomicBlockResiduals site edge
            ((canonicalChainImage targetSelection targetChain).take before.length)
            ((canonicalChainImage sourceSelection sourceChain).take before.length) := by
  have member : chosen∈es := by rw [split];exact List.mem_append_right _ List.mem_cons_self
  obtain ⟨actualBefore,actualAfter,middle,actualSplit,segment,_tail,reads⟩ :=
    targetChain.split_at_member member
  obtain ⟨beforeEq,afterEq⟩ := targetChain.first_created_split_unique actualSplit split
  subst actualBefore
  subst actualAfter
  obtain ⟨forward,directed⟩ : ∃forward,PrerequisiteReadsDirected target middle chosen forward := by
    rcases reads with ⟨stamp,fn,arg,atApp,same⟩ |⟨stamp,body,atLambda,same⟩
    · exact ⟨true,Or.inl ⟨stamp,fn,arg,atApp,same⟩,same⟩
    · exact ⟨false,Or.inr ⟨stamp,body,atLambda,same⟩,same⟩
  obtain ⟨edge,geometry,allChildren⟩ := site.beta_uncreated_child_residuals closed matching inputs flow positive
    balance rootDepth transparency relative normal history old (DegreeAligned.initial source F) selected
  obtain ⟨s,sb,r,f,name,node,marker,rest,data⟩ := site.beta_before_block_images_at_read history old selected sourceSafe
    sourceSelection targetSelection edge allChildren targetChain split segment directed lookup chosenMarked safeBefore
  exact ⟨edge,geometry,s,sb,r,f,name,node,marker,rest,forward,data⟩

end
#print axioms PathSite.beta_before_block_images_at_read
#print axioms PathSite.beta_before_block_images
end Lamping.AG
