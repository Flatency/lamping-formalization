import Lamping.Lamping.ChainRepresentation
import Lamping.Lamping.BetaSynchronizedBeforeImages
import Lamping.Lamping.SafeLastCopyArgumentBetaPieces
import Lamping.Lamping.BetaOldChainImages
import Lamping.Lamping.SingleUnsafeCopyArgumentCuts

namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {current : LTerm} {g : Net signature N B W} {root : B}

private def blocksAt (selection : OccurrenceFragmentSelection current g root)
    (edges : List Path) (valid : ∀p∈edges,(subtermAt current.erase p).isSome) :
    List (List (Endpoint g)) :=
  edges.attach.map (fun p=>(selection ⟨p.val,valid p.val p.property⟩).fragment.segments)

private theorem blocksAt_append (selection : OccurrenceFragmentSelection current g root)
    (valid : ∀p∈before++rest,(subtermAt current.erase p).isSome) :
    blocksAt selection (before++rest) valid=
      blocksAt selection before (fun p hp=>valid p (List.mem_append_left _ hp))++
      blocksAt selection rest (fun p hp=>valid p (List.mem_append_right _ hp)) := by
  simp only [blocksAt,List.attach_append,List.map_append,List.map_map,Function.comp_def]

private theorem actual_valid (chain : PrerequisiteChain current start edges)
    (member : p∈edges) : (subtermAt current.erase p).isSome := by
  rcases chain.eligible member with ⟨parent,stamp,fn,arg,equal,lookup⟩ | ⟨stamp,body,lookup⟩
  · have actual : current.subterm p=some fn := by
      rw [equal,LTerm.subterm_append,lookup];cases fn <;> rfl
    rw [←LTerm.erase_subterm,actual];rfl
  · rw [←LTerm.erase_subterm,lookup];rfl

private theorem canonical_cut (selection : OccurrenceFragmentSelection current g root)
    (chain : PrerequisiteChain current start edges)
    (split : edges=before++edge::after)
    (tailChain : PrerequisiteChain current next after)
    (position : Position current.erase) (atPosition : position.val=edge) :
    canonicalChainImage selection chain=
      (canonicalChainImage selection chain).take before.length++
        (selection position).fragment.segments::canonicalChainImage selection tailChain := by
  subst edges
  let valid : ∀p∈before++edge::after,(subtermAt current.erase p).isSome :=
    fun _ hp=>actual_valid chain hp
  change blocksAt selection (before++edge::after) valid=_
  rw [blocksAt_append]
  have suffix : blocksAt selection (edge::after)
      (fun p hp=>valid p (List.mem_append_right _ hp))=
      (selection position).fragment.segments::canonicalChainImage selection tailChain := by
    cases position with
    | mk path property =>
      change path=edge at atPosition
      subst path
      simp only [blocksAt,List.attach_cons,List.map_cons,List.map_map,Function.comp_def]
      rfl
  have prefixLength : (blocksAt selection before
      (fun p hp=>valid p (List.mem_append_left _ hp))).length=before.length := by
    simp only [blocksAt,List.length_map,List.length_attach]
  have prefixTake : (canonicalChainImage selection chain).take before.length=
      blocksAt selection before (fun p hp=>valid p (List.mem_append_left _ hp)) := by
    change (blocksAt selection (before++edge::after) valid).take before.length=_
    rw [blocksAt_append,←prefixLength,List.take_left]
  rw [suffix,prefixTake]

end

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Graph.Label signature} {i : Nat}

/-- Complete ordered forward preservation for two actual chains whose only
unsafe READs are normal copied ARG lambdas with safe actual LAST edges.
The cuts, all three comparisons, and their literal concatenation are derived. -/
theorem PathSite.beta_single_unsafe_copy_argument_forward
    (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
    {root : B} {source middle target original : LTerm} {F prior pre : List Path}
    {degree leftStamp rightStamp : Lambda.Labelled.Label}
    {leftBody rightBody : LTerm} {chosen leftParent rightParent leftStart rightStart : Path}
    {es fs : List Path} {marked : Marked}
    (closed : Closed source.erase) (initial : INIT original)
    (prefixHistory : History prior original source)
    (event : SelectedOldTurn F source degree pre middle target chosen)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (leftOccurs : ArgumentOccurrence event.body.erase (leftParent++[.arg]))
    (rightOccurs : ArgumentOccurrence event.body.erase (rightParent++[.arg]))
    (leftLookup : target.subterm (chosen++(leftParent++[.arg]))=some (.lam leftStamp leftBody))
    (rightLookup : target.subterm (chosen++(rightParent++[.arg]))=some (.lam rightStamp rightBody))
    (leftChain : PrerequisiteChain target leftStart es)
    (rightChain : PrerequisiteChain target rightStart fs)
    (iso : ChainIncidenceIso
      (chainSyntaxIncidence target (event.final_history.closed closed) es)
      (chainSyntaxIncidence target (event.final_history.closed closed) fs))
    (leftMember : chosen++(leftParent++[.arg])∈es)
    (rightMember : chosen++(rightParent++[.arg])∈fs)
    (leftOtherSafe : ∀e∈es,e≠chosen++(leftParent++[.arg]) →
      degreeReadSafe degree (target.labelAt e))
    (rightOtherSafe : ∀e∈fs,e≠chosen++(rightParent++[.arg]) →
      degreeReadSafe degree (target.labelAt e))
    (leftLastSafe : ∀node,
      middle.subterm ((chosen++[.fn,.body])++(leftParent++[.arg]))=some node →
        node.label.OuterBarsSafe (fun x=>x≠degree))
    (rightLastSafe : ∀node,
      middle.subterm ((chosen++[.fn,.body])++(rightParent++[.arg]))=some node →
        node.label.OuterBarsSafe (fun x=>x≠degree))
    (matching : Matches site.net root source.erase) (inputs : RootInputs site.net root)
    {boundary : B→Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {heights : B→Int} (balance : IndexedLevelBalance site.net heights) (rootDepth : heights root=0)
    (transparency : Transparency site.net root)
    (relative : Marked.RelativeHistory (pre++[chosen])
      (Marked.mark (site.betaSyntaxFiber root source.erase) source.erase) marked)
    (normal : Marked.Normal marked)
    (sourceSelection : OccurrenceFragmentSelection source site.net root)
    (representation : JointRepresentation closed sourceSelection)
    (targetSelection : OccurrenceFragmentSelection target site.reduce root) :
    SameChainRepresentation targetSelection leftChain rightChain := by
  obtain ⟨out⟩ := single_unsafe_copy_argument_cuts initial prefixHistory closed event selected sourceSafe
    leftOccurs rightOccurs leftLookup rightLookup leftChain rightChain iso leftMember rightMember
    leftOtherSafe rightOtherSafe
  have sameDirection : out.left.forward=out.right.forward :=
    out.leftFalse.trans out.rightFalse.symm
  have before := site.beta_synchronized_before_images closed matching inputs flow positive balance
    rootDepth transparency relative normal event.final_history event.final_old selected sourceSafe
    prefixHistory initial sourceSelection targetSelection representation.1 leftChain rightChain
    out.left out.right out.sameBefore out.sameHead sameDirection
  have leftValid : (subtermAt target.erase (chosen++(leftParent++[.arg]))).isSome := by
    rw [←LTerm.erase_subterm,leftLookup];rfl
  have rightValid : (subtermAt target.erase (chosen++(rightParent++[.arg]))).isSome := by
    rw [←LTerm.erase_subterm,rightLookup];rfl
  let leftPosition : Position target.erase := ⟨chosen++(leftParent++[.arg]),leftValid⟩
  let rightPosition : Position target.erase := ⟨chosen++(rightParent++[.arg]),rightValid⟩
  obtain ⟨headIso⟩ := out.headIso
  obtain ⟨localTarget,_localHistory,edge,selection,_geometry,ln,rn,_leftAt,_rightAt,
      _evaluations,_leftNonempty,_rightNonempty,_leftResidual,_rightResidual,head⟩ :=
    site.beta_safe_last_copy_argument_pieces closed initial prefixHistory event selected leftOccurs rightOccurs
      leftLookup rightLookup out.leftHeadChain out.rightHeadChain headIso
      out.leftAfterSafe out.rightAfterSafe leftLastSafe rightLastSafe
      matching inputs flow positive balance rootDepth transparency relative normal sourceSelection representation
      (targetSelection leftPosition) (targetSelection rightPosition)
  have after : SameChainRepresentation targetSelection out.leftAfterChain out.rightAfterChain :=
    (site.beta_marker_free_rep closed matching inputs flow positive balance rootDepth transparency
      relative normal event.final_history event.final_old (DegreeAligned.initial source F) selected
      sourceSelection targetSelection representation.1 out.leftAfterChain out.rightAfterChain
      out.leftAfterSafe out.rightAfterSafe).mpr out.afterIso
  change canonicalChainImage targetSelection leftChain=canonicalChainImage targetSelection rightChain
  rw [canonical_cut targetSelection leftChain out.left.split out.leftAfterChain leftPosition out.leftEdge.symm,
    canonical_cut targetSelection rightChain out.right.split out.rightAfterChain rightPosition out.rightEdge.symm]
  change canonicalChainImage targetSelection out.leftAfterChain=
    canonicalChainImage targetSelection out.rightAfterChain at after
  rw [before,head,after]

end
#print axioms PathSite.beta_single_unsafe_copy_argument_forward
end Lamping.AG

