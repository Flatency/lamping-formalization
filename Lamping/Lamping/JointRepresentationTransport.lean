import Lamping.Lamping.FamilyRepresentation
import Lamping.Lamping.NetIsoPathTransport
namespace Lamping.Graph
open AG Lambda Lambda.Labelled
section
variable {N M B W V : Type} [FiniteNames N] [FiniteNames M] [FiniteNames B]
  [FiniteNames W] [FiniteNames V]
variable {g : Net signature N B W} {h : Net signature M B V} (iso : NetIso g h)

theorem NetIso.occurrence_fragment_segments {root : B} {current : LTerm}
    (sourceMatches : Matches g root current.erase)
    (source : OccurrenceFragment current g root position)
    (target : OccurrenceFragment current h root position) :
    target.fragment.segments=source.fragment.segments.map iso.ends := by
  have targetMatches := iso.matches sourceMatches
  rcases source with ⟨sub,env,ctx,occurrence,source⟩
  rcases target with ⟨otherSub,otherEnv,otherCtx,otherOccurrence,target⟩
  obtain ⟨rfl,rfl,rfl⟩ := occurrence.same_occurrence otherOccurrence
  let mapped := iso.rootAccessBij root source.access
  have fullEq : mapped=target.access := targetMatches.accessWord_injective
    ((iso.accessWord source.access.val).trans (source.word.trans target.word.symm))
  have whole : target.access.val=source.access.val.map iso.ends :=
    (congrArg Subtype.val fullEq).symm
  rcases occurrence.last_departure with ⟨empty,external⟩ |
    ⟨parentPath,step,parentTerm,split,lookup,role⟩
  · have externalEdge : (sourceEdge env ctx sub).fromPort=.external := by
      cases sub <;> exact external
    rw [source.external_segments externalEdge,target.external_segments externalEdge]
    exact whole
  · let parentPosition : Position current.erase := ⟨parentPath,by
      rw [←LTerm.erase_subterm,lookup];rfl⟩
    obtain ⟨parent,parentWord,_⟩ := Matches.observation g sourceMatches parentPosition
    let newParent := iso.rootAccessBij root parent
    have sourceFrom : (sourceEdge env ctx sub).fromPort=ctx := by cases sub <;> rfl
    have actualRole : SourceDeparture parentTerm step (sourceEdge env ctx sub).fromPort := by
      rw [sourceFrom];exact role
    have oldWord : position=AG.accessWord g parent.val++[step] := by rw [parentWord];exact split
    have newWord : position=AG.accessWord h newParent.val++[step] := by
      change position=AG.accessWord h (parent.val.map iso.ends)++[step]
      rw [iso.accessWord];exact oldWord
    have oldCut := source.child_prefix sourceMatches actualRole parent oldWord
    have newCut := target.child_prefix targetMatches actualRole newParent newWord
    rw [oldCut.2,List.map_append] at whole
    change target.access.val=parent.val.map iso.ends++source.segments.map iso.ends at whole
    have literal : parent.val.map iso.ends++target.segments=
        parent.val.map iso.ends++source.segments.map iso.ends := newCut.2.symm.trans whole
    exact List.append_cancel_left literal
private theorem restore_segments (xs : List (Endpoint g)) :
    (xs.map iso.ends).map iso.symm.ends=xs := by
  simp only [List.map_map]
  have inverse : (iso.symm.ends ∘ iso.ends)=id := funext iso.ends.left_inv
  rw [inverse,List.map_id]

include iso

theorem NetIso.occurrence_fragment_equality {root : B} {current : LTerm}
    (sourceMatches : Matches g root current.erase)
    (sourceFirst : OccurrenceFragment current g root p)
    (targetFirst : OccurrenceFragment current h root p)
    (sourceSecond : OccurrenceFragment current g root q)
    (targetSecond : OccurrenceFragment current h root q) :
    targetFirst.fragment.segments=targetSecond.fragment.segments ↔
      sourceFirst.fragment.segments=sourceSecond.fragment.segments := by
  rw [iso.occurrence_fragment_segments sourceMatches sourceFirst targetFirst,
    iso.occurrence_fragment_segments sourceMatches sourceSecond targetSecond]
  constructor
  · intro same
    have undone := congrArg (List.map iso.symm.ends) same
    simpa only [restore_segments iso] using undone
  · exact congrArg (List.map iso.ends)

theorem NetIso.chain_representation {root : B} {current : LTerm}
    (sourceMatches : Matches g root current.erase)
    (source : OccurrenceFragmentSelection current g root)
    (target : OccurrenceFragmentSelection current h root)
    (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right) :
    SameChainRepresentation target first second ↔SameChainRepresentation source first second := by
  have blocks {p edges} (chain : PrerequisiteChain current p edges) :
      canonicalChainImage target chain=
        (canonicalChainImage source chain).map (List.map iso.ends) := by
    simp only [canonicalChainImage,List.map_map,Function.comp_def]
    apply congrArg (fun f => List.map f edges.attach)
    funext edge
    exact iso.occurrence_fragment_segments sourceMatches (source _) (target _)
  unfold SameChainRepresentation
  rw [blocks first,blocks second]
  constructor
  · intro same
    have undone := congrArg (List.map (List.map iso.symm.ends)) same
    simpa only [List.map_map,Function.comp_def,restore_segments iso,List.map_id_fun'] using undone
  · exact congrArg (List.map (List.map iso.ends))

theorem NetIso.joint_representation {root : B} {current : LTerm}
    (sourceMatches : Matches g root current.erase) (closed : Closed current.erase)
    (source : OccurrenceFragmentSelection current g root)
    (target : OccurrenceFragmentSelection current h root) :
    JointRepresentation closed target ↔JointRepresentation closed source := by
  have pieces (a b : SyntaxIncidence.Edge current) :=
    iso.occurrence_fragment_equality sourceMatches (source a) (target a) (source b) (target b)
  have chains : ChainRepresentationInvariant closed target ↔ChainRepresentationInvariant closed source := by
    constructor
    · intro invariant p q left right first second
      exact (iso.chain_representation sourceMatches source target first second).symm.trans (invariant first second)
    · intro invariant p q left right first second
      exact (iso.chain_representation sourceMatches source target first second).trans (invariant first second)
  have auxiliary : AuxiliarySeparation closed target ↔AuxiliarySeparation closed source := by
    constructor
    · intro invariant a b first second label distinct
      exact invariant a b first second label (fun equal=>distinct ((pieces a b).mp equal))
    · intro invariant a b first second label distinct
      exact invariant a b first second label (fun equal=>distinct ((pieces a b).mpr equal))
  exact and_congr chains auxiliary

end
end Lamping.Graph
