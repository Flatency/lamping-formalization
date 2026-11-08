import Lamping.Lamping.ChainFragmentUniqueness
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {current other : LTerm}

/-- Literal occurrence cuts depend on the matched syntax and real access
word, not the source annotation. This does not transport labels, degrees,
family identities or reduction histories. -/
theorem OccurrenceFragment.segments_unique_of_matches
    (matching : Matches g root current.erase) (otherMatching : Matches g root other.erase)
    (first : OccurrenceFragment current g root p) (second : OccurrenceFragment other g root p) :
    first.fragment.segments=second.fragment.segments := by
  have accesses : first.fragment.access=second.fragment.access :=
    matching.accessWord_injective (first.fragment.word.trans second.fragment.word.symm)
  rcases first.occurrence.last_departure with ⟨empty,external⟩ |
    ⟨parentPath,step,parentTerm,split,lookup,role⟩
  · rcases second.occurrence.last_departure with ⟨_,otherExternal⟩ |
      ⟨otherParent,otherStep,otherTerm,otherSplit,_otherLookup,_otherRole⟩
    · have leftExternal : (sourceEdge first.environment first.context first.term).fromPort=.external := by
        cases first.term <;> exact external
      have rightExternal : (sourceEdge second.environment second.context second.term).fromPort=.external := by
        cases second.term <;> exact otherExternal
      rw [first.fragment.external_segments leftExternal,second.fragment.external_segments rightExternal,accesses]
    · rw [empty] at otherSplit
      have impossible := congrArg List.length otherSplit
      simp only [List.length_nil,List.length_append,List.length_singleton] at impossible
      omega
  · rcases second.occurrence.last_departure with ⟨empty,_otherExternal⟩ |
      ⟨otherParent,otherStep,otherTerm,otherSplit,_otherLookup,otherRole⟩
    · rw [empty] at split
      have impossible := congrArg List.length split
      simp only [List.length_nil,List.length_append,List.length_singleton] at impossible
      omega
    · obtain ⟨parents,steps⟩ := List.append_inj' (split.symm.trans otherSplit) rfl
      have sameStep : step=otherStep := (List.cons.inj steps).1
      subst otherParent
      subst otherStep
      let parentPosition : Position current.erase := ⟨parentPath,by
        rw [←LTerm.erase_subterm,lookup];rfl⟩
      obtain ⟨parent,parentWord,_⟩ := Matches.observation g matching parentPosition
      have leftRole : SourceDeparture parentTerm step
          (sourceEdge first.environment first.context first.term).fromPort := by
        cases first.term <;> exact role
      have rightRole : SourceDeparture otherTerm step
          (sourceEdge second.environment second.context second.term).fromPort := by
        cases second.term <;> exact otherRole
      have word : p=accessWord g parent.val++[step] := by rw [parentWord];exact split
      have leftCut := first.fragment.child_prefix matching leftRole parent word
      have rightCut := second.fragment.child_prefix otherMatching rightRole parent word
      have literal := congrArg Subtype.val accesses
      rw [leftCut.2,rightCut.2] at literal
      exact List.append_cancel_left literal

/-- The SAME list of real syntax-edge positions has the same canonical
physical image under two annotations and independently chosen selectors. -/
theorem canonicalChainImage_same_positions
    (matching : Matches g root current.erase) (otherMatching : Matches g root other.erase)
    (first : OccurrenceFragmentSelection current g root)
    (second : OccurrenceFragmentSelection other g root)
    (firstChain : PrerequisiteChain current p edges) (secondChain : PrerequisiteChain other q edges) :
    canonicalChainImage first firstChain=canonicalChainImage second secondChain := by
  unfold canonicalChainImage
  apply List.map_congr_left
  intro edge _member
  exact OccurrenceFragment.segments_unique_of_matches matching otherMatching _ _
end
end Lamping.AG
