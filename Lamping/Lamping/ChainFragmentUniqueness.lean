import Lamping.Lamping.ChainRepresentation
import Lamping.Lamping.MatchingSharedSyntaxEvaluation
namespace Lamping.Lambda.Labelled
/-- A literal current occurrence determines its syntax environment and ports, even with repeated labels. -/
theorem SourceSubterm.same_occurrence
    (first : SourceSubterm outside context t p env ctx sub)
    (second : SourceSubterm outside context t p otherEnv otherCtx otherSub) :
    env=otherEnv ∧ctx=otherCtx ∧sub=otherSub := by
  induction first generalizing otherEnv otherCtx otherSub with
  | nil => cases second; exact ⟨rfl,rfl,rfl⟩
  | fn _ ih => cases second with | fn second => exact ih second
  | arg _ ih => cases second with | arg second => exact ih second
  | body _ ih => cases second with | body second => exact ih second
end Lamping.Lambda.Labelled

namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {current : LTerm} {g : Net signature N B W} {root : B}
/-- Actual rooted syntax-token cuts make the fragment at one position unique. No INIT or label injectivity is required. -/
theorem OccurrenceFragment.segments_unique (matching : Matches g root current.erase)
    (first second : OccurrenceFragment current g root position) :
    first.fragment.segments=second.fragment.segments := by
  rcases first with ⟨sub,env,ctx,occurrence,first⟩
  rcases second with ⟨otherSub,otherEnv,otherCtx,otherOccurrence,second⟩
  obtain ⟨rfl,rfl,rfl⟩ := occurrence.same_occurrence otherOccurrence
  have accesses : first.access=second.access :=
    matching.accessWord_injective (first.word.trans second.word.symm)
  rcases occurrence.last_departure with ⟨empty,external⟩ |
    ⟨parentPath,step,parentTerm,split,lookup,role⟩
  · have externalEdge : (sourceEdge env ctx sub).fromPort=.external := by
      cases sub <;> exact external
    rw [first.external_segments externalEdge,second.external_segments externalEdge,accesses]
  · let parentPosition : Position current.erase := ⟨parentPath,by
      rw [←LTerm.erase_subterm,lookup]; rfl⟩
    obtain ⟨parent,parentWord,_⟩ := Matches.observation g matching parentPosition
    have sourceFrom : (sourceEdge env ctx sub).fromPort=ctx := by cases sub <;> rfl
    have actualRole : SourceDeparture parentTerm step (sourceEdge env ctx sub).fromPort := by
      rw [sourceFrom]; exact role
    have word : position=accessWord g parent.val++[step] := by rw [parentWord]; exact split
    have firstCut := first.child_prefix matching actualRole parent word
    have secondCut := second.child_prefix matching actualRole parent word
    have lists := congrArg Subtype.val accesses
    rw [firstCut.2,secondCut.2] at lists
    exact List.append_cancel_left lists
end
end Lamping.AG
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {current : LTerm} {g : Net signature N B W} {root : B}

theorem OccurrenceFragment.access_unique (matching : Matches g root current.erase)
    (first second : OccurrenceFragment current g root position) :
    first.fragment.access=second.fragment.access :=
  matching.accessWord_injective (first.fragment.word.trans second.fragment.word.symm)

theorem canonicalChainImage_choice_independent (matching : Matches g root current.erase)
    (first second : OccurrenceFragmentSelection current g root)
    (chain : PrerequisiteChain current p edges) :
    canonicalChainImage first chain=canonicalChainImage second chain := by
  unfold canonicalChainImage
  apply List.map_congr_left
  intro edge member
  exact OccurrenceFragment.segments_unique matching _ _

theorem orientedChainImage_choice_independent (matching : Matches g root current.erase)
    (first second : OccurrenceFragmentSelection current g root)
    (reading : PrerequisiteReading current p edges directions) :
    orientedChainImage first reading=orientedChainImage second reading := by
  unfold orientedChainImage
  rw [canonicalChainImage_choice_independent matching first second reading.chain]

end
end Lamping.AG