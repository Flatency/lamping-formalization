import Lamping.Lamping.InitialFragmentReflection
import Lamping.Lamping.ChainInitialSequences
import Lamping.Lamping.InitialMatching

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

variable {current : LTerm} {level : Nat}

theorem initial_canonical_blocks_reflect_edges
    (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right)
    (selectLeft selectRight : OccurrenceFragmentSelection current (encode level current.erase).net (.inl ()))
    (same : canonicalChainImage selectLeft first=canonicalChainImage selectRight second) : left=right := by
  have lengths := congrArg List.length same
  simp only [canonicalChainImage_length] at lengths
  apply List.ext_getElem lengths
  intro i leftBound rightBound
  have firstBound : i<(canonicalChainImage selectLeft first).length := by
    simpa only [canonicalChainImage_length] using leftBound
  have secondBound : i<(canonicalChainImage selectRight second).length := by
    simpa only [canonicalChainImage_length] using rightBound
  have sameAt := congrArg (fun xs=>xs[i]?) same
  change (canonicalChainImage selectLeft first)[i]?=(canonicalChainImage selectRight second)[i]? at sameAt
  rw [List.getElem?_eq_getElem firstBound,List.getElem?_eq_getElem secondBound] at sameAt
  have segments := Option.some.inj sameAt
  simp only [canonicalChainImage,List.getElem_map] at segments
  have positions := OccurrenceFragment.initial_segments_injective _ _ segments
  simpa only [List.getElem_attach] using positions

/-- At one initial encoding with INIT labels, the precise bare incidence
object is isomorphic exactly when the canonical ordered physical blocks
coincide. Alignment with the original usual-chain object and preservation
along graph histories remain separate obligations. -/
theorem initial_chain_incidence_iff_blocks
    (closed : Closed current.erase) (initial : INIT current)
    (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right)
    (selectLeft selectRight : OccurrenceFragmentSelection current (encode level current.erase).net (.inl ())) :
    ChainIncidenceIsomorphic (chainSyntaxIncidence current closed left)
      (chainSyntaxIncidence current closed right) ↔
      canonicalChainImage selectLeft first=canonicalChainImage selectRight second := by
  constructor
  · rintro ⟨iso⟩
    exact initial_iso_canonical_blocks (encode_closed_matches current.erase closed level)
      closed initial first second iso selectLeft selectRight
  · intro same
    have equal := initial_canonical_blocks_reflect_edges first second selectLeft selectRight same
    subst right
    exact ⟨ChainIncidenceIso.refl _⟩

/-- The initial graph supplies the actual selector internally, before any
isomorphism/block comparison is made. No REP field is assumed. -/
theorem initial_chain_incidence_realization (current : LTerm) (closed : Closed current.erase)
    (initial : INIT current) (level : Nat) :
    ∃ selection : OccurrenceFragmentSelection current (encode level current.erase).net (.inl ()),
    ∀ (p q : Path) (left right : List Path)
      (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right),
      ChainIncidenceIsomorphic (chainSyntaxIncidence current closed left)
        (chainSyntaxIncidence current closed right) ↔
        canonicalChainImage selection first=canonicalChainImage selection second := by
  obtain ⟨selection⟩ := (encode_closed_matches current.erase closed level).occurrence_fragment_selection closed
  exact ⟨selection,fun _ _ _ _ first second=>initial_chain_incidence_iff_blocks closed initial
    first second selection selection⟩

end Lamping.AG
