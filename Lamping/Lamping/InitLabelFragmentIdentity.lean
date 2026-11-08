import Lamping.Lamping.ChainInitialRigidity
import Lamping.Lamping.ChainFragmentUniqueness

namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {current : LTerm} {g : Net signature N B W} {root : B}

/-- This uses INIT of the CURRENT syntax term. It must not be applied to a
noninitial intermediate term by resetting the original labels. No graph
history or representation invariant is assumed. -/
theorem init_label_fragment_identity
    (matching : Matches g root current.erase) (initial : INIT current)
    (selectLeft selectRight : OccurrenceFragmentSelection current g root)
    (left right : SyntaxIncidence.Edge current)
    (same : SyntaxIncidence.label current left=SyntaxIncidence.label current right) :
    left=right ∧(selectLeft left).fragment.segments=(selectRight right).fragment.segments := by
  have equal := syntaxIncidence_label_injective current initial.2 left right same
  subst right
  exact ⟨rfl,OccurrenceFragment.segments_unique matching _ _⟩

/-- In particular, the same-label/different-representation premise of the
auxiliary separation condition cannot occur at the initial labelled term.
This is its initial base, not preservation at later graph states. -/
theorem init_label_different_fragments_impossible
    (matching : Matches g root current.erase) (initial : INIT current)
    (selectLeft selectRight : OccurrenceFragmentSelection current g root)
    (left right : SyntaxIncidence.Edge current)
    (same : SyntaxIncidence.label current left=SyntaxIncidence.label current right)
    (different : (selectLeft left).fragment.segments≠(selectRight right).fragment.segments) : False :=
  different (init_label_fragment_identity matching initial selectLeft selectRight left right same).2
end
end Lamping.AG
