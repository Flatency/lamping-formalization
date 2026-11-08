import Lamping.Lamping.SuccessfulEndpointIso
import Lamping.Lamping.ChainFragmentUniqueness
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {current : LTerm} {g : Net signature N B W} {root : B}

/-- Corresponding syntax-edge paths retain their canonical source direction;
chase signs and a pointed starting node are not part of comparison. -/
def SameChainRepresentation (selection : OccurrenceFragmentSelection current g root)
    (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right) : Prop :=
  canonicalChainImage selection first=canonicalChainImage selection second

/-- REP's chain clause, as a proposition to be proved along the actual
history. No history, graph or match record assumes this conclusion. -/
def ChainRepresentationInvariant (closed : Closed current.erase)
    (selection : OccurrenceFragmentSelection current g root) : Prop :=
  ∀ {p q left right} (first : PrerequisiteChain current p left)
    (second : PrerequisiteChain current q right),
    SameChainRepresentation selection first second ↔
      ChainIncidenceIsomorphic (chainSyntaxIncidence current closed left)
        (chainSyntaxIncidence current closed right)

/-- Historical overstrong clause, retained only for the verified model counterexample. -/
def LegacyAuxiliarySeparation (closed : Closed current.erase)
    (selection : OccurrenceFragmentSelection current g root) : Prop :=
  ∀ (left right : SyntaxIncidence.Edge current),
    AuxiliaryAt current left.val → AuxiliaryAt current right.val →
    SyntaxIncidence.label current left=SyntaxIncidence.label current right →
    (selection left).fragment.segments≠(selection right).fragment.segments →
    ¬(PartialEndpointIso current closed (SyntaxIncidence.source current left)
        (SyntaxIncidence.source current right) ∧
      PartialEndpointIso current closed (SyntaxIncidence.target current closed left)
        (SyntaxIncidence.target current closed right))

/-- Compare only endpoints possessing actual successful prerequisite chains.
Undefined endpoints supply no isomorphism witness. -/
def AuxiliarySeparation (closed : Closed current.erase)
    (selection : OccurrenceFragmentSelection current g root) : Prop :=
  ∀ (left right : SyntaxIncidence.Edge current),
    AuxiliaryAt current left.val → AuxiliaryAt current right.val →
    SyntaxIncidence.label current left=SyntaxIncidence.label current right →
    (selection left).fragment.segments≠(selection right).fragment.segments →
    ¬(SuccessfulEndpointIso current closed (SyntaxIncidence.source current left)
        (SyntaxIncidence.source current right) ∧
      SuccessfulEndpointIso current closed (SyntaxIncidence.target current closed left)
        (SyntaxIncidence.target current closed right))

def JointRepresentation (closed : Closed current.erase)
    (selection : OccurrenceFragmentSelection current g root) : Prop :=
  ChainRepresentationInvariant closed selection ∧AuxiliarySeparation closed selection

theorem SameChainRepresentation.choice_independent (matching : Matches g root current.erase)
    (firstSelection secondSelection : OccurrenceFragmentSelection current g root)
    (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right) :
    SameChainRepresentation firstSelection first second ↔
      SameChainRepresentation secondSelection first second := by
  unfold SameChainRepresentation
  rw [canonicalChainImage_choice_independent matching firstSelection secondSelection first,
    canonicalChainImage_choice_independent matching firstSelection secondSelection second]

theorem ChainRepresentationInvariant.choice_independent (matching : Matches g root current.erase)
    (closed : Closed current.erase) (firstSelection secondSelection : OccurrenceFragmentSelection current g root) :
    ChainRepresentationInvariant closed firstSelection ↔ChainRepresentationInvariant closed secondSelection := by
  constructor
  · intro invariant p q left right first second
    exact (SameChainRepresentation.choice_independent matching firstSelection secondSelection first second).symm.trans
      (invariant first second)
  · intro invariant p q left right first second
    exact (SameChainRepresentation.choice_independent matching firstSelection secondSelection first second).trans
      (invariant first second)

theorem AuxiliarySeparation.choice_independent (matching : Matches g root current.erase)
    (closed : Closed current.erase) (firstSelection secondSelection : OccurrenceFragmentSelection current g root) :
    AuxiliarySeparation closed firstSelection ↔AuxiliarySeparation closed secondSelection := by
  have fragments (edge : SyntaxIncidence.Edge current) :
      (firstSelection edge).fragment.segments=(secondSelection edge).fragment.segments :=
    OccurrenceFragment.segments_unique matching _ _
  unfold AuxiliarySeparation
  simp only [fragments]

theorem JointRepresentation.choice_independent (matching : Matches g root current.erase)
    (closed : Closed current.erase) (firstSelection secondSelection : OccurrenceFragmentSelection current g root) :
    JointRepresentation closed firstSelection ↔JointRepresentation closed secondSelection := by
  exact and_congr (ChainRepresentationInvariant.choice_independent matching closed _ _)
    (AuxiliarySeparation.choice_independent matching closed _ _)
end
end Lamping.AG