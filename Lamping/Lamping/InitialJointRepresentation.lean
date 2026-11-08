import Lamping.Lamping.FamilyRepresentation
import Lamping.Lamping.InitialChainRepresentation
import Lamping.Lamping.InitLabelFragmentIdentity

namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {current : LTerm} {g : Net signature N B W} {root : B}

/-- Initial auxiliary separation follows from current INIT label uniqueness,
not from a supplied separation or graph representation certificate. -/
theorem init_auxiliary_separation (matching : Matches g root current.erase)
    (closed : Closed current.erase) (initial : INIT current)
    (selection : OccurrenceFragmentSelection current g root) :
    AuxiliarySeparation closed selection := by
  intro left right _leftAux _rightAux same different
  exact False.elim (init_label_different_fragments_impossible matching initial
    selection selection left right same different)
end

/-- Both REP clauses hold for the real initial encoding under any actual
selector. This is an initial instance, with no graph-step preservation claim. -/
theorem encode_initial_joint_representation (current : LTerm) (closed : Closed current.erase)
    (initial : INIT current) (level : Nat)
    (selection : OccurrenceFragmentSelection current (encode level current.erase).net (.inl ())) :
    JointRepresentation closed selection := by
  constructor
  · intro p q left right first second
    exact (initial_chain_incidence_iff_blocks closed initial first second selection selection).symm
  · exact init_auxiliary_separation (encode_closed_matches current.erase closed level)
      closed initial selection

/-- The graph supplies ONE actual occurrence selector and both initial
invariants from closed syntax. Neither invariant is an input field. -/
theorem encode_initial_joint_realization (current : LTerm) (closed : Closed current.erase)
    (initial : INIT current) (level : Nat) :
    ∃ selection : OccurrenceFragmentSelection current (encode level current.erase).net (.inl ()),
      JointRepresentation closed selection := by
  obtain ⟨selection⟩ := (encode_closed_matches current.erase closed level).occurrence_fragment_selection closed
  exact ⟨selection,encode_initial_joint_representation current closed initial level selection⟩

end Lamping.AG
