import Lamping.Lamping.InitialJointRepresentation

namespace Lamping.Checks.InitialJointRepresentation
open AG Graph Lambda Lambda.Labelled

/-- Every closed source and every initial level supplies both invariants;
this consumer supplies no selector, REP or auxiliary-separation witness. -/
theorem all_closed_initial_joint (term : Term) (closed : Closed term) (level : Nat) :
    ∃ selection : OccurrenceFragmentSelection (initLabels term) (encode level (initLabels term).erase).net (.inl ()),
      JointRepresentation (show Closed (initLabels term).erase from by
        simpa only [erase_initLabels] using closed) selection := by
  have initialClosed : Closed (initLabels term).erase := by
    simpa only [erase_initLabels] using closed
  exact
    (encode_initial_joint_realization (initLabels term) initialClosed (init_is_INIT term) level)

/-- A real sharing-Fan source at a nonzero initial level exercises the
joint producer rather than assuming either representation clause. -/
theorem actual_shared_level_seven_joint :
    ∃ selection : OccurrenceFragmentSelection
      (initLabels (.lam (.app (.var 0) (.var 0))))
      (encode 7 (.lam (.app (.var 0) (.var 0)))).net (.inl ()),
      JointRepresentation (show Closed
        (initLabels (.lam (.app (.var 0) (.var 0)))).erase from
          ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩) selection :=
  all_closed_initial_joint (.lam (.app (.var 0) (.var 0)))
    ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩ 7

/-- Both projections really follow from the generated joint instance. -/
theorem actual_shared_level_seven_clauses :
    ∃ selection : OccurrenceFragmentSelection
      (initLabels (.lam (.app (.var 0) (.var 0))))
      (encode 7 (.lam (.app (.var 0) (.var 0)))).net (.inl ()),
      ChainRepresentationInvariant
        (show Closed (initLabels (.lam (.app (.var 0) (.var 0)))).erase from
          ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩) selection ∧
      AuxiliarySeparation
        (show Closed (initLabels (.lam (.app (.var 0) (.var 0)))).erase from
          ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩) selection :=
  actual_shared_level_seven_joint

#print axioms init_auxiliary_separation
#print axioms encode_initial_joint_representation
#print axioms encode_initial_joint_realization
#print axioms all_closed_initial_joint
#print axioms actual_shared_level_seven_joint
end Lamping.Checks.InitialJointRepresentation
