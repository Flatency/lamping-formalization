import Lamping.Lamping.ControlPrincipalTags
namespace Lamping.AG

/-- The selected schema labels exactly the two physical principal endpoints,
possibly reversing their orientation. -/
def Schema.FitsControlPair (schema : Schema) (left right : Op) (i j : Nat) : Prop :=
  (schema.active=left ∧schema.passive=right ∧schema.low=i ∧schema.high=j) ∨
  (schema.active=right ∧schema.passive=left ∧schema.low=j ∧schema.high=i)

/-- A labelled control/control principal connection always admits an actual
standard cancellation or action schema. At equal index the real marker
images exclude mixed kinds; unequal indices select the lower active control. -/
theorem Traversal.control_pair_schema {i j : Nat} {left right : Op}
    (leftControl : left=.fan ∨left=.cro ∨left=.bra)
    (rightControl : right=.fan ∨right=.cro ∨right=.bra)
    {p : Port (.op left)} {q : Port (.op right)} {a b c : Context}
    (leftTurn : Traversal i (.op left) p (.inl ()) a b)
    (rightTurn : Traversal j (.op right) (.inl ()) q b c) :
    ∃ schema : Schema,schema.FitsControlPair left right i j := by
  by_cases equal : i=j
  · subst j
    have same := leftTurn.equal_index_control_principals leftControl rightControl rightTurn
    subst right
    rcases leftControl with same |same |same <;> subst left
    · exact ⟨.fanCancel i,Or.inl ⟨rfl,rfl,rfl,rfl⟩⟩
    · exact ⟨.croCancel i,Or.inl ⟨rfl,rfl,rfl,rfl⟩⟩
    · exact ⟨.braCancel i,Or.inl ⟨rfl,rfl,rfl,rfl⟩⟩
  · rcases Nat.lt_or_gt_of_ne equal with lower |higher
    · rcases leftControl with same |same |same <;> subst left
      · exact ⟨.fanAction right i j lower,Or.inl ⟨rfl,rfl,rfl,rfl⟩⟩
      · exact ⟨.croAction right i j lower,Or.inl ⟨rfl,rfl,rfl,rfl⟩⟩
      · exact ⟨.braAction right i j lower,Or.inl ⟨rfl,rfl,rfl,rfl⟩⟩
    · rcases rightControl with same |same |same <;> subst right
      · exact ⟨.fanAction left j i higher,Or.inr ⟨rfl,rfl,rfl,rfl⟩⟩
      · exact ⟨.croAction left j i higher,Or.inr ⟨rfl,rfl,rfl,rfl⟩⟩
      · exact ⟨.braAction left j i higher,Or.inr ⟨rfl,rfl,rfl,rfl⟩⟩
end Lamping.AG
