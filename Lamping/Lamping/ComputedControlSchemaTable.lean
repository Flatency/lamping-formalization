import Lamping.Lamping.ControlInteractionSchema

namespace Lamping.AG.ExposureScheduling

private def lowerControlSchema (active passive : Op) (i j : Nat) : Option Schema :=
  if lower : i<j then
    match active with
    | .fan => some (.fanAction passive i j lower)
    | .cro => some (.croAction passive i j lower)
    | .bra => some (.braAction passive i j lower)
    | _ => none
  else none

/-- Schema and physical orientation are computed solely from actual operation
kinds and indices. True means reverse the original left-to-right corridor. -/
def computeControlPairSchema (left right : Op) (i j : Nat) : Option (Schema × Bool) :=
  if i=j then
    match left,right with
    | .fan,.fan => some (.fanCancel i,false)
    | .cro,.cro => some (.croCancel i,false)
    | .bra,.bra => some (.braCancel i,false)
    | _,_ => none
  else if i<j then
    (lowerControlSchema left right i j).map fun schema => (schema,false)
  else
    (lowerControlSchema right left j i).map fun schema => (schema,true)

/-- This predicate checks the computed orientation; it stores no desired schema
or semantic witness in the returned runtime data. -/
def OrientedControlSchemaFits (selected : Schema × Bool) (left right : Op) (i j : Nat) : Prop :=
  if selected.2 then
    selected.1.active=right ∧ selected.1.passive=left ∧ selected.1.low=j ∧ selected.1.high=i
  else
    selected.1.active=left ∧ selected.1.passive=right ∧ selected.1.low=i ∧ selected.1.high=j

/-- Actual adjacent principal traversals make the computed table succeed.
At equal index the real traversal law excludes mixed control kinds. This is
a Prop correctness theorem for an independently defined finite computation. -/
theorem computeControlPairSchema_correct {i j : Nat} {left right : Op}
    (leftControl : left=.fan ∨left=.cro ∨left=.bra)
    (rightControl : right=.fan ∨right=.cro ∨right=.bra)
    {p : Port (.op left)} {q : Port (.op right)} {a b c : Context}
    (leftTurn : Traversal i (.op left) p (Sum.inl ()) a b)
    (rightTurn : Traversal j (.op right) (Sum.inl ()) q b c) :
    ∃ selected,computeControlPairSchema left right i j=some selected ∧
      OrientedControlSchemaFits selected left right i j := by
  by_cases equal : i=j
  · subst j
    have same := leftTurn.equal_index_control_principals leftControl rightControl rightTurn
    subst right
    rcases leftControl with same|same|same <;> subst left
    · refine ⟨(.fanCancel i,false),?_,⟨rfl,rfl,rfl,rfl⟩⟩
      unfold computeControlPairSchema
      rw [if_pos (rfl : i=i)] <;> rfl
    · refine ⟨(.croCancel i,false),?_,⟨rfl,rfl,rfl,rfl⟩⟩
      unfold computeControlPairSchema
      rw [if_pos (rfl : i=i)] <;> rfl
    · refine ⟨(.braCancel i,false),?_,⟨rfl,rfl,rfl,rfl⟩⟩
      unfold computeControlPairSchema
      rw [if_pos (rfl : i=i)] <;> rfl
  · by_cases lower : i<j
    · rcases leftControl with same|same|same <;> subst left
      · refine ⟨(.fanAction right i j lower,false),?_,⟨rfl,rfl,rfl,rfl⟩⟩
        unfold computeControlPairSchema
        rw [if_neg equal,if_pos lower]
        unfold lowerControlSchema
        rw [dif_pos lower] <;> rfl
      · refine ⟨(.croAction right i j lower,false),?_,⟨rfl,rfl,rfl,rfl⟩⟩
        unfold computeControlPairSchema
        rw [if_neg equal,if_pos lower]
        unfold lowerControlSchema
        rw [dif_pos lower] <;> rfl
      · refine ⟨(.braAction right i j lower,false),?_,⟨rfl,rfl,rfl,rfl⟩⟩
        unfold computeControlPairSchema
        rw [if_neg equal,if_pos lower]
        unfold lowerControlSchema
        rw [dif_pos lower] <;> rfl
    · have higher : j<i := by omega
      rcases rightControl with same|same|same <;> subst right
      · refine ⟨(.fanAction left j i higher,true),?_,⟨rfl,rfl,rfl,rfl⟩⟩
        unfold computeControlPairSchema
        rw [if_neg equal,if_neg lower]
        unfold lowerControlSchema
        rw [dif_pos higher] <;> rfl
      · refine ⟨(.croAction left j i higher,true),?_,⟨rfl,rfl,rfl,rfl⟩⟩
        unfold computeControlPairSchema
        rw [if_neg equal,if_neg lower]
        unfold lowerControlSchema
        rw [dif_pos higher] <;> rfl
      · refine ⟨(.braAction left j i higher,true),?_,⟨rfl,rfl,rfl,rfl⟩⟩
        unfold computeControlPairSchema
        rw [if_neg equal,if_neg lower]
        unfold lowerControlSchema
        rw [dif_pos higher] <;> rfl
end Lamping.AG.ExposureScheduling
