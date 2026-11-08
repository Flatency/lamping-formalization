import Lamping.Lamping.GraphIndexedBalance
import Lamping.Lamping.HighTailTransport
namespace Lamping.Checks.Phase5Review.IndexedBounds
open AG Graph Lambda

abbrev nonzeroSchema : Schema := .croAction .cro 2 3 (by decide)
def nonzeroSource : IndexedLevelBalance nonzeroSchema.left (fun _ => 3) where
  nodes := fun _ => 3
  vertices := Empty.elim
  wiring := by
    rintro (⟨u|u,p⟩ | ((a|a) | ⟨w,d⟩))
    · cases p <;> rfl
    · cases p <;> rfl
    · rfl
    · rfl
    · exact nomatch w
  bounded := by rintro (u|u) <;> cases u <;> change (_ : Int) ≤ 3 <;> decide

def nonzeroTarget : IndexedLevelBalance nonzeroSchema.right.net (fun _ => 3) where
  toLevelBalance := croRight_balance .cro 2 3 (by decide) 3 3 _ rfl (fun _ => rfl) rfl
  bounded := by rintro (u|u) <;> change (2 : Int) ≤ 2 <;> omega

example : nonzeroTarget.nodes (.inl ())=(2 : Int) := rfl
example : nonzeroTarget.nodes (.inr ())=(2 : Int) := rfl
theorem actual_nonzero_schema : Nonempty (IndexedLevelBalance nonzeroSchema.right.net (fun _ => 3)) :=
  nonzeroSchema.indexed_balance_preservation _ nonzeroSource

-- Cro equality is legal; Fan and Bra equality must both be rejected.
example : ControlIndexBound (label .cro 3) 3 := by change (3 : Int) ≤ 3; omega
example : ¬ControlIndexBound (label .fan 3) 3 := by change ¬(3 : Int)<3; omega
example : ¬ControlIndexBound (label .bra 3) 3 := by change ¬(3 : Int)<3; omega
example : ControlIndexBound (label .bra 3) 4 := by change (3 : Int)<4; omega

-- The rejected weak Bra equality also has a genuine traversal countercheck.
example : Traversal 0 (.op .bra) (.inr ()) (.inl ())
    ((Context.empty.cons (.star .empty)).cons .empty)
    (Context.empty.cons (.pair (.star .empty) .empty)) := bra_equal_height_actual
example : ¬∀ replacement : Context, Traversal 0 (.op .bra) (.inr ()) (.inl ())
    (((Context.empty.cons (.star .empty)).cons .empty).replace 1 replacement)
    ((Context.empty.cons (.pair (.star .empty) .empty)).replace 0 replacement) := bra_equal_height_no_sync

example (t : Term) : Nonempty (IndexedLevelBalance (encode 7 t).net (boundaryDepthAt 7)) :=
  encode_indexed_balance t 7
example (t : Term) (target : ActualNet (Boundary t)) (ss : List Schema)
    (trace : GraphTrace (ActualNet.initial t) target ss) :
    Nonempty (IndexedLevelBalance target.net (boundaryDepthAt 0)) := initial_trace_indexed_balance t target ss trace
#print axioms Schema.indexed_balance_preservation
#print axioms GraphTrace.indexed_balance
#print axioms initial_trace_indexed_balance
#print axioms actual_nonzero_schema
#print axioms bra_equal_height_no_sync
end Lamping.Checks.Phase5Review.IndexedBounds

