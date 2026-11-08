import Lamping.Lamping.MarkerExpressionContexts
import Lamping.Lamping.PathLabelDeterminism
namespace Lamping.AG.Marker
open Graph

namespace LevelExpr
theorem o_shape_total (a : LevelExpr)
    (total : ∀ input : Context, ∃ b, a.eval input.get=.o b) : ∃ b,a=.o b := by
  cases a with
  | o b => exact ⟨b,rfl⟩
  | empty => obtain ⟨b,impossible⟩ := total Context.empty; cases impossible
  | star a => obtain ⟨b,impossible⟩ := total Context.empty; cases impossible
  | pair a b => obtain ⟨c,impossible⟩ := total Context.empty; cases impossible
  | var k => obtain ⟨b,impossible⟩ := total Context.empty; cases impossible

theorem star_shape_total (a : LevelExpr)
    (total : ∀ input : Context, ∃ b, a.eval input.get=.star b) : ∃ b,a=.star b := by
  cases a with
  | star b => exact ⟨b,rfl⟩
  | empty => obtain ⟨b,impossible⟩ := total Context.empty; cases impossible
  | o a => obtain ⟨b,impossible⟩ := total Context.empty; cases impossible
  | pair a b => obtain ⟨c,impossible⟩ := total Context.empty; cases impossible
  | var k => obtain ⟨b,impossible⟩ := total Context.empty; cases impossible

theorem pair_shape_total (a : LevelExpr)
    (total : ∀ input : Context, ∃ b c, a.eval input.get=.pair b c) : ∃ b c,a=.pair b c := by
  cases a with
  | pair b c => exact ⟨b,c,rfl⟩
  | empty => obtain ⟨b,c,impossible⟩ := total Context.empty; cases impossible
  | o a => obtain ⟨b,c,impossible⟩ := total Context.empty; cases impossible
  | star a => obtain ⟨b,c,impossible⟩ := total Context.empty; cases impossible
  | var k => obtain ⟨b,c,impossible⟩ := total Context.empty; cases impossible

theorem empty_total (a : LevelExpr) (total : ∀ input : Context, a.eval input.get=.empty) : a=.empty := by
  cases a with
  | empty => rfl
  | o a => have impossible := total Context.empty; cases impossible
  | star a => have impossible := total Context.empty; cases impossible
  | pair a b => have impossible := total Context.empty; cases impossible
  | var k =>
    have impossible := total (Context.empty.replace k (Context.empty.cons (.star .empty)))
    change (Context.empty.replace k (Context.empty.cons (.star .empty))).get k=.empty at impossible
    rw [Context.replace_high _ _ (Nat.le_refl k),Nat.sub_self] at impossible
    cases impossible
end LevelExpr

/-- Only inverse controls impose a constructor test on their arriving level.
The predicate is proved from actual Traversal below, not assumed total. -/
def InputShape (i : Nat) : (kind : Kind) → Port kind → Port kind → Context → Prop
  | .op .fan,.inl _,.inr false,a => ∃ x,a.get i=.o x
  | .op .fan,.inl _,.inr true,a => ∃ x,a.get i=.star x
  | .op .cro,.inl _,.inr _,a => a.get i=.empty
  | .op .bra,.inl _,.inr _,a => ∃ x y,a.get i=.pair x y
  | _,_,_,_ => True

theorem input_shape {i kind p q a b} (rule : Traversal i kind p q a b) : InputShape i kind p q a := by
  cases rule with
  | direct passage => cases passage <;> trivial
  | inverse passage =>
    cases passage with
    | fanO a b x => exact ⟨x,by simp [Context.replace,Context.cons]⟩
    | fanStar a b x => exact ⟨x,by simp [Context.replace,Context.cons]⟩
    | cro a b => simp [InputShape,Context.replace,Context.cons]
    | bra a b x y => exact ⟨x,y,by simp [Context.replace,Context.cons]⟩
    | appFun a => trivial
    | appArg a => trivial
    | lamBody a => trivial

def ExprInputShape (i : Nat) : (kind : Kind) → Port kind → Port kind → ExprContext → Prop
  | .op .fan,.inl _,.inr false,a => ∃ x,a.get i=.o x
  | .op .fan,.inl _,.inr true,a => ∃ x,a.get i=.star x
  | .op .cro,.inl _,.inr _,a => a.get i=.empty
  | .op .bra,.inl _,.inr _,a => ∃ x y,a.get i=.pair x y
  | _,_,_,_ => True

/-- A constructor read by a total-input actual turn is a genuine written
expression constructor. A free variable cannot be treated as an invertible
O/Star/Pair/Empty input by assuming a total inverse. -/
theorem expression_input_shape (i : Nat) (kind : Kind) (p q : Port kind) (a : ExprContext)
    (total : ∀ input : Context, ∃ output, Traversal i kind p q (a.eval input) output) :
    ExprInputShape i kind p q a := by
  have shape : ∀ input : Context, InputShape i kind p q (a.eval input) := by
    intro input
    obtain ⟨output,rule⟩ := total input
    exact input_shape rule
  cases kind with
  | garbage => trivial
  | op op =>
    cases op with
    | app => trivial
    | lam => trivial
    | fan =>
      cases p with
      | inr branch => trivial
      | inl u =>
        cases q with
        | inl v => trivial
        | inr branch =>
          cases branch with
          | false => exact (a.get i).o_shape_total shape
          | true => exact (a.get i).star_shape_total shape
    | cro =>
      cases p with
      | inr u => trivial
      | inl u => cases q with
        | inl v => trivial
        | inr v => exact (a.get i).empty_total shape
    | bra =>
      cases p with
      | inr u => trivial
      | inl u => cases q with
        | inl v => trivial
        | inr v => exact (a.get i).pair_shape_total shape
end Lamping.AG.Marker
