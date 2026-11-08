import Lamping.Lamping.ActionMatching
import Lamping.Lamping.Fixtures

namespace Lamping.Checks.Phase5Review.ActionCandidate
open AG Graph

private def kept : Unit → Label signature := fun _ => label .app 0

/-- The proposed finite fan0/lambda1 candidate, with a kept app0, one real W,
fan auxiliaries at appFun/appArg, and lambda body directly wired to binding.
It is a legitimate site but fails the structural balance prerequisite. -/
def site : PathSite (.fanAction .lam 0 1 (by decide)) kept
    (B:=Unit) (W:=Empty) (V:=Unit) where
  wire := {
    mate := fun e => match e with
      | .inl ⟨.inl _,.inl _⟩ => .inl ⟨.inr (.inl ()),.inr false⟩
      | .inl ⟨.inl _,.inr false⟩ => .inr (.inl ())
      | .inl ⟨.inl _,.inr true⟩ => .inl ⟨.inr (.inl ()),.inr true⟩
      | .inl ⟨.inr (.inl _),.inl _⟩ => .inr (.inr (.inr (),false))
      | .inl ⟨.inr (.inl _),.inr false⟩ => .inl ⟨.inl (),.inl ()⟩
      | .inl ⟨.inr (.inl _),.inr true⟩ => .inl ⟨.inl (),.inr true⟩
      | .inl ⟨.inr (.inr _),.inl _⟩ => .inr (.inr (.inr (),true))
      | .inl ⟨.inr (.inr _),.inr d⟩ => .inl ⟨.inr (.inr ()),.inr (!d)⟩
      | .inr (.inl _) => .inl ⟨.inl (),.inr false⟩
      | .inr (.inr (.inl w,_)) => nomatch w
      | .inr (.inr (.inr _,false)) => .inl ⟨.inr (.inl ()),.inl ()⟩
      | .inr (.inr (.inr _,true)) => .inl ⟨.inr (.inr ()),.inl ()⟩
    involutive := by
      rintro (⟨u|(u|u),p⟩ | (u | ⟨w|v,d⟩))
      · cases u; cases p with
        | inl u => cases u; rfl
        | inr d => cases d <;> rfl
      · cases u; cases p with
        | inl u => cases u; rfl
        | inr d => cases d <;> rfl
      · cases u; cases p with
        | inl u => cases u; rfl
        | inr d => cases d <;> rfl
      · cases u; rfl
      · exact nomatch w
      · cases v; cases d <;> rfl
    fixedPointFree := by
      rintro (⟨u|(u|u),p⟩ | (u | ⟨w|v,d⟩)) same
      · cases p with
        | inl u => cases same
        | inr d => cases d <;> cases same
      · cases p with
        | inl u => cases same
        | inr d => cases d <;> cases same
      · cases p with
        | inl u => cases same
        | inr d => cases d <;> cases same
      · cases same
      · exact nomatch w
      · cases d <;> cases same }
  internal := oneWireInternal
  connected := oneWireConnected
  wiring := by
    rintro (b | ⟨v,b⟩)
    · cases b <;> rfl
    · cases v; cases b <;> rfl

/-- A fan cannot connect both unequal app0 outgoing heights directly. -/
theorem fan_fun_arg_balance_impossible (heights : Unit → Int)
    (balance : LevelBalance site.net heights) : False := by
  have funWire := balance.wiring (.inl ⟨.inl (),.inl ()⟩)
  have argWire := balance.wiring (.inl ⟨.inl (),.inr true⟩)
  change balance.nodes (.inr (.inl ()))=(0 : Int) at funWire
  change balance.nodes (.inr (.inl ()))=(1 : Int) at argWire
  omega

/-- Independently, the direct lambda1 body/binding wire has unequal heights. -/
theorem body_binding_balance_impossible (heights : Unit → Int)
    (balance : LevelBalance site.net heights) : False := by
  have wire := balance.wiring (.inl ⟨.inr (.inr ()),lamBody⟩)
  change (2 : Int)=1 at wire
  omega

theorem no_indexed_balance (heights : Unit → Int) :
    ¬Nonempty (IndexedLevelBalance site.net heights) := by
  rintro ⟨balance⟩
  exact fan_fun_arg_balance_impossible heights balance.toLevelBalance

#print axioms fan_fun_arg_balance_impossible
#print axioms body_binding_balance_impossible
#print axioms no_indexed_balance
end Lamping.Checks.Phase5Review.ActionCandidate
