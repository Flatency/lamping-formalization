import Lamping.Lamping.BalancedPrincipalRoutes
import Lamping.Lamping.Fixtures
namespace Lamping.Checks.LevelBalance
open AG Graph Lambda

private abbrev croSchema : Schema := .croAction .cro 0 1 (by decide)
private def croSource : LevelBalance croSchema.left (fun _ => 0) where
  nodes := fun _ => 0
  vertices := Empty.elim
  wiring := by
    rintro (⟨u|u,p⟩ | ((a|a) | ⟨w,d⟩))
    · cases p <;> rfl
    · cases p <;> rfl
    · rfl
    · rfl
    · exact nomatch w
private def croTarget : LevelBalance croSchema.right.net (fun _ => 0) :=
  croRight_balance .cro 0 1 (by decide) 0 0 _ rfl (fun _ => rfl) rfl
example : croTarget.nodes (.inl ())=(-1 : Int) := rfl
example : croTarget.nodes (.inr ())=(-1 : Int) := rfl
example : Nonempty (LevelBalance croSchema.right.net (fun _ => 0)) :=
  croSchema.balance_preservation _ croSource

-- This different-index principal pair is a genuine finite graph, but its
-- wiring cannot admit a LevelBalance potential.
example (boundary : Bool⊕Bool → Int) : ¬Nonempty (LevelBalance (leftNet .app .lam 0 1) boundary) := by
  rintro ⟨balance⟩
  have impossible := balance.proper_principal_indices (.inl ()) (.inr ()) (.inl ()) (.inl ())
    .app .lam 0 1 rfl rfl (Or.inl rfl) (Or.inr rfl) HEq.rfl HEq.rfl rfl
  omega

private def kept : Empty → Label signature := Empty.elim
private def betaSite : PathSite (.beta 2) kept (B:=Bool⊕Bool) (W:=Empty) (V:=Unit) where
  wire := {
    mate := fun e => match e with
      | .inl ⟨.inl k,_⟩ => nomatch k
      | .inl ⟨.inr (.inl _),.inl _⟩ => .inr (.inr (.inr (),false))
      | .inl ⟨.inr (.inr _),.inl _⟩ => .inr (.inr (.inr (),true))
      | .inl ⟨.inr (.inl _),.inr a⟩ => .inr (.inl (.inl a))
      | .inl ⟨.inr (.inr _),.inr a⟩ => .inr (.inl (.inr a))
      | .inr (.inl (.inl a)) => .inl ⟨.inr (.inl ()),.inr a⟩
      | .inr (.inl (.inr a)) => .inl ⟨.inr (.inr ()),.inr a⟩
      | .inr (.inr (.inl w,_)) => nomatch w
      | .inr (.inr (.inr _,false)) => .inl ⟨.inr (.inl ()),.inl ()⟩
      | .inr (.inr (.inr _,true)) => .inl ⟨.inr (.inr ()),.inl ()⟩
    involutive := by
      rintro (⟨k|(u|u),p⟩ | ((a|a) | ⟨w|v,d⟩))
      · exact nomatch k
      · cases u; cases p with | inl u => cases u; rfl | inr a => rfl
      · cases u; cases p with | inl u => cases u; rfl | inr a => rfl
      · rfl
      · rfl
      · exact nomatch w
      · cases v; cases d <;> rfl
    fixedPointFree := by
      rintro (⟨k|(u|u),p⟩ | ((a|a) | ⟨w|v,d⟩)) same
      · exact nomatch k
      · cases p <;> cases same
      · cases p <;> cases same
      · cases same
      · cases same
      · exact nomatch w
      · cases d <;> cases same }
  internal := oneWireInternal
  connected := oneWireConnected
  wiring := by
    rintro (b | ⟨v,b⟩)
    · cases b <;> rfl
    · cases v; cases b <;> rfl

private def betaBoundary : Bool⊕Bool → Int
  | .inl false | .inr true => 2
  | .inl true | .inr false => 3
private def betaBalance : LevelBalance betaSite.net betaBoundary where
  nodes := fun _ => 0
  vertices := fun _ => 2
  wiring := by
    rintro (⟨k|(u|u),p⟩ | ((a|a) | ⟨w|v,d⟩))
    · exact nomatch k
    · cases p with | inl u => rfl | inr a => cases a <;> rfl
    · cases p with | inl u => rfl | inr a => cases a <;> rfl
    · cases a <;> rfl
    · cases a <;> rfl
    · exact nomatch w
    · cases d <;> rfl

example : Nonempty (LevelBalance betaSite.reduce betaBoundary) := betaSite.reduce_balance betaBalance
example : Nonempty (LevelBalance (ActualNet.ofNet betaSite.reduce).net betaBoundary) :=
  (GraphStep.site kept betaSite).balance betaBalance
example (t : Term) (target : ActualNet (Boundary t)) (ss : List Schema)
    (trace : GraphTrace (ActualNet.initial t) target ss) :
    Nonempty (LevelBalance target.net (boundaryDepthAt 0)) := initial_trace_balance t target ss trace
#print axioms Schema.balance_preservation
#print axioms PathSite.reduce_balance
#print axioms initial_trace_balance
#print axioms reachable_proper_principal_indices
end Lamping.Checks.LevelBalance
