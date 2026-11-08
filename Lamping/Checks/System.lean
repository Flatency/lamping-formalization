import Lamping.Lamping.System
import Lamping.Lamping.Encoding
import Lamping.Lamping.PathRewrite
namespace Lamping.Checks.System
open Lamping.Graph Lamping.AG Lamping.Lambda

example : signature.principal .garbage = none := rfl
example : garbage.index = 0 := rfl
example : (Schema.beta 2).left.wire (.inl ⟨.inl (), .inl ()⟩) =
    .inl ⟨.inr (), .inl ()⟩ := rfl
example : (Schema.beta 2).right.net.wire (.inr (.inl (.inl false))) =
    .inr (.inl (.inr true)) := rfl
example : (Schema.beta 2).right.net.wire (.inr (.inl (.inl true))) =
    .inr (.inl (.inr false)) := rfl
example : (Schema.fanCancel 2).right.net.wire (.inr (.inl (.inl false))) =
    .inr (.inl (.inr false)) := rfl
example : (Schema.fanCancel 2).right.net.wire (.inr (.inl (.inl true))) =
    .inr (.inl (.inr true)) := rfl
example : (Schema.croCancel 2).right.net.wire (.inr (.inl (.inl ()))) =
    .inr (.inl (.inr ())) := rfl
example : (Schema.braCancel 2).right.net.wire (.inr (.inl (.inl ()))) =
    .inr (.inl (.inr ())) := rfl
example (i : Nat) : ¬ i < i := Nat.lt_irrefl i
example (i j : Nat) (h : i < j) : 0 < j ∧ j-1+1=j := cro_action_no_underflow i j h

example : (Schema.fanAction .app 1 3 (by decide)).right.net.label (.inl false) = label .app 3 := rfl
example : (Schema.fanAction .app 1 3 (by decide)).right.net.label (.inr true) = label .fan 1 := rfl
example : (Schema.croAction .lam 1 3 (by decide)).right.net.label (.inl ()) = label .lam 2 := rfl
example : (Schema.croAction .lam 1 3 (by decide)).right.net.label (.inr false) = label .cro 1 := rfl
example : (Schema.braAction .lam 1 3 (by decide)).right.net.label (.inl ()) = label .lam 4 := rfl
example : (Schema.braAction .lam 1 3 (by decide)).right.net.label (.inr true) = label .bra 1 := rfl
example : (fanRight .app 1 3).wire (.inl ⟨.inl true,.inr false⟩) =
    .inl ⟨.inr false,.inr true⟩ := rfl
example : (unaryRight .cro .lam 1 3).wire (.inl ⟨.inl (),.inr false⟩) =
    .inl ⟨.inr false,.inr ()⟩ := rfl

example : (varNet 3 0).wire (.inr (.inl (.inl ()))) = .inl ⟨(),.inr ()⟩ := rfl
example : (varNet 3 0).wire (.inr (.inl (.inr ⟨0,rfl⟩))) = .inl ⟨(),.inl ()⟩ := rfl
example : (encode 3 (.lam (.var 0))).net.label (.inr ()) = label .cro 3 := rfl
example : (encode 3 (.lam (.lam (.var 0)))).net.label (.inl (.inr ())) = garbage := rfl
example : (encode 3 (.app (.var 0) (.var 0))).net.label (.inr (.inl ())) = label .cro 3 := rfl
example : (encode 3 (.app (.var 0) (.var 0))).net.label (.inr (.inr ())) = label .cro 4 := rfl
example : (encode 3 (.app (.var 0) (.var 0))).net.label
    (.inl (.inr (.inl ⟨0,rfl⟩))) = label .bra 3 := rfl
example : (encode 3 (.app (.var 0) (.var 0))).net.label
    (.inl (.inr (.inr ⟨⟨0,rfl⟩,rfl⟩))) = label .fan 3 := rfl
example : (encode 3 (.app (.lam (.var 0)) (.var 0))).net.label
    (.inl (.inr (.inl ⟨0,rfl⟩))) = label .bra 3 := rfl
example : (appPatch 3 (.var 0) (.var 0)).wire
    (.inl ⟨.inr (.inr ⟨⟨0,rfl⟩,rfl⟩),.inr false⟩) =
    .inr (.inl (.inr (.inl (.inr ⟨0,rfl⟩)))) := rfl
example : (appPatch 3 (.var 0) (.var 0)).wire
    (.inl ⟨.inr (.inr ⟨⟨0,rfl⟩,rfl⟩),.inr true⟩) =
    .inl ⟨.inr (.inl ⟨0,rfl⟩),.inl ()⟩ := rfl
example (n : Nat) (t : Term) (ht : Closed t) :
    (encode n t).net.boundaryOrder = [Sum.inl ()] := closed_boundary_order n t ht

#print axioms cro_action_no_underflow
#print axioms Site.reduce_pairing
#print axioms Site.reduce_boundary
#print axioms PathSite.closed
#print axioms PathSite.reduce_pairing
#print axioms PathSite.reduce_boundary
#print axioms encode_pairing
#print axioms closed_boundary_order
end Lamping.Checks.System
