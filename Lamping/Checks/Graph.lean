import Lamping.Graph.Examples
open Lamping.Graph

-- Named roles, original self-loop, and distinct parallel wires.
example : fixtureSignature.principal () = some .principal := rfl
example : ThreePort.left ≠ ThreePort.right := by decide
example : selfLoopOriginal.wire (.inl ⟨.inr false,.left⟩) = .inl ⟨.inr false,.right⟩ := rfl
example : parallelOriginal.wire (.inl ⟨.inr false,.left⟩) = .inl ⟨.inr true,.left⟩ := rfl
example : parallelOriginal.wire (.inl ⟨.inr false,.right⟩) = .inl ⟨.inr true,.right⟩ := rfl
-- The principal line is subdivided before deletion.
example : parallelOriginal.wire (.inl ⟨.inr false,.principal⟩) = .inr (.inr (.inr (),false)) := rfl
-- Exact output type: selected old wire vertex Unit has disappeared; the four
-- remaining wire vertices are the frontier Bool×Bool. There are no nodes.
example : Net fixtureSignature (Empty ⊕ Empty) Empty ((Empty ⊕ Empty) ⊕ (Bool × Bool)) := annihilated
example (n d : Bool) : annihilated.wire (.inr (.inr (.inr (n,d),false))) =
    .inr (.inr (.inr (!n,d),false)) := annihilated_outer n d
example (n d : Bool) : annihilated.wire (.inr (.inr (.inr (n,d),true))) =
    .inr (.inr (.inr (!n,d),true)) := annihilated_inner n d
-- Countercheck: a different peripheral self-loop gives a different matching.
example : annihilated.wire (.inr (.inr (.inr (false,false),false))) ≠
    .inr (.inr (.inr (false,true),false)) := by intro h; cases h
example : selfLoopAnnihilated.wire (.inr (.inr (.inr (false,false),false))) =
    .inr (.inr (.inr (false,true),false)) := rfl
-- Closing already mutually connected boundaries retains a pure wire circle.
example : closedCircle.wire (.inr (.inr (.inr (),false))) =
    .inr (.inr (.inr (),true)) := rfl
example : closedCircle.wire (.inr (.inr (.inr (),true))) =
    .inr (.inr (.inr (),false)) := rfl
example : closedCircle.wire (.inr (.inr (.inr (),false))) ≠
    .inr (.inr (.inr (),false)) := by intro h; cases h
-- Nonempty ordered boundary completeness and uniqueness are universal facts.
example : boundaryWire.boundaryOrder.Nodup := boundaryWire.boundaryOrder_nodup
example (b : Empty ⊕ (Unit × Bool)) : b ∈ boundaryWire.boundaryOrder := boundaryWire.boundaryOrder_complete b
example : NetIso parallelOriginal parallelOriginal := NetIso.refl _
example : NetIso parallelOriginal parallelOriginal := (NetIso.refl parallelOriginal).symm.trans (NetIso.refl _)
#check restrict_natural
#check plug_natural
#check cutFragment_boundary
#check replace_boundary
#print axioms NetIso.symm
#print axioms NetIso.trans
#print axioms restrict_natural
#print axioms plug_natural
#print axioms replace_pairing
#print axioms replace_boundary
#print axioms annihilated_outer
#print axioms closedCircle_mate
