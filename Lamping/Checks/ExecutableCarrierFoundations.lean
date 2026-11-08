import Lamping.Graph.ExecutableCarrierRenaming
import Lamping.Graph.ExecutableFinitePartition

namespace Lamping.Checks.ExecutableCarrierFoundations
open Lamping.Graph

private def sig : Signature where
  Kind := Bool
  Port k := match k with | false => Unit | true => Bool
  finitePort k := by cases k <;> infer_instance
  principal k := match k with | false => some () | true => some false

private def oldLabels (n : Fin 3) : Label sig :=
  match n.val with
  | 0 => ⟨false, 0⟩
  | _ => ⟨true, n.val⟩

private theorem threeCases (n : Fin 3) : n = 0 ∨ n = 1 ∨ n = 2 := by omega
private theorem tenCases (n : Fin 10) :
    n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 := by omega

private def nodes : Bij (Fin 3) (Fin 3) where
  toFun n := if n = 0 then 2 else if n = 1 then 0 else 1
  invFun n := if n = 0 then 1 else if n = 1 then 2 else 0
  left_inv n := by rcases threeCases n with h | h | h <;> subst n <;> decide
  right_inv n := by rcases threeCases n with h | h | h <;> subst n <;> decide

private def freshLabels (n : Fin 3) : Label sig := oldLabels (nodes n)
private theorem compatible (n : Fin 3) : oldLabels (nodes n) = freshLabels n := rfl

private def vertices : Bij (Fin 2) (Fin 2) where
  toFun n := if n = 0 then 1 else 0
  invFun n := if n = 0 then 1 else 0
  left_inv n := by
    have h : n = 0 ∨ n = 1 := by omega
    rcases h with h | h <;> subst n <;> decide
  right_inv n := by
    have h : n = 0 ∨ n = 1 := by omega
    rcases h with h | h <;> subst n <;> decide

private abbrev OldPort := NodePort sig (Fin 3) oldLabels
private abbrev FreshPort := NodePort sig (Fin 3) freshLabels
private abbrev OldEnd := End sig (Fin 3) (Fin 1) (Fin 2) oldLabels
private abbrev FreshEnd := End sig (Fin 3) (Fin 1) (Fin 2) freshLabels
private def oldP0 : OldPort := ⟨0, ()⟩
private def oldP1f : OldPort := ⟨1, false⟩
private def oldP1t : OldPort := ⟨1, true⟩
private def oldP2f : OldPort := ⟨2, false⟩
private def oldP2t : OldPort := ⟨2, true⟩
private def freshP0f : FreshPort := ⟨0, false⟩
private def freshP0t : FreshPort := ⟨0, true⟩
private def freshP1 : FreshPort := ⟨1, ()⟩
private def freshP2f : FreshPort := ⟨2, false⟩
private def freshP2t : FreshPort := ⟨2, true⟩

private def endpointEncode (i : Fin 10) : OldEnd :=
  match i.val with
  | 0 => .inl oldP0
  | 1 => .inr (.inl 0)
  | 2 => .inl oldP1f
  | 3 => .inl oldP1t
  | 4 => .inl oldP2f
  | 5 => .inr (.inr (0, false))
  | 6 => .inl oldP2t
  | 7 => .inr (.inr (0, true))
  | 8 => .inr (.inr (1, false))
  | _ => .inr (.inr (1, true))

private def endpointDecode : OldEnd → Fin 10
  | .inl ⟨⟨0, _⟩, _⟩ => 0
  | .inl ⟨⟨1, _⟩, false⟩ => 2
  | .inl ⟨⟨1, _⟩, true⟩ => 3
  | .inl ⟨⟨2, _⟩, false⟩ => 4
  | .inl ⟨⟨2, _⟩, true⟩ => 6
  | .inl ⟨⟨n + 3, h⟩, _⟩ => False.elim (by omega)
  | .inr (.inl _) => 1
  | .inr (.inr (w, d)) => if w = 0 then (if d then 7 else 5) else (if d then 9 else 8)

private def oldEndpointCode : Bij (Fin 10) OldEnd where
  toFun := endpointEncode
  invFun := endpointDecode
  left_inv i := by
    rcases tenCases i with h | h | h | h | h | h | h | h | h | h <;> subst i <;> rfl
  right_inv e := by
    cases e with
    | inl p =>
      rcases p with ⟨n, p⟩
      rcases threeCases n with h | h | h <;> subst n <;> cases p <;> rfl
    | inr e =>
      cases e with
      | inl b =>
        have h : b = 0 := by omega
        subst b
        rfl
      | inr wd =>
        rcases wd with ⟨w, d⟩
        have h : w = 0 ∨ w = 1 := by omega
        rcases h with h | h <;> subst w <;> cases d <;> rfl

private def adjacentMate (i : Fin 10) : Fin 10 :=
  match i.val with
  | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 5
  | 5 => 4 | 6 => 7 | 7 => 6 | 8 => 9 | _ => 8

private def adjacent : Pairing (Fin 10) where
  mate := adjacentMate
  involutive i := by
    rcases tenCases i with h | h | h | h | h | h | h | h | h | h <;> subst i <;> rfl
  fixedPointFree i := by
    rcases tenCases i with h | h | h | h | h | h | h | h | h | h <;> subst i <;> decide

private def oldNet : Net sig (Fin 3) (Fin 1) (Fin 2) :=
  ⟨oldLabels, adjacent.rename oldEndpointCode⟩
private def ports : Bij FreshPort OldPort :=
  Executable.carrierPorts oldLabels freshLabels nodes compatible
private def ends : Bij FreshEnd OldEnd :=
  Executable.carrierEnds oldNet freshLabels nodes vertices compatible
private def freshNet : Net sig (Fin 3) (Fin 1) (Fin 2) :=
  Executable.reindex oldNet freshLabels nodes vertices compatible

private def duplicateNames : FiniteNames (Fin 3) where
  all := [0, 1, 1, 2]
  complete n := by rcases threeCases n with h | h | h <;> subst n <;> simp
private def isOne (n : Fin 3) : Prop := n = 1
private instance decIsOne : DecidablePred isOne := fun n => inferInstanceAs (Decidable (n = 1))
private def selectedNames : FiniteNames {n : Fin 3 // isOne n} :=
  @Executable.finiteSubtype (Fin 3) duplicateNames isOne decIsOne
private def outsideNames : FiniteNames {n : Fin 3 // ¬ isOne n} :=
  @Executable.finiteSubtype (Fin 3) duplicateNames (fun n => ¬ isOne n) (fun _ => inferInstance)
private def part : Bij ({n : Fin 3 // ¬ isOne n} ⊕ {n : Fin 3 // isOne n}) (Fin 3) :=
  Executable.partitionNames isOne
private def remaining02 : FiniteNames (RemainingNodes (0 : Fin 3) 2) :=
  @Executable.remainingNodesFinite (Fin 3) duplicateNames (inferInstance : DecidableEq (Fin 3)) 0 2
private def remaining20 : FiniteNames (RemainingNodes (2 : Fin 3) 0) :=
  @Executable.remainingNodesFinite (Fin 3) duplicateNames (inferInstance : DecidableEq (Fin 3)) 2 0
private def keep02 : RemainingNodes (0 : Fin 3) 2 := ⟨1, ⟨by decide, by decide⟩⟩
private def keep20 : RemainingNodes (2 : Fin 3) 0 := ⟨1, ⟨by decide, by decide⟩⟩
private def selectedOne : {n : Fin 3 // isOne n} := ⟨1, rfl⟩
private def outsideZero : {n : Fin 3 // ¬ isOne n} := ⟨0, by decide⟩
private def outsideTwo : {n : Fin 3 // ¬ isOne n} := ⟨2, by decide⟩
private def split02 : Bij (RemainingNodes (0 : Fin 3) 2 ⊕ (Unit ⊕ Unit)) (Fin 3) :=
  Executable.splitSelectedNodes (0 : Fin 3) 2 (by decide)
private def split20 : Bij (RemainingNodes (2 : Fin 3) 0 ⊕ (Unit ⊕ Unit)) (Fin 3) :=
  Executable.splitSelectedNodes (2 : Fin 3) 0 (by decide)

/-- Concrete carrier fixture only; no encoded reachability claim. -/
theorem actual_dependent_ports_and_reindex :
  (ports freshP0f = oldP2f) ∧
  (ports freshP1 = oldP0) ∧
  (ports freshP2t = oldP1t) ∧
  (ports.invFun oldP0 = freshP1) ∧
  (ports.invFun oldP1f = freshP2f) ∧
  (ports.invFun oldP2t = freshP0t) ∧
  (ends (.inr (.inl (0 : Fin 1))) = .inr (.inl (0 : Fin 1))) ∧
  (ends (.inr (.inr ((0 : Fin 2), false))) = .inr (.inr ((1 : Fin 2), false))) ∧
  (ends.invFun (.inr (.inr ((0 : Fin 2), true))) = .inr (.inr ((1 : Fin 2), true))) ∧
  (freshNet.wire (.inr (.inl (0 : Fin 1))) = .inl freshP1) ∧
  (freshNet.wire (.inl freshP1) = .inr (.inl (0 : Fin 1))) ∧
  (freshNet.wire (.inl freshP0f) = .inr (.inr ((1 : Fin 2), false))) ∧
  (freshNet.wire (.inr (.inr ((1 : Fin 2), true))) = .inl freshP0t) ∧
  (freshNet.wire (.inl freshP2f) = .inl freshP2t) ∧
  (freshNet.wire (.inr (.inr ((0 : Fin 2), false))) = .inr (.inr ((0 : Fin 2), true))) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Concrete carrier fixture only; no encoded reachability claim. -/
theorem actual_duplicate_partition_and_swap :
  (selectedNames.all.map Subtype.val = [(1 : Fin 3), 1]) ∧
  (outsideNames.all.map Subtype.val = [(0 : Fin 3), 2]) ∧
  (remaining02.all.map Subtype.val = [(1 : Fin 3), 1]) ∧
  (remaining20.all.map Subtype.val = [(1 : Fin 3), 1]) ∧
  (part.invFun (1 : Fin 3) = .inr selectedOne) ∧
  (part.invFun (0 : Fin 3) = .inl outsideZero) ∧
  (part.invFun (2 : Fin 3) = .inl outsideTwo) ∧
  (part (.inr selectedOne) = (1 : Fin 3)) ∧
  (split02 (.inr (.inl ())) = (0 : Fin 3)) ∧
  (split02 (.inr (.inr ())) = (2 : Fin 3)) ∧
  (split02.invFun (0 : Fin 3) = .inr (.inl ())) ∧
  (split02.invFun (2 : Fin 3) = .inr (.inr ())) ∧
  (split02.invFun (1 : Fin 3) = .inl keep02) ∧
  (split20 (.inr (.inl ())) = (2 : Fin 3)) ∧
  (split20 (.inr (.inr ())) = (0 : Fin 3)) ∧
  (split20.invFun (0 : Fin 3) = .inr (.inr ())) ∧
  (split20.invFun (2 : Fin 3) = .inr (.inl ())) ∧
  (split20.invFun (1 : Fin 3) = .inl keep20) ∧
  (split20 (.inl keep20) = (1 : Fin 3)) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Lamping.Checks.ExecutableCarrierFoundations
