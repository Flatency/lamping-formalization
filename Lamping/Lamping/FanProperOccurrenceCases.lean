import Lamping.Lamping.ActionSyntaxObservationKinds
namespace Lamping.AG
open Graph
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}

/-- The actual Bool copy is retained. An APP access can end only at context. -/
theorem PathSite.fan_app_access_cases
    (site : PathSite (Schema.fanAction Op.app i j lt) kept (B:=B) (W:=W) (V:=V))
    {root : B} (path : RootAccess site.reduce root) :
    (∃port : NodePort signature K kept,
      path.val.getLast?=some (site.reduce.wire (.inl ⟨.inl port.1,port.2⟩))) ∨
    ∃copy : Bool,path.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl copy),appCtx⟩)) := by
  rcases site.action_access_node_cases (IsAction.fan .app i j lt) path with kept |⟨node,port,passive,finish⟩
  · exact Or.inl kept
  · cases passive with
    | fan copy =>
      obtain ⟨kind,typed⟩ := path.property.2.2
      have actual := accessKind_at_actual_finish typed (.inr (.inl copy)) port finish
      cases port with
      | inl u => cases u;change none=some kind at actual;cases actual
      | inr side =>
        cases side
        · exact Or.inr ⟨copy,finish⟩
        · change none=some kind at actual;cases actual

/-- Lambda context and binding are distinct possible terminal roles. No
parent context assertion is inferred merely from this typed access. -/
theorem PathSite.fan_lam_access_cases
    (site : PathSite (Schema.fanAction Op.lam i j lt) kept (B:=B) (W:=W) (V:=V))
    {root : B} (path : RootAccess site.reduce root) :
    (∃port : NodePort signature K kept,
      path.val.getLast?=some (site.reduce.wire (.inl ⟨.inl port.1,port.2⟩))) ∨
    ∃copy : Bool,
      path.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl copy),.inl ()⟩)) ∨
      path.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl copy),lamBind⟩)) := by
  rcases site.action_access_node_cases (IsAction.fan .lam i j lt) path with kept |⟨node,port,passive,finish⟩
  · exact Or.inl kept
  · cases passive with
    | fan copy =>
      obtain ⟨kind,typed⟩ := path.property.2.2
      have actual := accessKind_at_actual_finish typed (.inr (.inl copy)) port finish
      cases port with
      | inl u => cases u;exact Or.inr ⟨copy,Or.inl finish⟩
      | inr side =>
        cases side
        · exact Or.inr ⟨copy,Or.inr finish⟩
        · change none=some kind at actual;cases actual
end
#print axioms PathSite.fan_app_access_cases
#print axioms PathSite.fan_lam_access_cases
end Lamping.AG
