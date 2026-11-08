import Lamping.Lamping.SchemaBalanceFactories
namespace Lamping.AG
open Graph

theorem LevelBalance.active_auxiliary {s : Schema} {boundary : s.Frontier → Int}
    (balance : LevelBalance s.left boundary) (a : Aux s.active) :
    boundary (.inl a)=portDepth s.low (.op s.active) (balance.nodes (.inl ())) (.inr a) :=
  (balance.wiring (.inr (.inl (.inl a)))).symm

theorem LevelBalance.passive_auxiliary {s : Schema} {boundary : s.Frontier → Int}
    (balance : LevelBalance s.left boundary) (a : Aux s.passive) :
    boundary (.inr a)=portDepth s.high (.op s.passive) (balance.nodes (.inr ())) (.inr a) :=
  (balance.wiring (.inr (.inl (.inr a)))).symm

theorem LevelBalance.principal_pair {s : Schema} {boundary : s.Frontier → Int}
    (balance : LevelBalance s.left boundary) :
    portDepth s.high (.op s.passive) (balance.nodes (.inr ())) (.inl ())=
      portDepth s.low (.op s.active) (balance.nodes (.inl ())) (.inl ()) :=
  balance.wiring (.inl ⟨.inl (),.inl ()⟩)

/-- Every actual schema preserves the potential on every ordered frontier
occurrence. The RHS node/control potentials are constructed explicitly. -/
theorem Schema.balance_preservation (s : Schema) (boundary : s.Frontier → Int)
    (old : LevelBalance s.left boundary) : Nonempty (LevelBalance s.right.net boundary) := by
  cases s with
  | beta i =>
    refine ⟨wires_balance boolFlip boundary ?_⟩
    intro a
    cases a with
    | false => exact (old.active_auxiliary false).trans (old.passive_auxiliary true).symm
    | true => exact (old.active_auxiliary true).trans (old.passive_auxiliary false).symm
  | fanCancel i =>
    have principal : old.nodes (.inr ())=old.nodes (.inl ()) := old.principal_pair
    refine ⟨wires_balance (Bij.refl Bool) boundary ?_⟩
    intro a
    exact (old.active_auxiliary a).trans (principal.symm.trans (old.passive_auxiliary a).symm)
  | croCancel i =>
    have principal : old.nodes (.inr ())+1=old.nodes (.inl ())+1 := old.principal_pair
    have equal : old.nodes (.inl ())=old.nodes (.inr ()) := by omega
    refine ⟨wires_balance (Bij.refl Unit) boundary ?_⟩
    intro a
    exact (old.active_auxiliary a).trans (equal.trans (old.passive_auxiliary a).symm)
  | braCancel i =>
    have principal : old.nodes (.inr ())=old.nodes (.inl ()) := old.principal_pair
    refine ⟨wires_balance (Bij.refl Unit) boundary ?_⟩
    intro a
    have equal : old.nodes (.inl ())+1=old.nodes (.inr ())+1 := by omega
    exact (old.active_auxiliary a).trans (equal.trans (old.passive_auxiliary a).symm)
  | fanAction f i j less =>
    exact ⟨fanRight_balance f i j (old.nodes (.inl ())) (old.nodes (.inr ())) boundary
      old.active_auxiliary old.passive_auxiliary old.principal_pair⟩
  | croAction f i j less =>
    exact ⟨croRight_balance f i j (by omega) (old.nodes (.inl ())) (old.nodes (.inr ())) boundary
      (old.active_auxiliary ()) old.passive_auxiliary old.principal_pair⟩
  | braAction f i j less =>
    exact ⟨braRight_balance f i j (old.nodes (.inl ())) (old.nodes (.inr ())) boundary
      (old.active_auxiliary ()) old.passive_auxiliary old.principal_pair⟩
end Lamping.AG
