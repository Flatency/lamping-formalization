import Lamping.Lamping.FlowBalance
namespace Lamping.AG
open Graph

def wires_flow {A B : Type} [FiniteNames A] [FiniteNames B] (route : Bij A B)
    (boundary : A⊕B → Bool) (opposite : ∀ a, boundary (.inr (route a)) = !boundary (.inl a)) :
    FlowBalance (wires A B route) boundary where
  nodes := Empty.elim
  vertices := Empty.elim
  wiring := by
    rintro (⟨node,p⟩ | ((a|b) | ⟨w,d⟩))
    · exact nomatch node
    · exact opposite a
    · have eq := opposite (route.invFun b)
      rw [route.right_inv] at eq
      change boundary (.inl (route.invFun b)) = !boundary (.inr b)
      rw [eq]; simp
    · exact nomatch w

def fanRight_flow (f : Op) (i j : Nat) (active passive : Bool) (boundary : Bool⊕Aux f → Bool)
    (left : ∀ b, boundary (.inl b) = active)
    (right : ∀ a, boundary (.inr a) = !(flowPort (.op f) passive (.inr a)))
    (principal : flowPort (.op f) passive (.inl ()) = !active) :
    FlowBalance (fanRight f i j) boundary where
  nodes := Sum.elim (fun _ => passive) (fun a => flowPort (.op f) passive (.inr a))
  vertices := Empty.elim
  wiring := by
    rintro (⟨b|a,p⟩ | ((b|a) | ⟨w,d⟩))
    · cases p with
      | inl u => cases u; change boundary (.inl b) = !(flowPort (.op f) passive (.inl ())); rw [principal,left]; simp
      | inr a => rfl
    · cases p with
      | inl u => cases u; exact right a
      | inr b =>
        change flowPort (.op f) passive (.inr a) = !(!(flowPort (.op f) passive (.inr a)))
        simp
    · change flowPort (.op f) passive (.inl ()) = !boundary (.inl b)
      rw [left,principal]
    · change flowPort (.op f) passive (.inr a) = !boundary (.inr a)
      rw [right]; simp
    · exact nomatch w

def unaryRight_flow (c : Unary) (f : Op) (i j : Nat)
    (active passive : Bool) (boundary : Unit⊕Aux f → Bool)
    (left : boundary (.inl ()) = active)
    (right : ∀ a, boundary (.inr a) = !(flowPort (.op f) passive (.inr a)))
    (principal : flowPort (.op f) passive (.inl ()) = !active) :
    FlowBalance (unaryRight c f i j) boundary where
  nodes := Sum.elim (fun _ => passive) (fun a => flowPort (.op f) passive (.inr a))
  vertices := Empty.elim
  wiring := by
    cases c <;> rintro (⟨u|a,p⟩ | ((u|a) | ⟨w,d⟩))
    all_goals first
    | exact nomatch w
    | (cases u; cases p with
      | inl u => cases u; change boundary (.inl ()) = !(flowPort (.op f) passive (.inl ())); rw [left,principal]; simp
      | inr a => rfl)
    | (cases p with
      | inl u => cases u; exact right a
      | inr u =>
        change flowPort (.op f) passive (.inr a) = !(!(flowPort (.op f) passive (.inr a)))
        simp)
    | (cases u; change flowPort (.op f) passive (.inl ()) = !boundary (.inl ()); rw [left,principal])
    | (change flowPort (.op f) passive (.inr a) = !boundary (.inr a); rw [right]; simp)

theorem FlowBalance.active_flow {s : Schema} {boundary : s.Frontier → Bool}
    (old : FlowBalance s.left boundary) (a : Aux s.active) :
    boundary (.inl a) = !(flowPort (.op s.active) (old.nodes (.inl ())) (.inr a)) := by
  have eq := old.wiring (.inr (.inl (.inl a)))
  change flowPort (.op s.active) (old.nodes (.inl ())) (.inr a) = !boundary (.inl a) at eq
  rw [eq]; simp

theorem FlowBalance.passive_flow {s : Schema} {boundary : s.Frontier → Bool}
    (old : FlowBalance s.left boundary) (a : Aux s.passive) :
    boundary (.inr a) = !(flowPort (.op s.passive) (old.nodes (.inr ())) (.inr a)) := by
  have eq := old.wiring (.inr (.inl (.inr a)))
  change flowPort (.op s.passive) (old.nodes (.inr ())) (.inr a) = !boundary (.inr a) at eq
  rw [eq]; simp

theorem FlowBalance.principal_flow {s : Schema} {boundary : s.Frontier → Bool}
    (old : FlowBalance s.left boundary) :
    flowPort (.op s.passive) (old.nodes (.inr ())) (.inl ()) =
      !(flowPort (.op s.active) (old.nodes (.inl ())) (.inl ())) :=
  old.wiring (.inl ⟨.inl (),.inl ()⟩)

/-- All seven local rewrites preserve every frontier polarity, with explicitly
constructed node bases. The control index does not enter the polarity. -/
theorem Schema.flow_preservation (s : Schema) (boundary : s.Frontier → Bool)
    (old : FlowBalance s.left boundary) : Nonempty (FlowBalance s.right.net boundary) := by
  cases s with
  | beta i =>
    refine ⟨wires_flow boolFlip boundary ?_⟩
    intro a
    cases a
    all_goals rw [old.active_flow,old.passive_flow]
    all_goals rfl
  | fanCancel i =>
    have principal : old.nodes (.inr ()) = !(old.nodes (.inl ())) := old.principal_flow
    refine ⟨wires_flow (Bij.refl Bool) boundary ?_⟩
    intro a
    change boundary (.inr a) = !boundary (.inl a)
    rw [old.active_flow,old.passive_flow]
    change (!(!(old.nodes (.inr ())))) = !(!(!(old.nodes (.inl ()))))
    rw [principal]
  | croCancel i =>
    have principal : old.nodes (.inr ()) = !(old.nodes (.inl ())) := old.principal_flow
    refine ⟨wires_flow (Bij.refl Unit) boundary ?_⟩
    intro a
    change boundary (.inr a) = !boundary (.inl a)
    rw [old.active_flow,old.passive_flow]
    change (!(!(old.nodes (.inr ())))) = !(!(!(old.nodes (.inl ()))))
    rw [principal]
  | braCancel i =>
    have principal : old.nodes (.inr ()) = !(old.nodes (.inl ())) := old.principal_flow
    refine ⟨wires_flow (Bij.refl Unit) boundary ?_⟩
    intro a
    change boundary (.inr a) = !boundary (.inl a)
    rw [old.active_flow,old.passive_flow]
    change (!(!(old.nodes (.inr ())))) = !(!(!(old.nodes (.inl ()))))
    rw [principal]
  | fanAction f i j less =>
    exact ⟨fanRight_flow f i j (old.nodes (.inl ())) (old.nodes (.inr ())) boundary
      (by intro b; simpa [Schema.active,flowPort] using old.active_flow b)
      old.passive_flow old.principal_flow⟩
  | croAction f i j less =>
    exact ⟨unaryRight_flow .cro f i j (old.nodes (.inl ())) (old.nodes (.inr ())) boundary
      (by simpa [Schema.active,flowPort] using old.active_flow ()) old.passive_flow old.principal_flow⟩
  | braAction f i j less =>
    exact ⟨unaryRight_flow .bra f i j (old.nodes (.inl ())) (old.nodes (.inr ())) boundary
      (by simpa [Schema.active,flowPort] using old.active_flow ()) old.passive_flow old.principal_flow⟩
end Lamping.AG
