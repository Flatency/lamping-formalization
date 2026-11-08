import Lamping.Lambda.CopyHeadOrder
namespace Lamping.Lambda
/-- The original ancestor of a final redex strictly before a protected cut
is recovered from actual creation locality, and remains at the same path. -/
theorem RightHistory.left_pointed_ancestor {a : RedexWithHistory m}
    (right : RightHistory cut a.history) (before : LeftOf a.redex.val cut) :
    ∃ initial : RedexOcc m, initial.val=a.redex.val ∧ a.history.derivation.Residual initial a.redex := by
  have original := a.history.derivation.valid.reflect_left right.paths_right before a.redex.property
  let initial : RedexOcc m := ⟨a.redex.val,original⟩
  have paths : ∀ p∈a.history.derivation.paths, LeftOf initial.val p := by
    intro p hp; exact before.trans (right.paths_right p hp)
  exact ⟨initial,rfl,(a.history.derivation.left_fixed initial paths a.redex).mpr rfl⟩

/-- AG5.2.9's external/left final-point case has an actual common singleton
extraction successor, without using confluence or an abstract join premise. -/
theorem Copy.common_of_left_pointed {a b : RedexWithHistory m} (copy : Copy a b)
    (right : RightHistory cut a.history) (before : LeftOf a.redex.val cut)
    (source : RunRepresents r a) (target : RunRepresents s b) : ExtractionJoin r s := by
  obtain ⟨initial,_,residual⟩ := right.left_pointed_ancestor before
  let initialCopy : Copy ⟨m,.nil m,initial⟩ a := ⟨a.history,.refl _,residual⟩
  obtain ⟨w,step⟩ := initial.contract_exists
  exact ⟨.of (.single (singleContraction step)) (.single step),
    initialCopy.initial_extraction initial a source step,
    (initialCopy.trans copy).initial_extraction initial b target step⟩

/-- The source pointed redex cannot equal a protected target-head residual:
the target has already consumed that initial old name. -/
theorem Copy.ne_protected_target_head {a b : RedexWithHistory m} (copy : Copy a b)
    (S : BetaAt m q u) (tail : ParallelHistory u b.target)
    (target : b.history=.cons (singleContraction S) tail)
    (right : RightHistory q a.history) : a.redex.val≠q := by
  intro same
  let initial : RedexOcc m := ⟨q,S.redex⟩
  have alive := (a.history.derivation.left_fixed initial right.paths_right a.redex).mpr same
  have targetAlive := (copy.initial_residual initial).mp alive
  exact (Copy.refl b).source_head_deleted S tail target b.redex targetAlive
end Lamping.Lambda
