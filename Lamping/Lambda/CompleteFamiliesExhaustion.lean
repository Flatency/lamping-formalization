import Lamping.Lambda.CanonicalFamilyEvents
import Lamping.Lambda.CompleteFamilies
namespace Lamping.Lambda

/-- A complete-family derivation never encounters any previously used family
again, even after an arbitrary actual extension. No completion is constructed. -/
theorem CompleteDerivation.no_future_family {ρ : ParallelHistory m t}
    (complete : CompleteDerivation ρ) (tail : ParallelHistory t u) (s : RedexOcc u) :
    ¬FamilyUsed ρ ⟨u,ρ.append tail,s⟩ := by
  induction complete generalizing u with
  | nil => intro impossible; cases impossible
  | @step v t ρ F h previous whole ih =>
    intro used
    let future : RedexWithHistory m := ⟨u,(ρ.append (.single h)).append tail,s⟩
    change FamilyUsedAt (.nil m) (ρ.append (.single h)) future at used
    rcases (FamilyUsedAt.append_iff (.nil m) ρ (.single h) future).mp used with old | fresh
    · apply ih ((ParallelHistory.single h).append tail) s
      simpa only [future,FamilyUsed,ParallelHistory.append_assoc] using old
    · change FamilyUsedAt ρ (.single h) future at fresh
      cases fresh with
      | @head _ _ _ _ _ _ _ _ r selected family =>
        have development : DevelopsFamilies ρ (FamilyUsed ρ) := by
          refine ⟨fun _ event => event,?_⟩
          intro q event
          apply ih (.nil _) q
          simpa only [ParallelHistory.append_nil] using event
        let current : RedexWithHistory m := ⟨t,ρ,r⟩
        obtain ⟨run,a,canonical,represented,related⟩ := current.canonical_exists
        have same : FamilyEq a current := related.symm
        have order : HistoryPrefix a.history ρ :=
          (canonical_prefix_relative canonical represented same).prefix_development development
        have extensionOrder : HistoryPrefix ρ future.history := by
          refine ⟨(ParallelHistory.single h).append tail,?_⟩
          simp only [future,ParallelHistory.append_assoc]
          exact .refl _
        have toFuture : Copy a future :=
          (canonical_copy_iff_history_prefix canonical represented (same.trans family)).mpr
            (order.trans extensionOrder)
        obtain ⟨q,toMiddle,toEnd⟩ := order.copy_interpolation extensionOrder a.redex s toFuture
        have toCurrent : Copy a current :=
          (canonical_copy_iff_history_prefix canonical represented same).mpr order
        have qSelected : q.val∈F := whole.maximal r q selected
          ((FamilyEq.copy toCurrent).symm.trans (.copy toMiddle))
        obtain ⟨extension,perm,residual⟩ := toEnd
        have perm' : PermEq extension ((ParallelHistory.single h).append tail) := by
          apply PermEq.cancel_prefix ρ
          simpa only [future,ParallelHistory.append_assoc] using perm
        have transported := (perm'.residual q s).mp residual
        rw [ParallelHistory.derivation_append,Derivation.residual_append] at transported
        obtain ⟨middle,first,_⟩ := transported
        exact h.no_selected_residual q qSelected middle (by simpa only [ParallelHistory.single_derivation] using first)
      | tail impossible => cases impossible

/-- AG5.4.7: every given complete-family derivation is a development of
its actual used families. This does not assert existence for arbitrary X. -/
theorem CompleteDerivation.develops_used {ρ : ParallelHistory m t}
    (complete : CompleteDerivation ρ) : DevelopsFamilies ρ (FamilyUsed ρ) := by
  refine ⟨fun _ event => event,?_⟩
  intro r event
  apply complete.no_future_family (.nil _) r
  simpa only [ParallelHistory.append_nil] using event

end Lamping.Lambda
