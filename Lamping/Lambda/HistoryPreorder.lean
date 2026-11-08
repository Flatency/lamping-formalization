import Lamping.Lambda.HistoryCancellation
namespace Lamping.Lambda

/-- An actual extension modulo generated permutation, with the same initial
term. This is the source history prefix preorder. -/
def HistoryPrefix (ρ : ParallelHistory m t) (σ : ParallelHistory m u) : Prop :=
  ∃ tail : ParallelHistory t u, PermEq (ρ.append tail) σ

namespace HistoryPrefix
theorem refl (ρ : ParallelHistory m t) : HistoryPrefix ρ ρ :=
  ⟨.nil _,by rw [ParallelHistory.append_nil]; exact .refl _⟩

theorem trans {ρ : ParallelHistory m t} {σ : ParallelHistory m u} {τ : ParallelHistory m v}
    (left : HistoryPrefix ρ σ) (right : HistoryPrefix σ τ) : HistoryPrefix ρ τ := by
  obtain ⟨first,hfirst⟩ := left
  obtain ⟨second,hsecond⟩ := right
  refine ⟨first.append second,?_⟩
  rw [←ParallelHistory.append_assoc]
  exact (hfirst.append second).trans hsecond

/-- AG5.1.12: a genuine Copy across two nested history prefixes factors
through an actual intermediate redex. General left cancellation is proved
separately, and the old redex is obtained from residual composition. -/
theorem copy_interpolation
    {ρ : ParallelHistory m t} {σ : ParallelHistory m u} {τ : ParallelHistory m v}
    (first : HistoryPrefix ρ σ) (second : HistoryPrefix σ τ)
    (r : RedexOcc t) (s : RedexOcc v)
    (copy : Copy ⟨t,ρ,r⟩ ⟨v,τ,s⟩) :
    ∃ q : RedexOcc u, Copy ⟨t,ρ,r⟩ ⟨u,σ,q⟩ ∧ Copy ⟨u,σ,q⟩ ⟨v,τ,s⟩ := by
  obtain ⟨a,ha⟩ := first
  obtain ⟨b,hb⟩ := second
  obtain ⟨extension,hext,residual⟩ := copy
  have composed : PermEq (ρ.append (a.append b)) τ := by
    rw [←ParallelHistory.append_assoc]
    exact (ha.append b).trans hb
  have equal : PermEq extension (a.append b) := (hext.trans composed.symm).cancel_prefix ρ
  have transported := (equal.residual r s).mp residual
  rw [ParallelHistory.derivation_append,Derivation.residual_append] at transported
  obtain ⟨q,left,right⟩ := transported
  exact ⟨q,⟨a,ha,left⟩,⟨b,hb,right⟩⟩
end HistoryPrefix
end Lamping.Lambda
