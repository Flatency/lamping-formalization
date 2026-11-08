import Lamping.Lambda.ResidualComposition
import Lamping.Lambda.Families
namespace Lamping.Lambda
namespace ParallelStep
 def empty (t : Term) : ParallelStep [] t t := by
   have hn : Marked.Normal (Marked.mark [] t) := by
     rw [Marked.normal_iff_no_step]
     rintro ⟨u, hu⟩
     obtain ⟨p, hp⟩ := hu.at
     have hh := hp.active
     rw [Marked.active_mark] at hh
     exact List.not_mem_nil hh.1
   exact ⟨[], Marked.mark [] t,
     (Marked.completeOld_iff [] t).mpr ⟨.nil _, hn⟩, Marked.erase_mark [] t⟩
end ParallelStep
namespace ParallelHistory
 @[simp] theorem single_derivation (h : ParallelStep F t u) :
     (single h).derivation = h.derivation := Derivation.append_nil _
end ParallelHistory

/-- Every generating permutation and every composition context preserve the
 residuals of all original redexes. Thus PermEq is not endpoint equality. -/
 theorem PermEq.residual {h k : ParallelHistory t u} (hp : PermEq h k) (r : RedexOcc t) (s : RedexOcc u) :
     h.derivation.Residual r s ↔ k.derivation.Residual r s := by
   induction hp with
   | refl => exact Iff.rfl
   | symm _ ih => exact (ih r s).symm
   | trans _ _ ih ik => exact (ih r s).trans (ik r s)
   | comp hh hk ih ik =>
     rw [ParallelHistory.derivation_append, ParallelHistory.derivation_append,
       Derivation.residual_append, Derivation.residual_append]
     constructor
     · rintro ⟨q, hq, hqs⟩; exact ⟨q, (ih r q).mp hq, (ik q s).mp hqs⟩
     · rintro ⟨q, hq, hqs⟩; exact ⟨q, (ih r q).mpr hq, (ik q s).mpr hqs⟩
   | development h k =>
     simpa only [ParallelHistory.single_derivation] using h.residual_independent k r s
   | moves sq =>
     simpa only [ParallelHistory.derivation_append, ParallelHistory.single_derivation] using sq.residual r s
   | empty h =>
     have he := h.residual_independent (ParallelStep.empty _) r s
     simpa only [ParallelHistory.single_derivation, ParallelStep.empty, ParallelStep.derivation,
       ParallelHistory.derivation, Derivation.nil] using he

 theorem Copy.trans {a b c : RedexWithHistory m} (h : Copy a b) (k : Copy b c) : Copy a c := by
   obtain ⟨τ, hperm, hres⟩ := h
   obtain ⟨υ, kperm, kres⟩ := k
   refine ⟨τ.append υ, ?_, ?_⟩
   · rw [← ParallelHistory.append_assoc]
     exact .trans (hperm.append υ) kperm
   · rw [ParallelHistory.derivation_append, Derivation.residual_append]
     exact ⟨b.redex, hres, kres⟩
end Lamping.Lambda

