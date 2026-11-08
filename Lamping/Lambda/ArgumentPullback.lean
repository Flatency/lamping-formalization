import Lamping.Lambda.ContextualHistories
import Lamping.Lambda.ArgumentCopies
namespace Lamping.Lambda
 theorem BetaAt.contract_lookup (R : BetaAt t p u)
     (hr : subtermAt t p = some (.app (.lam b) a)) :
     subtermAt u p = some (contract b a) := by
   obtain ⟨w, hw, hloc⟩ := replaceAt_lookup hr (contract b a)
   have hb : BetaAt t p w := ⟨b, a, hr, hw⟩
   rw [hb.unique R] at hloc
   exact hloc

 theorem ArgumentLift.copy_internal {R : BetaAt t p u} (lift : ArgumentLift R σ σ') :
     Internal (p ++ lift.occurrence) σ := by
   intro q hq
   rw [lift.copy_paths] at hq
   obtain ⟨r, _, he⟩ := List.mem_map.mp hq
   exact ⟨r, he.symm⟩

 theorem ArgumentLift.original_internal {R : BetaAt t p u} (lift : ArgumentLift R σ σ') :
     Internal (p ++ [.arg]) σ' := by
   intro q hq
   rw [lift.original_paths] at hq
   obtain ⟨r, _, he⟩ := List.mem_map.mp hq
   exact ⟨r, he.symm⟩

/-- Pull an arbitrary actual internal reduction back from the specified i-th
 argument instance to the original argument. The shifted copy is reflected
 through beta, then the resulting history is lifted into the original term.
 Its full parallelization is constructed by the real tile grid. -/
 theorem argument_lift_exists (R : BetaAt t p u)
     (hr : subtermAt t p = some (.app (.lam b) a))
     (ho : ArgumentOccurrence b occurrence)
     (σ : ParallelHistory u v) (hi : Internal (p ++ occurrence) σ) :
     ∃ (w : Term) (σ' : ParallelHistory t w), Atomic σ' ∧
       ∃ lift : ArgumentLift R σ σ', lift.occurrence = occurrence := by
   have hcopy : subtermAt u (p ++ occurrence) =
       some (rename (fun i => i + binderDepth occurrence) a) := by
     rw [subtermAt_append, R.contract_lookup hr, Option.bind_some]
     exact argument_copy ho a
   obtain ⟨qs, finalCopy, hpaths, hlocal, _⟩ := hi.extract hcopy
   obtain ⟨originalFinal, horiginal, _⟩ := hlocal.rename_reflect
   have harg : subtermAt t (p ++ [.arg]) = some a := by
     rw [subtermAt_append, hr]
     cases a <;> rfl
   obtain ⟨w, hglobal, _⟩ := horiginal.prefix_lift harg
   obtain ⟨σ', hatomic, hσpaths⟩ := hglobal.atomic
   have hprojection : ∃ (z : Term) (F : List Path) (full : ParallelHistory u z)
       (last : ParallelStep F w z), StepProjection (singleContraction R) σ' full last :=
     StepProjection.exists_projection (singleContraction R) σ'
   let lift : ArgumentLift R σ σ' :=
     { body := b
       argument := a
       redex := hr
       occurrence := occurrence
       isVariable := ho
       localPaths := qs
       copy_paths := hpaths
       original_paths := hσpaths
       parallelization := hprojection }
   exact ⟨w, σ', hatomic, lift, rfl⟩
end Lamping.Lambda

