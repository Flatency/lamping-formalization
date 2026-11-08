import Lamping.Lambda.CopyRegionProjection
import Lamping.Lambda.ContextualHistories
namespace Lamping.Lambda

/-- Construct the specified actual ordinary argument copy from the given
original argument program. The copy endpoint and its exact program are
derived by local reflection, binder lifting and contextual beta lifting. -/
theorem Atomic.argument_forward_mirror {original : ParallelHistory t v} (_ordinary : Atomic original)
    (R : BetaAt t p u) (lookup : subtermAt t p=some (.app (.lam b) a))
    (inside : Internal (p++[.arg]) original) (occurs : ArgumentOccurrence b occ) :
    ∃ w, ∃ copy : ParallelHistory u w, Atomic copy ∧
      ∃ lift : ArgumentLift R copy original, lift.occurrence=occ := by
  have argumentLookup : subtermAt t (p++[.arg])=some a := by
    rw [subtermAt_append,lookup]
    simp [subtermAt]
  obtain ⟨ps,argumentTarget,paths,localHistory,_⟩ := inside.extract argumentLookup
  have targetLookup : subtermAt u (p++occ)=some (rename (fun i => i+binderDepth occ) a) := by
    rw [subtermAt_append,R.contract_lookup lookup,Option.bind_some]
    exact argument_copy occurs a
  obtain ⟨w,copyHistory,_⟩ := (localHistory.rename (fun i => i+binderDepth occ)).prefix_lift targetLookup
  obtain ⟨copy,copyAtomic,copyPaths⟩ := copyHistory.atomic
  refine ⟨w,copy,copyAtomic,{
    body := b
    argument := a
    redex := lookup
    occurrence := occ
    isVariable := occurs
    localPaths := ps
    copy_paths := copyPaths
    original_paths := paths
    parallelization := StepProjection.exists_projection (singleContraction R) original },rfl⟩

end Lamping.Lambda

