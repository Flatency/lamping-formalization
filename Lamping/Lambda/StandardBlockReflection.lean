import Lamping.Lambda.StandardAppBlocks
import Lamping.Lambda.ArgumentStandardness
import Lamping.Lambda.AtomicScheduleSplit
namespace Lamping.Lambda

/-- Reconstruct intermediate selection geometry from the actual ordinary
program. No residual or standardness conclusion is supplied. -/
theorem Atomic.right_of_paths {ρ : ParallelHistory t u} (ordinary : Atomic ρ)
    (paths : ∀ p∈ρ.derivation.paths,LeftOf cut p) : RightHistory cut ρ := by
  induction ordinary with
  | nil t => exact .nil t
  | @cons t p v u tail head atomic ih =>
    refine .cons _ _ ?_ (ih ?_)
    · intro r selected
      have same : r.val=p := List.mem_singleton.mp selected
      rw [same]
      exact paths p (by simp [ParallelHistory.derivation,Derivation.append,ParallelStep.derivation,singleContraction])
    · intro q hq
      exact paths q (by simp [ParallelHistory.derivation,Derivation.append,hq])

/-- Reflect a genuine contextual phase into a standard ordinary local
history, retaining the complete program and target lookup. -/
theorem Atomic.standard_internal_reflect {ρ : ParallelHistory t u}
    (ordinary : Atomic ρ) (standard : Standard ρ) (inside : Internal site ρ)
    (lookup : subtermAt t site=some a) :
    ∃ b, ∃ programHistory : ParallelHistory a b, Atomic programHistory ∧ Standard programHistory ∧
      ρ.derivation.paths=programHistory.derivation.paths.map (fun p => site++p) ∧
      subtermAt u site=some b := by
  obtain ⟨ps,b,paths,history,last⟩ := inside.extract lookup
  obtain ⟨programHistory,atomic,program⟩ := history.atomic
  have localStandard : Standard programHistory := atomic.region_rename_standard_reflect ordinary
    (a:=a) (pre:=[]) (pre':=site) (ren:=id) (by simp [subtermAt]) (by simpa only [rename_id] using lookup)
    ps (by simpa using program) paths standard
  exact ⟨b,programHistory,atomic,localStandard,by rw [program]; exact paths,last⟩

theorem Atomic.standard_internal_right_reflect {ρ : ParallelHistory t u}
    (ordinary : Atomic ρ) (standard : Standard ρ) (inside : Internal site ρ)
    (lookup : subtermAt t site=some a) (right : RightHistory (site++cut) ρ) :
    ∃ b, ∃ programHistory : ParallelHistory a b,
      Atomic programHistory ∧ Standard programHistory ∧ RightHistory cut programHistory ∧
      ρ.derivation.paths=programHistory.derivation.paths.map (fun p => site++p) ∧
      subtermAt u site=some b := by
  obtain ⟨b,history,atomic,standard,paths,last⟩ := ordinary.standard_internal_reflect standard inside lookup
  refine ⟨b,history,atomic,standard,atomic.right_of_paths ?_,paths,last⟩
  intro p hp
  have member : site++p∈ρ.derivation.paths := by rw [paths]; exact List.mem_map.mpr ⟨p,hp,rfl⟩
  exact (right.paths_right _ member).strip_prefix

end Lamping.Lambda



