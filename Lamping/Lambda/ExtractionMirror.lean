import Lamping.Lambda.ExtractionRename
import Lamping.Lambda.ExtractionContextReflect
namespace Lamping.Lambda

def ExtractionRun.castSource (eq : t=u) (r : ExtractionRun t) : ExtractionRun u := eq ▸ r

@[simp] theorem ExtractionRun.castSource_paths (eq : t=u) (r : ExtractionRun t) :
    (r.castSource eq).history.derivation.paths=r.history.derivation.paths := by cases eq; rfl

@[simp] theorem ExtractionRun.rename_paths (r : ExtractionRun t) (ρ : Nat → Nat) :
    (r.rename ρ).history.derivation.paths=r.history.derivation.paths :=
  r.history.rename_derivation_paths ρ

theorem ExtractionStep.castSource (eq : t=u) {r s : ExtractionRun t}
    (h : ExtractionStep r s) : ExtractionStep (r.castSource eq) (s.castSource eq) := by
  cases eq
  exact h

theorem rename_left_inverse (left : ∀i,ν (ρ i)=i) (t : Term) :
    rename ν (rename ρ t)=t := by
  rw [rename_comp]
  have eq : ν ∘ ρ = id := funext left
  rw [eq,rename_id]

/-- Injective variable renaming reflects actual extraction generators.
 The inverse acts on actual histories; their target terms are reconstructed
 by beta determinism, rather than supplied as corresponding endpoints. -/
theorem ExtractionStep.rename_reflect {ρ ν : Nat → Nat} (left : ∀i,ν (ρ i)=i)
    {r : ExtractionRun t} {s : ExtractionRun (Lambda.rename ρ t)}
    (step : ExtractionStep (r.rename ρ) s) :
    ∃q,ExtractionStep r q ∧ s=q.rename ρ := by
  have source := rename_left_inverse left t
  let q := (s.rename ν).castSource source
  have unshifted : ExtractionStep (((r.rename ρ).rename ν).castSource source) q := by
    exact (step.rename ν).castSource source
  have original : ((r.rename ρ).rename ν).castSource source=r := by
    apply ExtractionRun.ext_paths
    simp only [ExtractionRun.castSource_paths,ExtractionRun.rename_paths]
  rw [original] at unshifted
  refine ⟨q,unshifted,?_⟩
  apply ExtractionRun.ext_paths
  simp only [q,ExtractionRun.castSource_paths,ExtractionRun.rename_paths]

theorem ExtractionStep.shift_reflect (k : Nat)
    {r : ExtractionRun t} {s : ExtractionRun (Lambda.rename (fun i => i+k) t)}
    (step : ExtractionStep (r.rename (fun i => i+k)) s) :
    ∃q,ExtractionStep r q ∧ s=q.rename (fun i => i+k) :=
  step.rename_reflect (ν := fun i => i-k) (fun i => Nat.add_sub_cancel i k)

end Lamping.Lambda
