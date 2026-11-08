import Lamping.Lambda.SubstitutionBeta
import Lamping.Lambda.ExtractionMirror
namespace Lamping.Lambda
namespace Atomic

theorem substitute_exists {ρ : ParallelHistory t u} (_h : Atomic ρ) (σ : Nat → Term) :
    ∃q : ParallelHistory (subst σ t) (subst σ u), Atomic q ∧ q.derivation.paths=ρ.derivation.paths :=
  (ρ.derivation.valid.subst σ).atomic

noncomputable def substitute {ρ : ParallelHistory t u} (h : Atomic ρ) (σ : Nat → Term) :
    ParallelHistory (subst σ t) (subst σ u) := Classical.choose (h.substitute_exists σ)

theorem substitute_atomic {ρ : ParallelHistory t u} (h : Atomic ρ) (σ : Nat → Term) :
    Atomic (h.substitute σ) := (Classical.choose_spec (h.substitute_exists σ)).1

@[simp] theorem substitute_paths {ρ : ParallelHistory t u} (h : Atomic ρ) (σ : Nat → Term) :
    (h.substitute σ).derivation.paths=ρ.derivation.paths := (Classical.choose_spec (h.substitute_exists σ)).2

@[simp] theorem substitute_length {ρ : ParallelHistory t u} (h : Atomic ρ) (σ : Nat → Term) :
    (h.substitute σ).length=ρ.length := by
  rw [←(h.substitute_atomic σ).paths_length,substitute_paths,h.paths_length]

theorem substitute_append {ρ : ParallelHistory t u} {τ : ParallelHistory u v}
    (h : Atomic ρ) (k : Atomic τ) (σ : Nat → Term) :
    (h.append k).substitute σ=(h.substitute σ).append (k.substitute σ) := by
  apply ((h.append k).substitute_atomic σ).paths_injective
    ((h.substitute_atomic σ).append (k.substitute_atomic σ))
  simp only [substitute_paths,ParallelHistory.derivation_append,Derivation.append]

theorem substitute_nil (t : Term) (σ : Nat → Term) :
    (Atomic.nil t).substitute σ=.nil (subst σ t) := by
  apply ((Atomic.nil t).substitute_atomic σ).paths_injective (.nil _)
  exact (Atomic.nil t).substitute_paths σ

theorem substitute_single (R : BetaAt t p u) (σ : Nat → Term) :
    (Atomic.single R).substitute σ=.single (singleContraction (R.subst σ)) := by
  apply ((Atomic.single R).substitute_atomic σ).paths_injective (.single (R.subst σ))
  exact (Atomic.single R).substitute_paths σ

theorem substitute_internal {ρ : ParallelHistory t u} (h : Atomic ρ)
    (inside : Internal site ρ) (σ : Nat → Term) : Internal site (h.substitute σ) := by
  intro q hq
  exact inside q (h.substitute_paths σ ▸ hq)
end Atomic

noncomputable def ExtractionRun.subst (σ : Nat → Term) (r : ExtractionRun t) :
    ExtractionRun (Lambda.subst σ t) := .of (r.atomic.substitute σ) (r.atomic.substitute_atomic σ)

@[simp] theorem ExtractionRun.subst_paths (r : ExtractionRun t) (σ : Nat → Term) :
    (r.subst σ).history.derivation.paths=r.history.derivation.paths := r.atomic.substitute_paths σ

@[simp] theorem ExtractionRun.subst_length (r : ExtractionRun t) (σ : Nat → Term) :
    (r.subst σ).history.length=r.history.length := r.atomic.substitute_length σ

theorem ExtractionRun.subst_prepend (r : ExtractionRun t)
    (pre : ParallelHistory m t) (ha : Atomic pre) (σ : Nat → Term) :
    (r.prepend pre ha).subst σ=(r.subst σ).prepend (ha.substitute σ) (ha.substitute_atomic σ) := by
  apply ExtractionRun.ext_paths
  simp only [ExtractionRun.subst_paths,ExtractionRun.prepend,ExtractionRun.of,
    ParallelHistory.derivation_append,Derivation.append,Atomic.substitute_paths]

end Lamping.Lambda
