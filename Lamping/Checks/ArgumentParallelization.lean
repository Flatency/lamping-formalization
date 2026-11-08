import Lamping.Lambda.ArgumentParallelCuts
import Lamping.Lambda.ArgumentCommutation
import Lamping.Lambda.ArgumentParallelization
namespace Lamping.Checks.ArgumentParallelization
open Lambda
abbrev delta : Term := .lam (.app (.var 0) (.var 0))
abbrev omegaTerm : Term := .app delta delta
abbrev twins : Term := .app omegaTerm omegaTerm
def rightStep : BetaAt twins [.arg] twins := ⟨.app (.var 0) (.var 0),delta,rfl,rfl⟩
def leftStep : BetaAt twins [.fn] twins := ⟨.app (.var 0) (.var 0),delta,rfl,rfl⟩
example : ∃ (v : Term) (source : BetaAt twins [.fn] v)
    (after : ParallelStep ((singleContraction source).residualSet [[.arg]]) v twins),
    PermEq ((ParallelHistory.single (singleContraction rightStep)).append (.single (singleContraction leftStep)))
      ((ParallelHistory.single (singleContraction source)).append (.single after)) ∧
    ∀ p∈after.paths, DisjointPositions [.fn] p := by
  apply (singleContraction rightStep).pull_inside_step (site:=[.fn]) (q:=[])
  · intro p hp
    cases List.mem_singleton.mp hp
    exact rightStep.redex
  · intro r hr
    have same := List.mem_singleton.mp hr
    rw [same]
    exact DisjointPositions.head_ne (by intro h; cases h)
example (h : ParallelStep F t u)
    (apart : ∀ r : RedexOcc t, r.val∈F → DisjointPositions cut r.val) :
    ∀ q∈h.paths, DisjointPositions cut q := h.paths_apart apart
example (h : ParallelStep F t u) (s : RedexOcc t)
    (selected : s.val∈F) (inside : ∃ q, s.val=site++q)
    (valid : ∀ p∈F, ∃ z, subtermAt t p=some z ∧ IsRedex z)
    (scope : ∀ r : RedexOcc t, r.val∈F → r.val=s.val ∨ DisjointPositions site r.val) :
    ∃ (v : Term) (head : BetaAt t s.val v)
      (tail : ParallelStep ((singleContraction head).residualSet F) v u),
      PermEq (.single h) ((ParallelHistory.single (singleContraction head)).append (.single tail)) ∧
      ∀ p∈tail.paths, DisjointPositions site p :=
  h.selected_factor_apart s selected inside valid scope
#print axioms Marked.StepAt.apart_cut
#print axioms ParallelStep.paths_apart
#print axioms ParallelStep.selected_factor_apart
#print axioms ParallelStep.pull_inside_step
example (ρ : ParallelHistory t u) (outside : ApartHistory site ρ)
    (σ : ParallelHistory u w) (atomic : Atomic σ) (inside : Internal site σ) :
    ∃ (v : Term) (source : ParallelHistory t v) (after : ParallelHistory v w),
      Atomic source ∧ source.derivation.paths=σ.derivation.paths ∧
      PermEq (ρ.append σ) (source.append after) ∧ ApartHistory site after :=
  outside.pull_inside atomic inside
example (ρ : ParallelHistory t u) (outside : ApartHistory site ρ)
    (r : RedexOcc t) (inside : ∃ q, r.val=site++q) :
    ∃ s : RedexOcc u, s.val=r.val ∧ ρ.derivation.Residual r s :=
  outside.inside_survives r inside
#print axioms Atomic.pull_inside_step
#print axioms ApartHistory.pull_inside
#print axioms ApartHistory.inside_survives
example {R : BetaAt t p u} {copy : ParallelHistory u v} {original : ParallelHistory t w}
    (lift : ArgumentLift R copy original) (copyAtomic : Atomic copy) (originalAtomic : Atomic original)
    {full : ParallelHistory u z} {last : ParallelStep F w z}
    (row : StepProjection (singleContraction R) original full last) :
    ∃ other : ParallelHistory v z, PermEq full (copy.append other) ∧ ApartHistory (p++lift.occurrence) other :=
  lift.factor_projection copyAtomic originalAtomic row
example {R : BetaAt t p u} {copy : ParallelHistory u v} {original : ParallelHistory t w}
    (lift : ArgumentLift R copy original) (copyAtomic : Atomic copy) (originalAtomic : Atomic original)
    (positive : 0<copy.length) (pre : ParallelHistory m t) (preAtomic : Atomic pre)
    (a b : RedexWithHistory m)
    (originalRep : RunRepresents (.of (pre.append original) (preAtomic.append originalAtomic)) a)
    (copyRep : RunRepresents (.of ((pre.append (.single (singleContraction R))).append copy)
      ((preAtomic.append (.single R)).append copyAtomic)) b) :
    ∃ common : RedexWithHistory m, Copy a common ∧ Copy b common :=
  lift.pointed_join copyAtomic originalAtomic positive pre preAtomic a b originalRep copyRep
def duplicateRoot : BetaAt (.app (.lam (.app (.var 0) (.var 0))) omegaTerm) [] twins :=
  ⟨.app (.var 0) (.var 0),omegaTerm,rfl,rfl⟩
def twoLeft : ParallelHistory twins twins := .cons (singleContraction leftStep) (.single (singleContraction leftStep))
theorem twoLeft_atomic : Atomic twoLeft := .cons leftStep (.single leftStep)
/-- A genuine non-linear beta duplicates the argument; the selected copy
executes two actual contractions. Its original/copy pointed runs join by Copy. -/
example : ∃ (w : Term) (original : ParallelHistory (.app (.lam (.app (.var 0) (.var 0))) omegaTerm) w)
    (ordinary : Atomic original) (_lift : ArgumentLift duplicateRoot twoLeft original)
    (a b common : RedexWithHistory (.app (.lam (.app (.var 0) (.var 0))) omegaTerm)),
    RunRepresents (.of original ordinary) a ∧
    RunRepresents (.of ((ParallelHistory.single (singleContraction duplicateRoot)).append twoLeft)
      ((Atomic.single duplicateRoot).append twoLeft_atomic)) b ∧ Copy a common ∧ Copy b common := by
  have inside : Internal [.fn] twoLeft := by
    intro q hq
    change q∈[[.fn],[.fn]] at hq
    have same : q=[.fn] := by simpa using hq
    exact ⟨[],by simpa using same⟩
  obtain ⟨w,original,ordinary,lift,_⟩ := argument_lift_exists duplicateRoot rfl (occurrence:=[.fn]) rfl twoLeft inside
  have positive : 0<twoLeft.length := by decide
  let originalRun := ExtractionRun.of original ordinary
  let copyRun := ExtractionRun.of ((ParallelHistory.single (singleContraction duplicateRoot)).append twoLeft)
    ((Atomic.single duplicateRoot).append twoLeft_atomic)
  obtain ⟨a,ha⟩ := originalRun.represents_exists (by
    change 0<original.length
    rw [lift.length twoLeft_atomic ordinary]; exact positive)
  obtain ⟨b,hb⟩ := copyRun.represents_exists (by decide)
  obtain ⟨common,left,right⟩ := lift.pointed_join twoLeft_atomic ordinary positive (.nil _) (.nil _) a b ha hb
  exact ⟨w,original,ordinary,lift,a,b,common,ha,hb,left,right⟩
#print axioms Atomic.argument_projection_factor
#print axioms ArgumentLift.factor_projection
#print axioms ArgumentLift.parallelized_factor
#print axioms argument_pointed_join
#print axioms ArgumentLift.pointed_join
#print axioms ArgumentLift.pointed_family
end Lamping.Checks.ArgumentParallelization
