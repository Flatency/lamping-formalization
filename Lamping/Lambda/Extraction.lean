import Lamping.Lambda.SingleContraction
import Lamping.Lambda.DerivationProjection
namespace Lamping.Lambda

/-- Ordinary beta histories represented by genuine singleton parallel steps.
 In particular these contain no empty step or arbitrary grouping of a set. -/
inductive Atomic : ParallelHistory t u → Prop where
  | nil (t) : Atomic (.nil t)
  | cons (h : BetaAt t p u) : Atomic σ → Atomic (.cons (singleContraction h) σ)
namespace Atomic
 theorem append (h : Atomic ρ) (k : Atomic σ) : Atomic (ρ.append σ) := by
   induction h with
   | nil => exact k
   | cons h hs ih => exact .cons h (ih k)
 theorem single (h : BetaAt t p u) : Atomic (ParallelHistory.single (singleContraction h)) :=
   .cons h (.nil _)
 theorem paths_length (h : Atomic ρ) : ρ.derivation.paths.length = ρ.length := by
   induction h with
   | nil => rfl
   | cons h hs ih =>
     change ([(_ : Path)] ++ _).length = 1 + _
     simp only [List.length_append, List.length_singleton, ih]
end Atomic

/-- The original extraction operates on ordinary contraction histories,
 including the final contracted redex. Restricting to Atomic removes the
 empty-step/grouping ambiguity of the parallel representation. -/
structure ExtractionRun (source : Term) where
  target : Term
  history : ParallelHistory source target
  atomic : Atomic history
namespace ExtractionRun
 def of (h : ParallelHistory t u) (ha : Atomic h) : ExtractionRun t := ⟨u, h, ha⟩
 def rank (h : ExtractionRun t) : Nat := h.history.length
end ExtractionRun

/-- Every actual contraction lies strictly inside the fixed subexpression
 rooted at p, allowing contraction at that subexpression's root. -/
def Internal (p : Path) (ρ : ParallelHistory t u) : Prop :=
  ∀ q ∈ ρ.derivation.paths, ∃ s, q = p ++ s

def DisjointPositions (p q : Path) : Prop :=
  (¬ ∃ s, q = p ++ s) ∧ (¬ ∃ s, p = q ++ s)

/-- The chosen body variable occurrence (the source's i-th argument instance).
 De Bruijn depth distinguishes the contracted binder from inner binders. -/
def ArgumentOccurrence (b : Term) (p : Path) : Prop :=
  subtermAt b p = some (.var (binderDepth p))

/-- A concrete pullback of a history from a specified argument copy. Both
 histories perform the identical local occurrence sequence. The tile row
 records its genuine full parallelization after R, not endpoint equality. -/
structure ArgumentLift (hR : BetaAt t p u) (σ : ParallelHistory u v)
    (σ' : ParallelHistory t w) where
  body : Term
  argument : Term
  redex : subtermAt t p = some (.app (.lam body) argument)
  occurrence : Path
  isVariable : ArgumentOccurrence body occurrence
  localPaths : List Path
  copy_paths : σ.derivation.paths = localPaths.map (fun q => (p ++ occurrence) ++ q)
  original_paths : σ'.derivation.paths = localPaths.map (fun q => (p ++ [.arg]) ++ q)
  parallelization : ∃ (z : Term) (F : List Path) (σfull : ParallelHistory u z)
    (last : ParallelStep F w z), StepProjection (singleContraction hR) σ' σfull last

/-- The four source extraction generators, on actual ordinary contraction
 histories. Local function-part includes the whole lambda subexpression.
 The fourth rule retains a particular bound-variable occurrence and a concrete
 mirrored history in the original argument. -/
inductive ExtractionStep : ExtractionRun m → ExtractionRun m → Prop where
  | residual (ρ : ParallelHistory m t) (hρ : Atomic ρ)
      (R : BetaAt t p u) (S : BetaAt u q v) (S' : BetaAt t q' v')
      (hs : (singleContraction R).derivation.Residual ⟨q', S'.redex⟩ ⟨q, S.redex⟩) :
      ExtractionStep
        (.of ((ρ.append (.single (singleContraction R))).append (.single (singleContraction S)))
          ((hρ.append (.single R)).append (.single S)))
        (.of (ρ.append (.single (singleContraction S'))) (hρ.append (.single S')))
  | disjoint (ρ : ParallelHistory m t) (hρ : Atomic ρ)
      (R : BetaAt t p u) (σ : ParallelHistory t v) (hσ : Atomic σ)
      (σ' : ParallelHistory u w) (hσ' : Atomic σ')
      (last : ParallelStep F v w) (row : StepProjection (singleContraction R) σ σ' last)
      (positive : 0 < σ.length) (site : Path) (apart : DisjointPositions p site)
      (inside : Internal site σ) :
      ExtractionStep
        (.of ((ρ.append (.single (singleContraction R))).append σ')
          ((hρ.append (.single R)).append hσ'))
        (.of (ρ.append σ) (hρ.append hσ))
  | functionPart (ρ : ParallelHistory m t) (hρ : Atomic ρ)
      (R : BetaAt t p u) (σ : ParallelHistory t v) (hσ : Atomic σ)
      (σ' : ParallelHistory u w) (hσ' : Atomic σ')
      (last : ParallelStep F v w) (row : StepProjection (singleContraction R) σ σ' last)
      (positive : 0 < σ.length) (inside : Internal (p ++ [.fn]) σ) :
      ExtractionStep
        (.of ((ρ.append (.single (singleContraction R))).append σ')
          ((hρ.append (.single R)).append hσ'))
        (.of (ρ.append σ) (hρ.append hσ))
  | argumentPart (ρ : ParallelHistory m t) (hρ : Atomic ρ)
      (R : BetaAt t p u) (σ : ParallelHistory u v) (hσ : Atomic σ)
      (σ' : ParallelHistory t w) (hσ' : Atomic σ')
      (positive : 0 < σ.length) (lift : ArgumentLift R σ σ') :
      ExtractionStep
        (.of ((ρ.append (.single (singleContraction R))).append σ)
          ((hρ.append (.single R)).append hσ))
        (.of (ρ.append σ') (hρ.append hσ'))
end Lamping.Lambda

