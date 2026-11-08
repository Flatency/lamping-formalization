import Lamping.Lambda.ProjectionRowUniqueness
import Lamping.Lambda.ExtractionArgumentUniqueness
import Lamping.Lambda.ExtractionRegionArgumentExclusion
import Lamping.Lambda.ExtractionContexts
import Lamping.Lambda.ResidualExtractionPeak
namespace Lamping.Lambda

/-- The original four extraction generators with their common ordinary
 prefix removed. This records a genuine deletion at the first contraction. -/
inductive RootExtraction (R : BetaAt t p u) : ExtractionRun u → ExtractionRun t → Prop where
  | residual (S : BetaAt u q v) (A : BetaAt t a w)
      (old : (singleContraction R).derivation.Residual ⟨a,A.redex⟩ ⟨q,S.redex⟩) :
      RootExtraction R (.of (.single (singleContraction S)) (.single S))
        (.of (.single (singleContraction A)) (.single A))
  | disjoint (σ : ParallelHistory t v) (ha : Atomic σ)
      (τ : ParallelHistory u w) (hb : Atomic τ) (last : ParallelStep F v w)
      (row : StepProjection (singleContraction R) σ τ last)
      (positive : 0 < σ.length) (site : Path) (apart : DisjointPositions p site)
      (inside : Internal site σ) : RootExtraction R (.of τ hb) (.of σ ha)
  | functionPart (σ : ParallelHistory t v) (ha : Atomic σ)
      (τ : ParallelHistory u w) (hb : Atomic τ) (last : ParallelStep F v w)
      (row : StepProjection (singleContraction R) σ τ last)
      (positive : 0 < σ.length) (inside : Internal (p ++ [.fn]) σ) :
      RootExtraction R (.of τ hb) (.of σ ha)
  | argumentPart (σ : ParallelHistory u v) (ha : Atomic σ)
      (τ : ParallelHistory t w) (hb : Atomic τ) (positive : 0 < σ.length)
      (lift : ArgumentLift R σ τ) : RootExtraction R (.of σ ha) (.of τ hb)

theorem RootExtraction.step (h : RootExtraction R r s) :
    ExtractionStep (.of (.cons (singleContraction R) r.history) (.cons R r.atomic)) s := by
  cases h with
  | residual S A old => exact .residual (.nil _) (.nil _) R S A old
  | disjoint σ ha τ hb last row positive site apart inside =>
    exact .disjoint (.nil _) (.nil _) R σ ha τ hb last row positive site apart inside
  | functionPart σ ha τ hb last row positive inside =>
    exact .functionPart (.nil _) (.nil _) R σ ha τ hb last row positive inside
  | argumentPart σ ha τ hb positive lift =>
    exact .argumentPart (.nil _) (.nil _) R σ ha τ hb positive lift

theorem RootExtraction.prepend {R : BetaAt t p u} {r : ExtractionRun u} {s : ExtractionRun t}
    (h : RootExtraction R r s)
    (pre : ParallelHistory m t) (ha : Atomic pre) :
    ExtractionStep ((ExtractionRun.of (.cons (singleContraction R) r.history)
      (.cons R r.atomic)).prepend pre ha) (s.prepend pre ha) := h.step.prepend pre ha

/-- Every original generator has an exact root presentation after removing
 its own ordinary prefix. No endpoint-only or permutation quotient is used. -/
theorem ExtractionStep.root_factor {r s : ExtractionRun m} (h : ExtractionStep r s) :
    ∃ (t u : Term) (p : Path) (pre : ParallelHistory m t) (ha : Atomic pre)
      (R : BetaAt t p u) (tail : ExtractionRun u) (result : ExtractionRun t),
      RootExtraction R tail result ∧
      r = (ExtractionRun.of (.cons (singleContraction R) tail.history) (.cons R tail.atomic)).prepend pre ha ∧
      s = result.prepend pre ha := by
  cases h with
  | residual pre ha R S A old =>
    refine ⟨_,_,_,pre,ha,R,.of (.single (singleContraction S)) (.single S),
      .of (.single (singleContraction A)) (.single A),.residual S A old,?_,rfl⟩
    apply ExtractionRun.ext_paths
    simp only [ExtractionRun.of, ExtractionRun.prepend, ParallelHistory.derivation_append,
      Derivation.append, ParallelHistory.single_derivation, ParallelHistory.derivation,
      List.append_assoc]
  | disjoint pre ha R σ hσ τ hτ last row positive site apart inside =>
    refine ⟨_,_,_,pre,ha,R,.of τ hτ,.of σ hσ,
      .disjoint σ hσ τ hτ last row positive site apart inside,?_,rfl⟩
    apply ExtractionRun.ext_paths
    simp only [ExtractionRun.of, ExtractionRun.prepend, ParallelHistory.derivation_append,
      Derivation.append, ParallelHistory.single_derivation, ParallelHistory.derivation,
      List.append_assoc]
  | functionPart pre ha R σ hσ τ hτ last row positive inside =>
    refine ⟨_,_,_,pre,ha,R,.of τ hτ,.of σ hσ,
      .functionPart σ hσ τ hτ last row positive inside,?_,rfl⟩
    apply ExtractionRun.ext_paths
    simp only [ExtractionRun.of, ExtractionRun.prepend, ParallelHistory.derivation_append,
      Derivation.append, ParallelHistory.single_derivation, ParallelHistory.derivation,
      List.append_assoc]
  | argumentPart pre ha R σ hσ τ hτ positive lift =>
    refine ⟨_,_,_,pre,ha,R,.of σ hσ,.of τ hτ,
      .argumentPart σ hσ τ hτ positive lift,?_,rfl⟩
    apply ExtractionRun.ext_paths
    simp only [ExtractionRun.of, ExtractionRun.prepend, ParallelHistory.derivation_append,
      Derivation.append, ParallelHistory.single_derivation, ParallelHistory.derivation,
      List.append_assoc]

private theorem residual_row_target (R : BetaAt t p u) (S : BetaAt u q v)
    (A : BetaAt t a x)
    (old : (singleContraction R).derivation.Residual ⟨a,A.redex⟩ ⟨q,S.redex⟩)
    (σ : ParallelHistory t w) (ha : Atomic σ) {last : ParallelStep F w v}
    (row : StepProjection (singleContraction R) σ (.single (singleContraction S)) last) :
    ExtractionRun.of σ ha = .of (.single (singleContraction A)) (.single A) := by
  cases ha with
  | nil => have len := row.length; simp only [ParallelHistory.length, ParallelHistory.single] at len; omega
  | @cons t b y w tail B ht =>
    have len := row.length
    cases tail with
    | cons head rest =>
      simp only [ParallelHistory.length, ParallelHistory.single] at len
      omega
    | nil =>
      have back := row.singleton_residual B S
      have origin := (singleContraction R).derivation.residual_unique_source
        ⟨b,B.redex⟩ ⟨a,A.redex⟩ ⟨q,S.redex⟩ back old
      apply ExtractionRun.ext_paths
      change [b] = [a]
      exact congrArg (fun r : RedexOcc t => [r.val]) origin

private theorem residual_argument_target (R : BetaAt t p u) (S : BetaAt u q v)
    (A : BetaAt t a x)
    (old : (singleContraction R).derivation.Residual ⟨a,A.redex⟩ ⟨q,S.redex⟩)
    (original : ParallelHistory t w) (ha : Atomic original)
    (lift : ArgumentLift R (.single (singleContraction S)) original) :
    ExtractionRun.of original ha = .of (.single (singleContraction A)) (.single A) := by
  have len := lift.length (.single S) ha
  cases ha with
  | nil => simp only [ParallelHistory.length, ParallelHistory.single] at len; omega
  | @cons t b y w tail B ht =>
    cases tail with
    | cons head rest => simp only [ParallelHistory.length, ParallelHistory.single] at len; omega
    | nil => exact (residual_argument_target_unique R S A B old lift).symm

/-- At a fixed deleted contraction the four faithful source presentations
 have a unique actual target. This covers all same-deletion critical pairs. -/
theorem RootExtraction.target_unique (h : RootExtraction R r s) (k : RootExtraction R r s') : s = s' := by
  cases h with
  | residual S A old =>
    cases k with
    | residual S B old' => exact residual_extraction_target_unique (.nil _) (.nil _) R S A B old old'
    | disjoint σ ha τ hb last row positive site apart inside =>
      exact (residual_row_target R S A old σ ha row).symm
    | functionPart σ ha τ hb last row positive inside =>
      exact (residual_row_target R S A old σ ha row).symm
    | argumentPart σ ha τ hb positive lift =>
      exact (residual_argument_target R S A old τ hb lift).symm
  | disjoint σ ha τ hb last row positive site apart inside =>
    cases k with
    | residual S A old => exact residual_row_target R S A old σ ha row
    | disjoint σ' ha' τ' hb' last' row' positive' site' apart' inside' =>
      exact row.atomic_top_run_unique row' ha ha' hb
    | functionPart σ' ha' τ' hb' last' row' positive' inside' =>
      exact row.atomic_top_run_unique row' ha ha' hb
    | argumentPart σ' ha' τ' hb' positive' lift =>
      exact False.elim (lift.no_region_projection R row ha hb hb' (.inl apart) inside positive')
  | functionPart σ ha τ hb last row positive inside =>
    cases k with
    | residual S A old => exact residual_row_target R S A old σ ha row
    | disjoint σ' ha' τ' hb' last' row' positive' site' apart' inside' =>
      exact row.atomic_top_run_unique row' ha ha' hb
    | functionPart σ' ha' τ' hb' last' row' positive' inside' =>
      exact row.atomic_top_run_unique row' ha ha' hb
    | argumentPart σ' ha' τ' hb' positive' lift =>
      exact False.elim (lift.no_region_projection R row ha hb hb' (.inr rfl) inside positive')
  | argumentPart σ ha τ hb positive lift =>
    cases k with
    | residual S A old => exact residual_argument_target R S A old τ hb lift
    | disjoint σ' ha' τ' hb' last' row' positive' site' apart' inside' =>
      exact False.elim (lift.no_region_projection R row' ha' ha hb (.inl apart') inside' positive)
    | functionPart σ' ha' τ' hb' last' row' positive' inside' =>
      exact False.elim (lift.no_region_projection R row' ha' ha hb (.inr rfl) inside' positive)
    | argumentPart σ' ha' τ' hb' positive' lift' =>
      exact lift.original_run_unique R lift' ha hb hb' positive

/-- Equal actual deletion indices in a common source schedule give identical
 targets, even when their prefixes and redex implementations were presented
 separately. Ordinary alignment recovers the same prefix and root redex. -/
theorem RootExtraction.same_index_target_unique
    (pre : ParallelHistory m t) (ha : Atomic pre)
    (pre' : ParallelHistory m t') (ha' : Atomic pre')
    (R : BetaAt t p u) (R' : BetaAt t' p' u')
    (tail : ExtractionRun u) (tail' : ExtractionRun u')
    (result : ExtractionRun t) (result' : ExtractionRun t')
    (h : RootExtraction R tail result) (k : RootExtraction R' tail' result')
    (whole : (ExtractionRun.of (.cons (singleContraction R) tail.history)
      (.cons R tail.atomic)).prepend pre ha =
      (ExtractionRun.of (.cons (singleContraction R') tail'.history)
      (.cons R' tail'.atomic)).prepend pre' ha')
    (index : pre.length = pre'.length) :
    result.prepend pre ha = result'.prepend pre' ha' := by
  cases tail with
  | mk target rest hr =>
    cases tail' with
    | mk target' rest' hr' =>
      have endpoint : target = target' := congrArg ExtractionRun.target whole
      cases endpoint
      have paths := congrArg (fun r => r.history.derivation.paths) whole
      have same : pre.append (.cons (singleContraction R) rest) =
          pre'.append (.cons (singleContraction R') rest') :=
        (ha.append (.cons R hr)).paths_injective (ha'.append (.cons R' hr')) paths
      obtain ⟨sourceEq, prefixEq, suffixEq⟩ := ha.prefix_alignment ha'
        (.cons R hr) (.cons R' hr') same index
      cases sourceEq
      have prefixes := eq_of_heq prefixEq
      cases prefixes
      have suffixes := eq_of_heq suffixEq
      have suffixPaths := congrArg (fun r => r.derivation.paths) suffixes
      change p :: rest.derivation.paths = p' :: rest'.derivation.paths at suffixPaths
      have rootName := (List.cons.inj suffixPaths).1
      cases rootName
      have middle := R.unique R'
      cases middle
      have roots : R = R' := Subsingleton.elim _ _
      cases roots
      have tails := hr.paths_injective hr' (List.cons.inj suffixPaths).2
      cases tails
      have results := h.target_unique k
      cases results
      rfl

end Lamping.Lambda
