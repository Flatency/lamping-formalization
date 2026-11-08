import Lamping.Lambda.ContextualCreationSeparation
import Lamping.Lambda.AtomicRowExistence
import Lamping.Lambda.CreationPullback
import Lamping.Lambda.SingletonProjectionRow
import Lamping.Lambda.ExtractionFunctionResidualPeak
import Lamping.Lambda.OrdinarySplits
import Lamping.Lambda.ExtractionInternal
import Lamping.Lambda.ProjectionSplits
import Lamping.Lambda.ExtractionFunctionLongTail
import Lamping.Lambda.ExtractionArgumentResidualPeak
import Lamping.Lambda.RenameResiduals
import Lamping.Lambda.ExtractionArgumentLongTail
import Lamping.Lambda.ProjectionRowUniqueness
import Lamping.Lambda.ExtractionArgumentUniqueness
import Lamping.Lambda.ExtractionRegionArgumentExclusion
import Lamping.Lambda.ExtractionIndex
import Lamping.Lambda.ExtractionCuts
import Lamping.Lambda.RootTailResidualPeak
import Lamping.Lambda.ExtractionRename
import Lamping.Lambda.SingletonCube
import Lamping.Lambda.ExtractionFunctionRegionPeak
import Lamping.Lambda.ExtractionFunctionRegionLongTail
import Lamping.Lambda.RootArgumentTailPeak
import Lamping.Lambda.RootDisjointTailPeak
import Lamping.Lambda.RootTailRegionPeak
import Lamping.Lambda.ExtractionFunctionArgumentPeak
import Lamping.Lambda.ExtractionChurchRosser
import Lamping.Lambda.ExtractionNormalHead
import Lamping.Lambda.ArgumentPointedPrefix
import Lamping.Lambda.CanonicalCopyAncestor
import Lamping.Lambda.FreshPointedNormal
import Lamping.Lambda.FamilyCopyAncestor
import Lamping.Lambda.CompleteFamilyAncestors
import Lamping.Lambda.ParallelScopes
import Lamping.Lambda.TagProjection
import Lamping.Lambda.FiniteSelectionReindex
import Lamping.Lambda.DisjointCommutation
import Lamping.Lambda.SubstitutionOrigins
import Lamping.Lambda.RootResidualPaths
import Lamping.Lambda.CompleteFamilies
import Lamping.Lambda.Standardization
import Lamping.Lambda.ExtractionFamilies
import Lamping.Lambda.OccurrenceRank
import Lamping.Lambda.ArgumentPullback
import Lamping.Lambda.HistoryProjection
import Lamping.Lambda.InitialFamilies
import Lamping.Lambda.MaximalCopies
import Lamping.Lambda.ExtractionConfluence
namespace Lamping.Checks.Families
open Lambda

def I : Term := .lam (.var 0)
def A : Term := .app I (.var 0)
def initial : Term := .app I A

def outer : Derivation initial A := ⟨[[]], .cons
  (by exact ⟨.var 0, A, rfl, rfl⟩) (.nil _)⟩
def inner : Derivation initial A := ⟨[[.arg]], .cons
  (by exact ⟨.var 0, .var 0, rfl, rfl⟩) (.nil _)⟩
-- Same start and endpoint cannot erase the actual history identity.
example : outer ≠ inner := by
  intro h
  have hp := congrArg Derivation.paths h
  contradiction

def oldOuter : RedexOcc initial := ⟨[], _, rfl, trivial⟩
def oldInner : RedexOcc initial := ⟨[.arg], _, rfl, trivial⟩
def afterRoot : RedexOcc A := ⟨[], _, rfl, trivial⟩

def trackedOuter : Marked := .app [[.arg]] (.lam (.var 0)) (.var 0)
theorem outer_tracking : Marked.History outer.paths (Marked.mark [] initial) trackedOuter :=
  .cons (.appRoot _ _ _) (.nil _)
example : outer.Residual oldInner afterRoot :=
  ⟨trackedOuter, outer_tracking, rfl, by decide⟩
example : ¬ outer.Residual oldOuter afterRoot := by
  rintro ⟨v, hv, _, hr⟩
  have he := hv.deterministic outer_tracking
  subst v
  change [] ∈ Marked.tracePositions [] trackedOuter at hr
  simp [trackedOuter, Marked.tracePositions] at hr

-- A contraction really duplicates a passive old name and erases its own.
def duplicated : Marked := Marked.contract (.app [] (.var 0) (.var 0))
  (.app [[.arg]] (.lam (.var 0)) (.var 0))
example : Marked.tracePositions [.arg] duplicated = [[.fn], [.arg]] := by decide
example : Marked.tracePositions [] duplicated = [] := by decide

example (a : RedexWithHistory m) : Copy a a := Copy.refl a
example (a : RedexWithHistory m) : FamilyEq a a := FamilyEq.refl a
example (h : FamilyEq a b) : FamilyEq b a := h.symm
example (h : FamilyEq a b) (k : FamilyEq b c) : FamilyEq a c := h.trans k

#print axioms Derivation.residual_nil
#print axioms ParallelStep.exists_target
#print axioms ParallelStep.endpoint
#print axioms ParallelStep.old_residual
#print axioms PermEq.least
#print axioms FamilyEq.equivalence
#print axioms FamilyEq.of_permutation
-- The same endpoint is provably insufficient even for generated PermEq.
def outerParallel : ParallelStep [[]] initial A where
  paths := [[]]
  markedTarget := trackedOuter
  complete := (Marked.completeOld_iff [[]] initial).mpr
    ⟨.cons (.root _ _ _) (.nil _), by trivial⟩
  target_eq := rfl

def trackedInner : Marked := .app [[]] (.lam (.var 0)) (.var 0)
def innerParallel : ParallelStep [[.arg]] initial A where
  paths := [[.arg]]
  markedTarget := trackedInner
  complete := (Marked.completeOld_iff [[.arg]] initial).mpr
    ⟨.cons (.appR (.root _ _ _)) (.nil _), by trivial⟩
  target_eq := rfl

example : ¬ PermEq (ParallelHistory.single outerParallel) (.single innerParallel) := by
  intro h
  have hr : innerParallel.derivation.Residual oldOuter afterRoot :=
    (innerParallel.residual_iff oldOuter afterRoot).mpr (by decide)
  have hl := (h.residual oldOuter afterRoot).mpr (by simpa only [ParallelHistory.single_derivation] using hr)
  rw [ParallelHistory.single_derivation, outerParallel.residual_iff] at hl
  change [] ∈ Marked.tracePositions [] trackedOuter at hl
  simp [trackedOuter, Marked.tracePositions] at hl

-- A nonempty complete-family prefix may finish at a genuine beta redex.
def delta : Term := .lam (.app (.var 0) (.var 0))
def omegaTerm : Term := .app delta delta
def omegaRedex : RedexOcc omegaTerm := ⟨[], _, rfl, trivial⟩
def omegaAfter : Marked := Marked.contract (.app [] (.var 0) (.var 0))
  (.lam (.app [] (.var 0) (.var 0)))
def omegaParallel : ParallelStep [[]] omegaTerm omegaTerm where
  paths := [[]]
  markedTarget := omegaAfter
  complete := (Marked.completeOld_iff [[]] omegaTerm).mpr
    ⟨.cons (.root _ _ _) (.nil _), by trivial⟩
  target_eq := rfl

theorem omega_only_redex (s : RedexOcc omegaTerm) : s = omegaRedex := by
  have hs := (mem_redexPositions omegaTerm s.val).mpr s.property
  have he : redexPositions omegaTerm = [[]] := by decide
  rw [he] at hs
  exact Subtype.ext (List.mem_singleton.mp hs)

theorem omega_complete_step : CompleteFamilyStep (.nil omegaTerm) omegaParallel := by
  constructor
  · intro p hp
    have he := List.mem_singleton.mp hp
    subst p
    exact omegaRedex.property
  · refine ⟨omegaRedex, by simp [omegaRedex], ?_⟩
    intro s
    rw [omega_only_redex s]
    constructor
    · intro _; exact FamilyEq.refl _
    · intro _; exact List.mem_singleton_self _

example : CompleteDerivation (ParallelHistory.single omegaParallel) := by
  exact .step (.nil omegaTerm) omega_complete_step
example : IsRedex omegaTerm := by trivial
example : Closed omegaTerm := by simp [Closed, Scoped, omegaTerm, delta]

#print axioms parallel_marked_diamond
#print axioms ParallelMovesSquare.exists
#print axioms ParallelMovesSquare.residual
#print axioms Derivation.residual_append
#print axioms PermEq.residual
#print axioms Copy.trans
#print axioms omega_complete_step
end Lamping.Checks.Families



namespace Lamping.Checks.Extraction
open Lambda

def iTerm : Term := .lam (.var 0)
def argTerm : Term := .app iTerm (.var 0)
def dupBody : Term := .app (.var 0) (.var 0)
def start : Term := .app (.lam dupBody) argTerm

def outerBeta : BetaAt start [] (.app argTerm argTerm) :=
  ⟨dupBody, argTerm, rfl, rfl⟩
def copyBeta : BetaAt (.app argTerm argTerm) [.fn] (.app (.var 0) argTerm) :=
  ⟨.var 0, .var 0, rfl, rfl⟩
def originalBeta : BetaAt start [.arg] (.app (.lam dupBody) (.var 0)) :=
  ⟨.var 0, .var 0, rfl, rfl⟩

def copyHistory := ParallelHistory.single (singleContraction copyBeta)
def originalHistory := ParallelHistory.single (singleContraction originalBeta)

def actualArgumentLift : ArgumentLift outerBeta copyHistory originalHistory where
  body := dupBody
  argument := argTerm
  redex := rfl
  occurrence := [.fn]
  isVariable := rfl
  localPaths := [[]]
  copy_paths := rfl
  original_paths := rfl
  parallelization := by
    obtain ⟨w, afterR, afterOriginal, _⟩ := parallel_moves
      (singleContraction outerBeta) (singleContraction originalBeta)
    exact ⟨w, _, .single afterR, afterOriginal,
      .cons ⟨singleContraction outerBeta, singleContraction originalBeta, afterR, afterOriginal⟩ (.nil _)⟩

def beforeExtraction : ExtractionRun start := .of
  ((ParallelHistory.single (singleContraction outerBeta)).append copyHistory)
  ((Atomic.single outerBeta).append (Atomic.single copyBeta))
def afterExtraction : ExtractionRun start := .of originalHistory (Atomic.single originalBeta)

theorem argument_extraction : ExtractionStep beforeExtraction afterExtraction := by
  exact .argumentPart (.nil _) (.nil _) outerBeta copyHistory (.single copyBeta)
    originalHistory (.single originalBeta) (by decide) actualArgumentLift

example : beforeExtraction.rank = 2 := rfl
example : afterExtraction.rank = 1 := rfl
example : afterExtraction.rank < beforeExtraction.rank := argument_extraction.rank_lt
example : ExtractionNormal afterExtraction := extraction_rank_one_normal _ rfl
example : ¬ ArgumentOccurrence (.lam (.var 0)) [.body] := by simp [ArgumentOccurrence, subtermAt, binderDepth]
example : ArgumentOccurrence (.lam (.var 1)) [.body] := by rfl
example : (singleContraction outerBeta).derivation.Residual
    ⟨[.arg], originalBeta.redex⟩ ⟨[.fn], copyBeta.redex⟩ :=
  actualArgumentLift.singleton_residual outerBeta copyBeta originalBeta
#print axioms ArgumentLift.singleton_residual
#print axioms residual_argument_target_unique
example : actualArgumentLift.occurrence = actualArgumentLift.occurrence :=
  actualArgumentLift.copy_occurrence_unique outerBeta actualArgumentLift (.single copyBeta) (by decide)
example : ExtractionRun.of originalHistory (.single originalBeta) =
    ExtractionRun.of originalHistory (.single originalBeta) :=
  actualArgumentLift.original_run_unique outerBeta actualArgumentLift (.single copyBeta)
    (.single originalBeta) (.single originalBeta) (by decide)
#print axioms ArgumentLift.head_residual
#print axioms ArgumentLift.copy_occurrence_unique
#print axioms ArgumentLift.original_run_unique
#print axioms ArgumentLift.no_region_projection
example : ExtractionStep (beforeExtraction.rename (fun _ => 7)) (afterExtraction.rename (fun _ => 7)) :=
  argument_extraction.rename (fun _ => 7)
example (v : Term) (σ : ParallelHistory start v) (ha : Atomic σ)
    (F : List Path) (last : ParallelStep F v (.app (.var 0) argTerm))
    (row : StepProjection (singleContraction outerBeta) σ copyHistory last)
    (inside : Internal [.fn] σ) : False :=
  actualArgumentLift.no_region_projection outerBeta row ha (.single copyBeta) (.single originalBeta)
    (.inr rfl) inside (by decide)

-- Rule (i): the terminal left copy is a genuine old residual of the initial A.
theorem copied_residual : (singleContraction outerBeta).derivation.Residual
    ⟨[.arg], originalBeta.redex⟩ ⟨[.fn], copyBeta.redex⟩ := by
  rw [ParallelStep.residual_iff]
  decide

theorem direct_residual_extraction : ExtractionStep beforeExtraction afterExtraction := by
  exact .residual (.nil _) (.nil _) outerBeta copyBeta originalBeta copied_residual

#print axioms argument_extraction
#print axioms direct_residual_extraction
#print axioms ExtractionStep.rank_lt
#print axioms no_infinite_extraction
#print axioms extraction_wellFounded
#print axioms extraction_normal_exists_positive
#print axioms PermEq.selection
end Lamping.Checks.Extraction

namespace Lamping.Checks.Extraction
open Lambda

def leftCopy : RedexOcc (.app argTerm argTerm) := ⟨[.fn], _, rfl, trivial⟩
def rightCopy : RedexOcc (.app argTerm argTerm) := ⟨[.arg], _, rfl, trivial⟩
def argumentOriginal : RedexOcc start := ⟨[.arg], _, rfl, trivial⟩
def outerPrefix := ParallelHistory.single (singleContraction outerBeta)

theorem two_copies_same_family :
    FamilyEq ⟨_, outerPrefix, leftCopy⟩ ⟨_, outerPrefix, rightCopy⟩ := by
  have hl : Copy ⟨start, .nil start, argumentOriginal⟩ ⟨_, outerPrefix, leftCopy⟩ := by
    refine ⟨outerPrefix, .refl _, ?_⟩
    unfold outerPrefix
    rw [ParallelHistory.single_derivation, ParallelStep.residual_iff]
    decide
  have hr : Copy ⟨start, .nil start, argumentOriginal⟩ ⟨_, outerPrefix, rightCopy⟩ := by
    refine ⟨outerPrefix, .refl _, ?_⟩
    unfold outerPrefix
    rw [ParallelHistory.single_derivation, ParallelStep.residual_iff]
    decide
  exact .trans (.symm (.copy hl)) (.copy hr)

-- The bare existential in the source's “Namely” sentence is satisfied by
-- every singleton, even one that omits a coexisting member of the same family.
theorem singleton_residual_presentation (ρ : ParallelHistory m t) (S : RedexOcc t) :
    ∃ (σ : ParallelHistory m t) (τ : ParallelHistory t t),
      PermEq (σ.append τ) ρ ∧ ∀ q : RedexOcc t,
        q.val ∈ [S.val] ↔ τ.derivation.Residual S q := by
  refine ⟨ρ, .nil _, ?_, ?_⟩
  · rw [ParallelHistory.append_nil]; exact .refl _
  · intro q
    change q.val ∈ [S.val] ↔ (Derivation.nil t).Residual S q
    rw [Derivation.residual_nil]
    constructor
    · intro hq; exact Subtype.ext (List.mem_singleton.mp hq).symm
    · intro hq; cases hq; exact List.mem_singleton_self _

theorem partial_copy_step_not_complete :
    ¬ CompleteFamilyStep outerPrefix (singleContraction copyBeta) := by
  intro h
  have hr := h.maximal leftCopy rightCopy (by simp [leftCopy]) two_copies_same_family
  have hn : rightCopy.val ∉ [[Step.fn]] := by decide
  exact hn hr

#print axioms two_copies_same_family
#print axioms partial_copy_step_not_complete
end Lamping.Checks.Extraction

namespace Lamping.Checks.Extraction
open Lambda

def outerOriginal : RedexOcc start := ⟨[], outerBeta.redex⟩
theorem outer_initial_whole_family :
    CompleteFamilyStep (.nil start) (singleContraction outerBeta) := by
  constructor
  · intro p hp
    have he := List.mem_singleton.mp hp
    subst p; exact outerBeta.redex
  · refine ⟨outerOriginal, List.mem_singleton_self _, ?_⟩
    intro s
    rw [initial_families_injective]
    constructor
    · intro hs; exact Subtype.ext (List.mem_singleton.mp hs).symm
    · intro he; cases he; exact List.mem_singleton_self _

theorem outer_prefix_complete : CompleteDerivation outerPrefix :=
  .step (.nil _) outer_initial_whole_family

-- The weak “Namely” presentation does not become maximal merely because the
-- preceding prefix is complete: the two coexisting copies are still one family.
example : CompleteDerivation outerPrefix ∧
    ¬ CompleteFamilyStep outerPrefix (singleContraction copyBeta) :=
  ⟨outer_prefix_complete, partial_copy_step_not_complete⟩

#print axioms initial_family_iff
#print axioms initial_families_injective
#print axioms outer_prefix_complete
#print axioms RunRepresents.unique
end Lamping.Checks.Extraction


namespace Lamping.Checks.RootResidualPaths
open Lambda
private def I : Term := .lam (.var 0)
private def argument : Term := .app I (.var 0)
private def body : Term := .app I (.var 0)
private def rb : RedexOcc (.app (.lam body) (.var 0)) := ⟨[.fn, .body], by decide⟩
private def sb : RedexOcc (contract body (.var 0)) := ⟨[], by decide⟩
example : (rootContraction body (.var 0)).Residual rb sb :=
  root_body_residual rb sb rfl
private def ra : RedexOcc (.app (.lam (.lam (.var 1))) argument) := ⟨[.arg], by decide⟩
private def sa : RedexOcc (contract (.lam (.var 1)) argument) := ⟨[.body], by decide⟩
example : (rootContraction (.lam (.var 1)) argument).Residual ra sa :=
  root_argument_residual [.body] [] rfl ra sa rfl rfl
-- The inner bound variable is not an instance of the removed outer binder.
example : subtermAt (.lam (.var 0)) [.body] ≠ some (.var (binderDepth [.body])) := by decide
#print axioms Marked.subst_trace_iff_source
#print axioms Marked.trace_subst_insert
#print axioms root_body_residual
#print axioms root_argument_residual
#print axioms Marked.contract_trace_iff
#print axioms root_residual_iff
end Lamping.Checks.RootResidualPaths


namespace Lamping.Checks.DisjointCommutation
open Lambda
private def A : Term := .app (.lam (.var 0)) (.var 0)
private theorem leftStep : BetaAt (.app A A) [.fn] (.app (.var 0) A) :=
  ⟨.var 0, .var 0, rfl, rfl⟩
private theorem rightStep : BetaAt (.app A A) [.arg] (.app A (.var 0)) :=
  ⟨.var 0, .var 0, rfl, rfl⟩
private theorem apart : DisjointPositions [.fn] [.arg] := by
  constructor <;> rintro ⟨x, hx⟩ <;> cases hx
example : ∃ w, BetaAt (.app (.var 0) A) [.arg] w ∧
    BetaAt (.app A (.var 0)) [.fn] w := leftStep.disjoint_square rightStep apart
private def r : RedexOcc (.app A A) := ⟨[.arg], by decide⟩
private def s : RedexOcc (.app (.var 0) A) := ⟨[.arg], by decide⟩
example : (singleContraction leftStep).derivation.Residual r s :=
  leftStep.disjoint_residual r s rfl apart
#print axioms replaceAt_disjoint_square
#print axioms BetaAt.disjoint_square
#print axioms BetaAt.disjoint_residual
end Lamping.Checks.DisjointCommutation


namespace Lamping.Checks.DisjointSelection
open Lambda
private def A : Term := .app (.lam (.var 0)) (.var 0)
private theorem hl : BetaAt (.app A A) [.fn] (.app (.var 0) A) :=
  ⟨.var 0, .var 0, rfl, rfl⟩
private theorem hr : BetaAt (.app A A) [.arg] (.app A (.var 0)) :=
  ⟨.var 0, .var 0, rfl, rfl⟩
private theorem hd : DisjointPositions [.fn] [.arg] := by
  constructor <;> rintro ⟨x, hx⟩ <;> cases hx
example : [.arg] ∈ (singleContraction hl).residualSet [[.arg]] :=
  (hl.disjoint_residualSet ⟨[.arg], hr.redex⟩ hd [.arg]).mpr rfl
example : [.fn] ∉ (singleContraction hl).residualSet [[.arg]] := by
  intro h
  have hh := (hl.disjoint_residualSet ⟨[.arg], hr.redex⟩ hd [.fn]).mp h
  cases hh
example : ∃ w, ∃ sq : ParallelMovesSquare [[.fn]] [[.arg]] (.app A A)
    (.app (.var 0) A) (.app A (.var 0)) w,
    sq.first = singleContraction hl ∧ sq.second = singleContraction hr ∧
    sq.afterFirst.paths = [[.arg]] ∧ sq.afterSecond.paths = [[.fn]] :=
  hl.disjoint_parallel_square hr hd
#print axioms Marked.ReductionAt.trace_outside
#print axioms BetaAt.disjoint_residual_iff
#print axioms BetaAt.disjoint_residualSet
#print axioms ParallelStep.reindex
#print axioms BetaAt.disjoint_parallel_square
end Lamping.Checks.DisjointSelection


namespace Lamping.Checks.ApplicationIdentity
open Lambda
open Lambda.Marked
private def potential : Term := .lam (.app (.var 1) (.var 0))
example : HeadVariable [.body] 0 (markAll [] potential) :=
  headVariable_markAll (by rfl)
example : tagsAt (markAll [] potential) [.body] = [[.body]] := by decide
example : ¬ Valid (markAll [] potential) := by simp [markAll, markAllAt, potential, Valid]
example : EveryApplicationTagged (markAll [] potential) := everyApplicationTagged_markAllAt [] potential []
example : SingleTags (markAll [] potential) := singleTags_markAllAt [] potential []
private def b0 : Marked := .app [] (.var 0) (.var 0)
private def b1 : Marked := .app [[.arg]] (.var 0) (.var 0)
private def a0 : Marked := .app [[]] (.lam (.var 0)) (.var 0)
private def a1 : Marked := .app [[.arg]] (.lam (.var 0)) (.var 0)
private def t0 : Marked := .app [] (.lam b0) a0
private def t1 : Marked := .app [[.fn]] (.lam b1) a1
private theorem h0 : History [[]] t0 (Marked.contract b0 a0) :=
  .cons (.appRoot [] b0 a0) (.nil _)
private theorem h1 : History [[]] t1 (Marked.contract b1 a1) :=
  .cons (.appRoot [[.fn]] b1 a1) (.nil _)
private theorem initial_inclusion (q : Path) :
    q ∈ tracePositions [] t0 → q ∈ tracePositions [.arg] t1 := by
  simp [t0, t1, b0, b1, a0, a1, tracePositions]
  exact fun h => Or.inr h
example (q : Path) (h : q ∈ tracePositions [] (Marked.contract b0 a0)) :
    q ∈ tracePositions [.arg] (Marked.contract b1 a1) :=
  h0.trace_inclusion h1 rfl initial_inclusion q h
example : [] ∉ tracePositions [] (Marked.contract b0 a0) := by decide
example : [] ∈ tracePositions [.arg] (Marked.contract b1 a1) := by decide
example : [.fn] ∈ tracePositions [] (Marked.contract b0 a0) ∧
    [.arg] ∈ tracePositions [] (Marked.contract b0 a0) := by decide
#print axioms tagsAt_markAllAt
#print axioms headVariable_markAllAt
#print axioms EveryApplicationTagged.redex_tag
#print axioms History.everyApplicationTagged
#print axioms TagSubset.of_trace
#print axioms History.trace_inclusion
end Lamping.Checks.ApplicationIdentity

#print axioms Lamping.Lambda.argument_lift_exists
#print axioms Lamping.Lambda.argument_copy
#print axioms Lamping.Lambda.history_diamond
#print axioms Lamping.Lambda.ParallelStep.endpoint_selection

namespace Lamping.Checks.ContextualResiduals
open Lambda
open Lamping.Checks.Families
private def beta : BetaAt (.lam initial) [.body] (.lam A) :=
  ⟨.var 0, A, rfl, rfl⟩
private def H : Derivation (.lam initial) (.lam A) := (singleContraction beta).derivation
private def R : RedexOcc (.lam initial) := ⟨[.body, .arg], by decide⟩
private def S : RedexOcc (.lam A) := ⟨[.body], by decide⟩
example : H.Residual R S ↔ outer.Residual oldInner afterRoot :=
  outer.prefix_residual_iff H (pre := [.body]) rfl rfl oldInner afterRoot R S rfl rfl
example : [.body] ∈ (singleContraction beta).residualSet [[.body, .arg]] := by
  apply ((singleContraction beta).residualSet_prefix_iff outerParallel
    (pre := [.body]) rfl rfl (q := []) (r := [.arg])).mpr
  decide
example : [.arg] ∉ (singleContraction beta).residualSet [[.body, .arg]] := by
  intro h
  obtain ⟨q, hq⟩ := (singleContraction beta).residualSet_has_prefix
    (pre := [.body]) (ps := [[]]) rfl h
  cases hq
example : ∃ b, ∃ k : ParallelStep [[]] initial b,
    Term.lam A = Term.lam b ∧ (singleContraction beta).paths = k.paths.map (Step.body :: ·) :=
  ParallelStep.lam_scope (F := [[]]) (singleContraction beta)
#print axioms Marked.ReductionAt.prefix_reflect
#print axioms Marked.History.prefix_trace_iff
#print axioms Derivation.prefix_residual_iff
#print axioms ParallelStep.residualSet_prefix_members
#print axioms ParallelStep.app_left_scope
#print axioms ParallelStep.app_right_scope
#print axioms ParallelStep.lam_scope
end Lamping.Checks.ContextualResiduals

namespace Lamping.Checks.GeneralCreationSeparation
open Lambda
private def I : Term := .lam (.var 0)
private def A : Term := .app I (.var 0)
private def start : Term := .lam (.app I (.app I A))
private def middle : Term := .lam (.app I A)
private def finish : Term := .lam A
private def R : BetaAt start [.body] middle := ⟨.var 0, .app I A, rfl, rfl⟩
private def S : BetaAt start [.body, .arg] middle := ⟨.var 0, A, rfl, rfl⟩
private def step : BetaAt middle [.body] finish := ⟨.var 0, A, rfl, rfl⟩
private def afterR : ParallelStep ((singleContraction R).residualSet [[.body, .arg]]) middle finish := by
  change ParallelStep [[.body]] middle finish
  exact singleContraction step
private def afterS : ParallelStep ((singleContraction S).residualSet [[.body]]) middle finish := by
  change ParallelStep [[.body]] middle finish
  exact singleContraction step
private def T1 : RedexOcc middle := ⟨[.body, .arg], by decide⟩
private def T : RedexOcc finish := ⟨[.body], by decide⟩
private theorem h1 : afterR.derivation.Residual T1 T := by
  rw [ParallelStep.residual_iff]
  decide
private theorem h2 : afterS.derivation.Residual T1 T := by
  rw [ParallelStep.residual_iff]
  decide
example : ∃ T0 : RedexOcc start,
    ((singleContraction R).derivation.append afterR.derivation).Residual T0 T :=
  creation_separation R S (by decide) afterR afterS T1 T1 T h1 h2
#print axioms creation_separation_outside_prefix
#print axioms SyntaxFrame.creation_separation
#print axioms creation_separation_at
#print axioms creation_separation
end Lamping.Checks.GeneralCreationSeparation

namespace Lamping.Checks.CreationOutsideContext
open Lambda
private def I : Term := .lam (.var 0)
private def A : Term := .app I (.var 0)
private def start : Term := .app (.lam (.app A A)) (.var 0)
private def left : Term := .app (.lam (.app (.var 0) A)) (.var 0)
private def right : Term := .app (.lam (.app A (.var 0))) (.var 0)
private def finish : Term := .app (.lam (.app (.var 0) (.var 0))) (.var 0)
private def R : BetaAt start [.fn, .body, .fn] left := ⟨.var 0, .var 0, rfl, rfl⟩
private def S : BetaAt start [.fn, .body, .arg] right := ⟨.var 0, .var 0, rfl, rfl⟩
private def a : BetaAt left [.fn, .body, .arg] finish := ⟨.var 0, .var 0, rfl, rfl⟩
private def b : BetaAt right [.fn, .body, .fn] finish := ⟨.var 0, .var 0, rfl, rfl⟩
private def afterR : ParallelStep ((singleContraction R).residualSet [[.fn, .body, .arg]]) left finish := by
  change ParallelStep [[.fn, .body, .arg]] left finish
  exact singleContraction a
private def afterS : ParallelStep ((singleContraction S).residualSet [[.fn, .body, .fn]]) right finish := by
  change ParallelStep [[.fn, .body, .fn]] right finish
  exact singleContraction b
private def T1 : RedexOcc left := ⟨[], by decide⟩
private def T2 : RedexOcc right := ⟨[], by decide⟩
private def T : RedexOcc finish := ⟨[], by decide⟩
example : ∃ T0 : RedexOcc start,
    ((singleContraction R).derivation.append afterR.derivation).Residual T0 T := by
  apply creation_separation R S (by decide) afterR afterS T1 T2 T
  · rw [ParallelStep.residual_iff]; decide
  · rw [ParallelStep.residual_iff]; decide
end Lamping.Checks.CreationOutsideContext

namespace Lamping.Checks.FunctionProjection
open Lambda
private def I : Term := .lam (.var 0)
private def A : Term := .app I (.var 0)
private def body : Term := .app I A
private def start : Term := .app (.lam body) (.var 0)
private def middle : Term := .app (.lam A) (.var 0)
private def finish : Term := .app I (.var 0)
private def R : BetaAt start [] body := ⟨body, .var 0, rfl, rfl⟩
private def S : BetaAt start [.fn, .body] middle := ⟨.var 0, A, rfl, rfl⟩
private def T : BetaAt middle [.fn, .body] finish := ⟨.var 0, .var 0, rfl, rfl⟩
private def σ := ParallelHistory.cons (singleContraction S) (.single (singleContraction T))
private theorem atomic : Atomic σ := .cons S (.single T)
private theorem inside : Internal [.fn] σ := by
  intro q hq
  change q ∈ [[.fn, .body], [.fn, .body]] at hq
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hq
  subst q
  exact ⟨[.body], rfl⟩
example : ∃ w, ∃ F, ∃ projected : ParallelHistory body w,
    ∃ last : ParallelStep F finish w, Atomic projected ∧
      StepProjection (singleContraction R) σ projected last ∧ last.paths = [[]] := by
  obtain ⟨w, F, projected, last, ha, row⟩ := atomic.function_projection R inside
  exact ⟨w, F, projected, last, ha, row,
    (row.final_vertical_singleton inside (by rintro ⟨q, hq⟩; cases hq)).1⟩
example : (singleContraction R).residualSet [[.fn, .body]] = [[]] := by decide
#print axioms StepProjection.final_selection
#print axioms StepProjection.final_selection_outside_members
#print axioms StepProjection.final_vertical_singleton
#print axioms BetaAt.function_residualSet_singleton
#print axioms BetaAt.outside_residualSet_singleton
#print axioms creation_predecessor_pullback
#print axioms singleton_projection_row
#print axioms Atomic.function_projection
#print axioms Atomic.disjoint_projection
private def sb : BetaAt body [] A := ⟨.var 0, A, rfl, rfl⟩
private def tb : BetaAt A [] (.var 0) := ⟨.var 0, .var 0, rfl, rfl⟩
private def V : BetaAt body [.arg] A := ⟨.var 0, .var 0, rfl, rfl⟩
private def r1 : BetaAt middle [] A := ⟨A, .var 0, rfl, rfl⟩
private def r2 : BetaAt finish [] (.var 0) := ⟨.var 0, .var 0, rfl, rfl⟩
private def square1 : ParallelMovesSquare [[]] [[.fn, .body]] start body middle A where
  first := singleContraction R
  second := singleContraction S
  afterFirst := by change ParallelStep [[]] body A; exact singleContraction sb
  afterSecond := by change ParallelStep [[]] middle A; exact singleContraction r1
private def square2 : ParallelMovesSquare [[]] [[.fn, .body]] middle A finish (.var 0) where
  first := singleContraction r1
  second := singleContraction T
  afterFirst := by change ParallelStep [[]] A (.var 0); exact singleContraction tb
  afterSecond := by change ParallelStep [[]] finish (.var 0); exact singleContraction r2
private theorem row : StepProjection (singleContraction R) σ
    (.cons (singleContraction sb) (.single (singleContraction tb))) (singleContraction r2) :=
  .cons square1 (.cons square2 (.nil (singleContraction r2)))
private theorem oldPredecessor : (singleContraction sb).derivation.Residual
    ⟨[.arg], V.redex⟩ ⟨[], tb.redex⟩ := by
  rw [ParallelStep.residual_iff]
  decide
example : ExtractionJoin (.of σ atomic)
    (.of (.cons (singleContraction R) (.single (singleContraction V))) (.cons R (.single V))) :=
  extraction_function_residual_peak R sb tb S T row inside V oldPredecessor
#print axioms extraction_function_residual_peak
example : ∃ (mid : Term) (pre : ParallelHistory start mid) (post : ParallelHistory mid finish),
    Atomic pre ∧ Atomic post ∧ σ = pre.append post ∧ pre.length = 1 :=
  atomic.split_at 1 (by change 1 ≤ 2; omega)
example : ∃ bridge : ParallelHistory start middle, Atomic bridge ∧
    ParallelHistory.single (singleContraction S) = (ParallelHistory.nil start).append bridge ∧
    σ = bridge.append (.single (singleContraction T)) :=
  Atomic.prefix_comparable (.nil start) (.single S) atomic (.single T) rfl
    (by change 0 ≤ 1; omega)
#print axioms Atomic.split_at
#print axioms Atomic.prefix_alignment
#print axioms Atomic.prefix_comparable
#print axioms StepProjection.split_append
#print axioms ExtractionRun.ext_paths
example : ∃ (x : Term) (K : List Path) (pre : ParallelHistory start x)
    (post : ParallelHistory x finish) (vertical : ParallelStep K x A),
    Atomic pre ∧ Atomic post ∧ σ = pre.append post ∧
    StepProjection (singleContraction R) pre (.single (singleContraction sb)) vertical ∧
    StepProjection vertical post (.single (singleContraction tb)) (singleContraction r2) := by
  exact row.split_bottom (.single (singleContraction sb)) (.single (singleContraction tb))
    atomic (.single sb) (.single tb)
#print axioms Atomic.append_iff
#print axioms StepProjection.split_bottom
private def body3 : Term := .app I body
private def start3 : Term := .app (.lam body3) (.var 0)
private def R3 : BetaAt start3 [] body3 := ⟨body3, .var 0, rfl, rfl⟩
private def top3 : BetaAt start3 [.fn, .body] start := ⟨.var 0, body, rfl, rfl⟩
private def bottom3 : BetaAt body3 [] body := ⟨.var 0, body, rfl, rfl⟩
private def square3 : ParallelMovesSquare [[]] [[.fn, .body]] start3 body3 start body where
  first := singleContraction R3
  second := singleContraction top3
  afterFirst := by change ParallelStep [[]] body3 body; exact singleContraction bottom3
  afterSecond := by change ParallelStep [[]] start body; exact singleContraction R
private theorem row3 : StepProjection (singleContraction R3)
    (.cons (singleContraction top3) σ)
    (.cons (singleContraction bottom3) (.cons (singleContraction sb) (.single (singleContraction tb))))
    (singleContraction r2) := .cons square3 row
example : ExtractionJoin (.of (.cons (singleContraction top3) σ) (.cons top3 atomic))
    (.of (.cons (singleContraction R3)
      (.cons (singleContraction bottom3) (.single (singleContraction V))))
      (.cons R3 (.cons bottom3 (.single V)))) := by
  apply extraction_function_residual_long_peak R3 (.single (singleContraction bottom3))
    (.single bottom3) sb tb _ (.cons top3 atomic) row3 ?_ V oldPredecessor
  intro q hq
  change q ∈ [[.fn, .body], [.fn, .body], [.fn, .body]] at hq
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hq
  subst q
  exact ⟨[.body], rfl⟩
#print axioms function_residual_pullback
#print axioms extraction_function_residual_prefixed_peak
#print axioms extraction_function_residual_long_peak
private theorem oneRow : StepProjection (singleContraction R) (.single (singleContraction S))
    (.single (singleContraction sb)) (singleContraction r1) := .cons square1 (.nil (singleContraction r1))
private def localFunction : RootExtraction R (.of (.single (singleContraction sb)) (.single sb))
    (.of (.single (singleContraction S)) (.single S)) :=
  .functionPart _ (.single S) _ (.single sb) (singleContraction r1) oneRow (by decide)
    (by intro q hq; change q ∈ [[.fn, .body]] at hq; cases List.mem_singleton.mp hq; exact ⟨[.body], rfl⟩)
private def localResidual : RootExtraction R (.of (.single (singleContraction sb)) (.single sb))
    (.of (.single (singleContraction S)) (.single S)) :=
  .residual sb S (by rw [ParallelStep.residual_iff]; decide)
private def beforeStart : Term := .app I start
private def Q : BetaAt beforeStart [] start := ⟨.var 0, start, rfl, rfl⟩
private def indexedSource : ExtractionRun beforeStart := .of
  (.cons (singleContraction Q) (.cons (singleContraction R) (.single (singleContraction sb))))
  (.cons Q (.cons R (.single sb)))
private def indexedTarget : ExtractionRun beforeStart := .of
  (.cons (singleContraction Q) (.single (singleContraction S))) (.cons Q (.single S))
private theorem indexedFunction : ExtractionAt 1 indexedSource indexedTarget :=
  ⟨_,_,_,.single (singleContraction Q),.single Q,R,_,_,localFunction,rfl,rfl,rfl⟩
private theorem indexedResidual : ExtractionAt 1 indexedSource indexedTarget :=
  ⟨_,_,_,.single (singleContraction Q),.single Q,R,_,_,localResidual,rfl,rfl,rfl⟩
example : ExtractionJoin indexedTarget indexedTarget := indexedFunction.peak_join indexedResidual
example : ExtractionStep indexedSource indexedTarget := indexedFunction.step
example : ∃ result : ExtractionRun start,
    ExtractionAt 0 (.of (.cons (singleContraction R) (.single (singleContraction sb)))
      (.cons R (.single sb))) result ∧
    indexedTarget = result.prepend (.single (singleContraction Q)) (.single Q) :=
  indexedFunction.uncons Q (.of (.cons (singleContraction R) (.single (singleContraction sb)))
    (.cons R (.single sb)))
example : ∃ result : ExtractionRun start,
    ExtractionAt 0 (.of (.cons (singleContraction R) (.single (singleContraction sb)))
      (.cons R (.single sb))) result ∧
    indexedTarget = result.prepend (.single (singleContraction Q)) (.single Q) :=
  ExtractionAt.strip_prefix (.single (singleContraction Q)) (.single Q)
    (.of (.cons (singleContraction R) (.single (singleContraction sb))) (.cons R (.single sb)))
    indexedResidual
#print axioms RootExtraction.target_unique
#print axioms ExtractionStep.root_factor
#print axioms RootExtraction.same_index_target_unique
#print axioms ExtractionStep.indexed_iff
#print axioms ExtractionAt.target_unique
#print axioms ExtractionAt.uncons
#print axioms ExtractionAt.strip_prefix
#print axioms ExtractionAt.strict_fork_factor
#print axioms RootExtraction.residual_tail_join
end Lamping.Checks.FunctionProjection

namespace Lamping.Checks.ExtractionInternal
open Lambda
private def I : Term := .lam (.var 0)
private def A : Term := .app I (.var 0)
private def start : Term := .lam (.app I A)
private def R : BetaAt start [.body] (.lam A) := ⟨.var 0, A, rfl, rfl⟩
private def S : BetaAt (.lam A) [.body] (.lam (.var 0)) := ⟨.var 0, .var 0, rfl, rfl⟩
private def S' : BetaAt start [.body, .arg] (.lam A) := ⟨.var 0, .var 0, rfl, rfl⟩
private def before : ExtractionRun start := .of
  (.cons (singleContraction R) (.single (singleContraction S))) (.cons R (.single S))
private def after : ExtractionRun start := .of (.single (singleContraction S')) (.single S')
private theorem step : ExtractionStep before after := by
  apply ExtractionStep.residual (.nil start) (.nil start) R S S'
  rw [ParallelStep.residual_iff]
  decide
example : Internal [.body] after.history := by
  apply step.internal
  intro q hq
  change q ∈ [[.body], [.body]] at hq
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hq
  subst q
  exact ⟨[], rfl⟩
example : ¬ Internal [.fn] after.history := by
  intro h
  obtain ⟨q, hq⟩ := h [.body, .arg] (by change ([.body, .arg] : Path) ∈ [[.body, .arg]]; simp)
  cases hq
#print axioms StepProjection.internal_reflect
#print axioms ExtractionStep.internal
#print axioms Extraction.internal
end Lamping.Checks.ExtractionInternal

namespace Lamping.Checks.RenameResiduals
open Lambda
private def I : Term := .lam (.var 0)
private def inner : Term := .app I (.var 2)
private def start : Term := .app I inner
private def R : BetaAt start [] inner := ⟨.var 0, inner, rfl, rfl⟩
private def collapse : Nat → Nat := fun _ => 0
private def old : RedexOcc start := ⟨[.arg], by decide⟩
private def output : RedexOcc inner := ⟨[], by decide⟩
private def renamedOld : RedexOcc (rename collapse start) := ⟨[.arg], by decide⟩
private def renamedOutput : RedexOcc (rename collapse inner) := ⟨[], by decide⟩
example : (singleContraction (R.rename collapse)).derivation.Residual renamedOld renamedOutput := by
  apply ((singleContraction R).derivation.rename_residual_iff
    (singleContraction (R.rename collapse)).derivation rfl old output renamedOld renamedOutput rfl rfl).mpr
  rw [ParallelStep.residual_iff]
  decide
example : ¬ Function.Injective collapse := by
  intro h
  have impossible : (0 : Nat) = 1 := h rfl
  omega
#print axioms Marked.markAt_rename
#print axioms Marked.History.rename
#print axioms Derivation.rename_residual_iff
end Lamping.Checks.RenameResiduals

namespace Lamping.Checks.ArgumentLongTail
open Lambda
private def I : Term := .lam (.var 0)
private def A : Term := .app I (.var 0)
private def B : Term := .app I A
private def C : Term := .app I B
private def dup : Term := .lam (.app (.var 0) (.var 0))
private def start : Term := .app dup C
private def R : BetaAt start [] (.app C C) := ⟨.app (.var 0) (.var 0), C, rfl, rfl⟩
private def P : BetaAt (.app C C) [.fn] (.app B C) := ⟨.var 0, B, rfl, rfl⟩
private def S : BetaAt (.app B C) [.fn] (.app A C) := ⟨.var 0, A, rfl, rfl⟩
private def T : BetaAt (.app A C) [.fn] (.app (.var 0) C) := ⟨.var 0, .var 0, rfl, rfl⟩
private def V : BetaAt (.app B C) [.fn, .arg] (.app A C) := ⟨.var 0, .var 0, rfl, rfl⟩
private def P' : BetaAt start [.arg] (.app dup B) := ⟨.var 0, B, rfl, rfl⟩
private def S' : BetaAt (.app dup B) [.arg] (.app dup A) := ⟨.var 0, A, rfl, rfl⟩
private def T' : BetaAt (.app dup A) [.arg] (.app dup (.var 0)) := ⟨.var 0, .var 0, rfl, rfl⟩
private def original := ParallelHistory.cons (singleContraction P')
  (.cons (singleContraction S') (.single (singleContraction T')))
private theorem ordinary : Atomic original := .cons P' (.cons S' (.single T'))
private def copied := ParallelHistory.cons (singleContraction P)
  (.cons (singleContraction S) (.single (singleContraction T)))
private def lift : ArgumentLift R copied original where
  body := .app (.var 0) (.var 0)
  argument := C
  redex := rfl
  occurrence := [.fn]
  isVariable := rfl
  localPaths := [[], [], []]
  copy_paths := rfl
  original_paths := rfl
  parallelization := StepProjection.exists_projection (singleContraction R) original
example : ExtractionJoin (.of original ordinary)
    (.of (.cons (singleContraction R)
      (.cons (singleContraction P) (.single (singleContraction V))))
      (.cons R (.cons P (.single V)))) := by
  apply extraction_argument_residual_long_peak R (.single (singleContraction P)) (.single P)
    S T original ordinary lift V
  rw [ParallelStep.residual_iff]
  decide
private def deep : BetaAt start [.arg,.arg,.arg] (.app dup B) := ⟨.var 0,.var 0,rfl,rfl⟩
private def ancestor : RedexWithHistory start := ⟨start,.nil _,⟨[.arg,.arg,.arg],deep.redex⟩⟩
private def current : RedexWithHistory start :=
  ⟨.app A C,.cons (singleContraction R) (.cons (singleContraction P) (.single (singleContraction S))),⟨[.fn],T.redex⟩⟩
private theorem ancestorCanonical : CanonicalRun (.of (.single (singleContraction deep)) (.single deep)) :=
  ⟨by change 0<1; omega,
    Standard.single_step _ ⟨_,deep.redex⟩ (leftmost_singleton _),extraction_single_normal deep⟩
private theorem family : FamilyEq ancestor current := by
  apply initial_family_iff _ current |>.mpr
  let r0 : RedexOcc start := ⟨[.arg,.arg,.arg],deep.redex⟩
  let r1 : RedexOcc (.app C C) := ⟨[.fn,.arg,.arg],by decide⟩
  let r2 : RedexOcc (.app B C) := ⟨[.fn,.arg],by decide⟩
  let r3 : RedexOcc (.app A C) := ⟨[.fn],T.redex⟩
  have hr : (singleContraction R).derivation.Residual r0 r1 := by rw [ParallelStep.residual_iff]; decide
  have hp : (singleContraction P).derivation.Residual r1 r2 := by rw [ParallelStep.residual_iff]; decide
  have hs : (singleContraction S).derivation.Residual r2 r3 := by rw [ParallelStep.residual_iff]; decide
  exact (Derivation.residual_append _ _ r0 r3).mpr
    ⟨r1,hr,(Derivation.residual_append _ _ r1 r3).mpr ⟨r2,hp,hs⟩⟩
example : Copy ancestor current :=
  (canonical_copy_iff_history_prefix ancestorCanonical ⟨deep,.nil _,rfl⟩ family).mpr
    ⟨current.history,.refl _⟩
#print axioms Derivation.region_rename_target
#print axioms Derivation.region_rename_residual_iff
#print axioms ArgumentLift.split_prefix
#print axioms extraction_argument_residual_long_peak
example : ExtractionJoin (.of original ordinary)
    (.of (.cons (singleContraction R)
      (.cons (singleContraction P) (.single (singleContraction V))))
      (.cons R (.cons P (.single V)))) := by
  apply argument_tail_peak R copied (.cons P (.cons S (.single T))) original ordinary lift
    (result := .of (.cons (singleContraction P) (.single (singleContraction V))) (.cons P (.single V)))
  apply ExtractionStep.residual (.single (singleContraction P)) (.single P) S T V
  rw [ParallelStep.residual_iff]
  decide
end Lamping.Checks.ArgumentLongTail

namespace Lamping.Checks.ProjectionRowUniqueness
open Lambda
private def I : Term := .lam (.var 0)
private def A : Term := .app I (.var 0)
private def start : Term := .app (.app A A) A
private def target : Term := .app (.app (.var 0) (.var 0)) A
private def finish : Term := .app (.app (.var 0) (.var 0)) (.var 0)
private def selected : List Path := [[.fn, .fn], [.fn, .arg]]
private def annotation : Marked := .app [] (.app [] (.var 0) (.var 0))
  (.app [[.arg]] (.lam (.var 0)) (.var 0))
private def first : ParallelStep selected start target where
  paths := [[.fn, .fn], [.fn, .arg]]
  markedTarget := annotation
  complete := (Marked.completeOld_iff selected start).mpr
    ⟨.cons (.appL (.appL (.root _ _ _)))
      (.cons (.appL (.appR (.root _ _ _))) (.nil _)), by trivial⟩
  target_eq := rfl
private def second : ParallelStep selected start target where
  paths := [[.fn, .arg], [.fn, .fn]]
  markedTarget := annotation
  complete := (Marked.completeOld_iff selected start).mpr
    ⟨.cons (.appL (.appR (.root _ _ _)))
      (.cons (.appL (.appL (.root _ _ _))) (.nil _)), by trivial⟩
  target_eq := rfl
private def top : BetaAt start [.arg] (.app (.app A A) (.var 0)) := ⟨.var 0, .var 0, rfl, rfl⟩
private def bottom : BetaAt target [.arg] finish := ⟨.var 0, .var 0, rfl, rfl⟩
private def lastAnnotation : Marked := .app [] (.app [] (.var 0) (.var 0)) (.var 0)
private def afterTop : ParallelStep selected (.app (.app A A) (.var 0)) finish where
  paths := [[.fn, .fn], [.fn, .arg]]
  markedTarget := lastAnnotation
  complete := (Marked.completeOld_iff selected _).mpr
    ⟨.cons (.appL (.appL (.root _ _ _)))
      (.cons (.appL (.appR (.root _ _ _))) (.nil _)), by trivial⟩
  target_eq := rfl
private def afterTop' : ParallelStep selected (.app (.app A A) (.var 0)) finish where
  paths := [[.fn, .arg], [.fn, .fn]]
  markedTarget := lastAnnotation
  complete := (Marked.completeOld_iff selected _).mpr
    ⟨.cons (.appL (.appR (.root _ _ _)))
      (.cons (.appL (.appL (.root _ _ _))) (.nil _)), by trivial⟩
  target_eq := rfl
private def square : ParallelMovesSquare selected [[.arg]] start target (.app (.app A A) (.var 0)) finish where
  first := first
  second := singleContraction top
  afterFirst := by change ParallelStep [[.arg]] target finish; exact singleContraction bottom
  afterSecond := by change ParallelStep selected _ finish; exact afterTop
private def square' : ParallelMovesSquare selected [[.arg]] start target (.app (.app A A) (.var 0)) finish where
  first := second
  second := singleContraction top
  afterFirst := by change ParallelStep [[.arg]] target finish; exact singleContraction bottom
  afterSecond := by change ParallelStep selected _ finish; exact afterTop'
private theorem row : StepProjection first (.single (singleContraction top))
    (.single (singleContraction bottom)) afterTop := .cons square (.nil afterTop)
private theorem row' : StepProjection second (.single (singleContraction top))
    (.single (singleContraction bottom)) afterTop' := .cons square' (.nil afterTop')
example : first.paths ≠ second.paths := by decide
example : ExtractionRun.of (.single (singleContraction top)) (.single top) =
    ExtractionRun.of (.single (singleContraction top)) (.single top) :=
  row.atomic_top_run_unique row' (.single top) (.single top) (.single bottom)
#print axioms StepProjection.atomic_top_paths_unique
#print axioms StepProjection.atomic_top_run_unique
end Lamping.Checks.ProjectionRowUniqueness

namespace Lamping.Checks.ExtractionRename
open Lambda
private def I : Term := .lam (.var 0)
private def A : Term := .app I (.var 1)
private def start : Term := .lam (.app (.lam (.lam (.var 1))) A)
private def copied : Term := .lam (.lam (.app I (.var 2)))
private def R : BetaAt start [.body] copied := ⟨.lam (.var 1), A, rfl, rfl⟩
private def S : BetaAt copied [.body,.body] (.lam (.lam (.var 2))) := ⟨.var 0,.var 2,rfl,rfl⟩
private def original : Term := .lam (.app (.lam (.lam (.var 1))) (.var 1))
private def A' : BetaAt start [.body,.arg] original := ⟨.var 0,.var 1,rfl,rfl⟩
private def lift : ArgumentLift R (.single (singleContraction S)) (.single (singleContraction A')) where
  body := .lam (.var 1)
  argument := A
  redex := rfl
  occurrence := [.body]
  isVariable := rfl
  localPaths := [[]]
  copy_paths := rfl
  original_paths := rfl
  parallelization := StepProjection.exists_projection (singleContraction R) (.single (singleContraction A'))
example : subtermAt (rename (fun _ => 7) start) [.body,.arg,.arg] = some (.var 8) := rfl
example : subtermAt (rename (fun _ => 7) copied) [.body,.body,.arg] = some (.var 9) := rfl
example : ArgumentOccurrence (lift.rename (fun _ => 7)).body (lift.rename (fun _ => 7)).occurrence :=
  (lift.rename (fun _ => 7)).isVariable
example : ExtractionStep
    ((ExtractionRun.of (.cons (singleContraction R) (.single (singleContraction S)))
      (.cons R (.single S))).rename (fun _ => 7))
    ((ExtractionRun.of (.single (singleContraction A')) (.single A')).rename (fun _ => 7)) :=
  (ExtractionStep.argumentPart (.nil _) (.nil _) R _ (.single S) _ (.single A') (by decide) lift).rename (fun _ => 7)
#print axioms ParallelStep.rename
#print axioms StepProjection.rename
#print axioms ArgumentOccurrence.rename
#print axioms ArgumentLift.rename
#print axioms ExtractionStep.rename
#print axioms Extraction.rename
end Lamping.Checks.ExtractionRename

namespace Lamping.Checks.FunctionDisjointRegion
open Lambda
private def I : Term := .lam (.var 0)
private def A : Term := .app I (.var 0)
private def body : Term := .app A A
private def start : Term := .app (.lam body) (.var 0)
private def middle : Term := .app (.lam (.app (.var 0) A)) (.var 0)
private def finish : Term := .app (.lam (.app (.var 0) (.var 0))) (.var 0)
private def R : BetaAt start [] body := ⟨body,.var 0,rfl,rfl⟩
private def S : BetaAt body [.fn] (.app (.var 0) A) := ⟨.var 0,.var 0,rfl,rfl⟩
private def T : BetaAt (.app (.var 0) A) [.arg] (.app (.var 0) (.var 0)) := ⟨.var 0,.var 0,rfl,rfl⟩
private def S' : BetaAt start [.fn,.body,.fn] middle := ⟨.var 0,.var 0,rfl,rfl⟩
private def T' : BetaAt middle [.fn,.body,.arg] finish := ⟨.var 0,.var 0,rfl,rfl⟩
private def R1 : BetaAt middle [] (.app (.var 0) A) := ⟨.app (.var 0) A,.var 0,rfl,rfl⟩
private def R2 : BetaAt finish [] (.app (.var 0) (.var 0)) := ⟨.app (.var 0) (.var 0),.var 0,rfl,rfl⟩
private def V : BetaAt body [.arg] (.app A (.var 0)) := ⟨.var 0,.var 0,rfl,rfl⟩
private def sq1 : ParallelMovesSquare [[]] [[.fn,.body,.fn]] start body middle (.app (.var 0) A) :=
  ⟨singleContraction R,singleContraction S',by change ParallelStep [[.fn]] _ _; exact singleContraction S,
    by change ParallelStep [[]] _ _; exact singleContraction R1⟩
private def sq2 : ParallelMovesSquare [[]] [[.fn,.body,.arg]] middle (.app (.var 0) A) finish (.app (.var 0) (.var 0)) :=
  ⟨singleContraction R1,singleContraction T',by change ParallelStep [[.arg]] _ _; exact singleContraction T,
    by change ParallelStep [[]] _ _; exact singleContraction R2⟩
private theorem row : StepProjection (singleContraction R)
    (.cons (singleContraction S') (.single (singleContraction T')))
    (.cons (singleContraction S) (.single (singleContraction T))) (singleContraction R2) :=
  .cons sq1 (.cons sq2 (.nil (singleContraction R2)))
example : ExtractionJoin
    (.of (.cons (singleContraction S') (.single (singleContraction T'))) (.cons S' (.single T')))
    (.of (.cons (singleContraction R) (.single (singleContraction V))) (.cons R (.single V))) := by
  apply extraction_function_region_peak R S T S' T' row ?_ V ?_
    (.inl (by constructor <;> rintro ⟨q,hq⟩ <;> cases hq))
  · intro q hq
    change q ∈ [[.fn,.body,.fn],[.fn,.body,.arg]] at hq
    rcases List.mem_cons.mp hq with he | he
    · cases he; exact ⟨[.body,.fn],rfl⟩
    · cases List.mem_singleton.mp he; exact ⟨[.body,.arg],rfl⟩
  · rw [ParallelStep.residual_iff]; decide
#print axioms BetaAt.function_residual_coordinates
#print axioms BetaAt.function_disjoint_reflect
#print axioms BetaAt.function_internal_reflect
#print axioms extraction_function_region_peak
end Lamping.Checks.FunctionDisjointRegion

namespace Lamping.Checks.FunctionFunctionRegion
open Lambda
private def I : Term := .lam (.var 0)
private def A : Term := .app I (.var 0)
private def body : Term := .app (.lam (.app I (.var 0))) (.var 0)
private def start : Term := .app (.lam body) (.var 0)
private def middle : Term := .app (.lam A) (.var 0)
private def finish : Term := .app I (.var 0)
private def R : BetaAt start [] body := ⟨body,.var 0,rfl,rfl⟩
private def S : BetaAt body [] A := ⟨.app I (.var 0),.var 0,rfl,rfl⟩
private def T : BetaAt A [] (.var 0) := ⟨.var 0,.var 0,rfl,rfl⟩
private def S' : BetaAt start [.fn,.body] middle := ⟨.app I (.var 0),.var 0,rfl,rfl⟩
private def T' : BetaAt middle [.fn,.body] finish := ⟨.var 0,.var 0,rfl,rfl⟩
private def R1 : BetaAt middle [] A := ⟨A,.var 0,rfl,rfl⟩
private def R2 : BetaAt finish [] (.var 0) := ⟨.var 0,.var 0,rfl,rfl⟩
private def V : BetaAt body [.fn,.body] A := ⟨.var 0,.var 0,rfl,rfl⟩
private def sq1 : ParallelMovesSquare [[]] [[.fn,.body]] start body middle A :=
  ⟨singleContraction R,singleContraction S',by change ParallelStep [[]] _ _; exact singleContraction S,
    by change ParallelStep [[]] _ _; exact singleContraction R1⟩
private def sq2 : ParallelMovesSquare [[]] [[.fn,.body]] middle A finish (.var 0) :=
  ⟨singleContraction R1,singleContraction T',by change ParallelStep [[]] _ _; exact singleContraction T,
    by change ParallelStep [[]] _ _; exact singleContraction R2⟩
private theorem row : StepProjection (singleContraction R)
    (.cons (singleContraction S') (.single (singleContraction T')))
    (.cons (singleContraction S) (.single (singleContraction T))) (singleContraction R2) :=
  .cons sq1 (.cons sq2 (.nil (singleContraction R2)))
example : ExtractionJoin
    (.of (.cons (singleContraction S') (.single (singleContraction T'))) (.cons S' (.single T')))
    (.of (.cons (singleContraction R) (.single (singleContraction V))) (.cons R (.single V))) := by
  apply extraction_function_region_peak R S T S' T' row ?_ V ?_ (.inr ⟨[.body],rfl⟩)
  · intro q hq
    change q ∈ [[.fn,.body],[.fn,.body]] at hq
    simp only [List.mem_cons,List.not_mem_nil,or_false,or_self] at hq
    subst q
    exact ⟨[.body],rfl⟩
  · rw [ParallelStep.residual_iff]; decide
end Lamping.Checks.FunctionFunctionRegion

namespace Lamping.Checks.SingletonCube
open Lambda
private def I : Term := .lam (.var 0)
private def A : Term := .app I (.var 0)
private def start : Term := .app (.app A A) A
private def u : Term := .app (.app (.var 0) A) A
private def v : Term := .app (.app A (.var 0)) A
private def z : Term := .app (.app A A) (.var 0)
private def x : Term := .app (.app (.var 0) A) (.var 0)
private def y : Term := .app (.app A (.var 0)) (.var 0)
private def finish : Term := .app (.app (.var 0) (.var 0)) (.var 0)
private def R : BetaAt start [.fn,.fn] u := ⟨.var 0,.var 0,rfl,rfl⟩
private def S : BetaAt start [.fn,.arg] v := ⟨.var 0,.var 0,rfl,rfl⟩
private def C : BetaAt start [.arg] z := ⟨.var 0,.var 0,rfl,rfl⟩
private def C_R : BetaAt u [.arg] x := ⟨.var 0,.var 0,rfl,rfl⟩
private def R_C : BetaAt z [.fn,.fn] x := ⟨.var 0,.var 0,rfl,rfl⟩
private def C_S : BetaAt v [.arg] y := ⟨.var 0,.var 0,rfl,rfl⟩
private def S_C : BetaAt z [.fn,.arg] y := ⟨.var 0,.var 0,rfl,rfl⟩
private def S_RC : BetaAt x [.fn,.arg] finish := ⟨.var 0,.var 0,rfl,rfl⟩
private def R_SC : BetaAt y [.fn,.fn] finish := ⟨.var 0,.var 0,rfl,rfl⟩
private def back := singleton_cube_back R S C ⟨[.fn,.arg],by decide⟩ ⟨[.fn,.fn],by decide⟩
  C_R R_C C_S S_C S_RC R_SC (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide)
example : back.first.paths = [[.fn,.fn]] := rfl
example : back.second.paths = [[.fn,.arg]] := rfl
example : back.afterFirst.paths = [[.fn,.arg]] := rfl
example : back.afterSecond.paths = [[.fn,.fn]] := rfl
#print axioms ParallelMovesSquare.singleton_residualSet
#print axioms singleton_cube_back
end Lamping.Checks.SingletonCube

namespace Lamping.Checks.FunctionRegionLong
open Lambda
private def I : Term := .lam (.var 0)
private def A : Term := .app I (.var 0)
private def body : Term := .app A (.app A A)
private def start : Term := .app (.lam body) (.var 0)
private def w0 : Term := .app (.var 0) (.app A A)
private def w1 : Term := .app (.var 0) (.app (.var 0) A)
private def w2 : Term := .app (.var 0) (.app (.var 0) (.var 0))
private def v0 : Term := .app (.lam w0) (.var 0)
private def v1 : Term := .app (.lam w1) (.var 0)
private def v2 : Term := .app (.lam w2) (.var 0)
private def x1 : Term := .app A (.app (.var 0) A)
private def x2 : Term := .app A (.app (.var 0) (.var 0))
private def R : BetaAt start [] body := ⟨body,.var 0,rfl,rfl⟩
private def S : BetaAt body [.fn] w0 := ⟨.var 0,.var 0,rfl,rfl⟩
private def B1 : BetaAt w0 [.arg,.fn] w1 := ⟨.var 0,.var 0,rfl,rfl⟩
private def B2 : BetaAt w1 [.arg,.arg] w2 := ⟨.var 0,.var 0,rfl,rfl⟩
private def S' : BetaAt start [.fn,.body,.fn] v0 := ⟨.var 0,.var 0,rfl,rfl⟩
private def A1 : BetaAt v0 [.fn,.body,.arg,.fn] v1 := ⟨.var 0,.var 0,rfl,rfl⟩
private def A2 : BetaAt v1 [.fn,.body,.arg,.arg] v2 := ⟨.var 0,.var 0,rfl,rfl⟩
private def R0 : BetaAt v0 [] w0 := ⟨w0,.var 0,rfl,rfl⟩
private def R1 : BetaAt v1 [] w1 := ⟨w1,.var 0,rfl,rfl⟩
private def R2 : BetaAt v2 [] w2 := ⟨w2,.var 0,rfl,rfl⟩
private def V1 : BetaAt body [.arg,.fn] x1 := ⟨.var 0,.var 0,rfl,rfl⟩
private def V2 : BetaAt x1 [.arg,.arg] x2 := ⟨.var 0,.var 0,rfl,rfl⟩
private def S1 : BetaAt x1 [.fn] w1 := ⟨.var 0,.var 0,rfl,rfl⟩
private def S2 : BetaAt x2 [.fn] w2 := ⟨.var 0,.var 0,rfl,rfl⟩
private def whole : ParallelHistory start v2 :=
  .cons (singleContraction S') (.cons (singleContraction A1) (.single (singleContraction A2)))
private def middle : ParallelHistory w0 w2 :=
  .cons (singleContraction B1) (.single (singleContraction B2))
private def lower : ParallelHistory body x2 :=
  .cons (singleContraction V1) (.single (singleContraction V2))
private theorem outerRow : StepProjection (singleContraction R) whole
    (.cons (singleContraction S) middle) (singleContraction R2) := by
  let sq0 : ParallelMovesSquare [[]] [[.fn,.body,.fn]] start body v0 w0 :=
    ⟨singleContraction R,singleContraction S',by change ParallelStep [[.fn]] _ _; exact singleContraction S,
      by change ParallelStep [[]] _ _; exact singleContraction R0⟩
  let sq1 : ParallelMovesSquare [[]] [[.fn,.body,.arg,.fn]] v0 w0 v1 w1 :=
    ⟨singleContraction R0,singleContraction A1,by change ParallelStep [[.arg,.fn]] _ _; exact singleContraction B1,
      by change ParallelStep [[]] _ _; exact singleContraction R1⟩
  let sq2 : ParallelMovesSquare [[]] [[.fn,.body,.arg,.arg]] v1 w1 v2 w2 :=
    ⟨singleContraction R1,singleContraction A2,by change ParallelStep [[.arg,.arg]] _ _; exact singleContraction B2,
      by change ParallelStep [[]] _ _; exact singleContraction R2⟩
  exact .cons sq0 (.cons sq1 (.cons sq2 (.nil _)))
private theorem lowerRow : StepProjection (singleContraction S) lower middle (singleContraction S2) := by
  let sq1 : ParallelMovesSquare [[.fn]] [[.arg,.fn]] body w0 x1 w1 :=
    ⟨singleContraction S,singleContraction V1,by change ParallelStep [[.arg,.fn]] _ _; exact singleContraction B1,
      by change ParallelStep [[.fn]] _ _; exact singleContraction S1⟩
  let sq2 : ParallelMovesSquare [[.fn]] [[.arg,.arg]] x1 w1 x2 w2 :=
    ⟨singleContraction S1,singleContraction V2,by change ParallelStep [[.arg,.arg]] _ _; exact singleContraction B2,
      by change ParallelStep [[.fn]] _ _; exact singleContraction S2⟩
  exact .cons sq1 (.cons sq2 (.nil _))
example : ExtractionJoin
    (.of whole (.cons S' (.cons A1 (.single A2))))
    (.of (.cons (singleContraction R) lower) (.cons R (.cons V1 (.single V2)))) := by
  have hw : Internal [.fn] whole := by
    intro name hq
    change name∈[[.fn,.body,.fn],[.fn,.body,.arg,.fn],[.fn,.body,.arg,.arg]] at hq
    rcases List.mem_cons.mp hq with he | he
    · cases he; exact ⟨[.body,.fn],rfl⟩
    · rcases List.mem_cons.mp he with he | he
      · cases he; exact ⟨[.body,.arg,.fn],rfl⟩
      · cases List.mem_singleton.mp he; exact ⟨[.body,.arg,.arg],rfl⟩
  have hl : Internal [.arg] lower := by
    intro name hq
    change name∈[[.arg,.fn],[.arg,.arg]] at hq
    rcases List.mem_cons.mp hq with he | he
    · cases he; exact ⟨[.fn],rfl⟩
    · cases List.mem_singleton.mp he; exact ⟨[.arg],rfl⟩
  exact extraction_function_region_long_peak R (.nil body) (.nil body) S middle
    (.cons B1 (.single B2)) whole (.cons S' (.cons A1 (.single A2))) outerRow hw
    lower (.cons V1 (.single V2)) lowerRow (by change 0<2; omega)
    (.inl (by constructor <;> rintro ⟨q,hq⟩ <;> cases hq)) hl
#print axioms ParallelStep.eq_of_paths
#print axioms StepProjection.region_head
#print axioms function_region_pullback_tile
#print axioms function_region_pullback
#print axioms function_region_site
#print axioms extraction_function_region_long_peak
private theorem disjointStep : ExtractionStep
    (.of (.cons (singleContraction S) middle) (.cons S (.cons B1 (.single B2))))
    (.of lower (.cons V1 (.single V2))) :=
  ExtractionStep.disjoint (.nil _) (.nil _) S lower (.cons V1 (.single V2))
    middle (.cons B1 (.single B2)) (singleContraction S2) lowerRow (by change 0<2; omega)
    [.arg] (by constructor <;> rintro ⟨q,hq⟩ <;> cases hq)
    (by intro q hq; change q∈[[.arg,.fn],[.arg,.arg]] at hq
        rcases List.mem_cons.mp hq with he | he
        · cases he; exact ⟨[.fn],rfl⟩
        · cases List.mem_singleton.mp he; exact ⟨[.arg],rfl⟩)
example : ExtractionStep
    ((ExtractionRun.of (.cons (singleContraction S) middle) (.cons S (.cons B1 (.single B2)))).subst (fun _ => A))
    ((ExtractionRun.of lower (.cons V1 (.single V2))).subst (fun _ => A)) := disjointStep.subst (fun _ => A)
end Lamping.Checks.FunctionRegionLong

namespace Lamping.Checks.ArgumentTailAll
open Lambda
private def I : Term := .lam (.var 0)
private def A : Term := .app I (.var 1)
private def B : Term := .app I A
private def shiftedA : Term := .app I (.var 2)
private def shiftedB : Term := .app I shiftedA
private def start : Term := .app (.lam (.lam (.var 1))) B
private def copied : Term := .lam shiftedB
private def originalEnd : Term := .app (.lam (.lam (.var 1))) (.var 1)
private def R : BetaAt start [] copied := ⟨.lam (.var 1),B,rfl,rfl⟩
private def S : BetaAt copied [.body] (.lam shiftedA) := ⟨.var 0,shiftedA,rfl,rfl⟩
private def T : BetaAt (.lam shiftedA) [.body] (.lam (.var 2)) := ⟨.var 0,.var 2,rfl,rfl⟩
private def V : BetaAt copied [.body,.arg] (.lam shiftedA) := ⟨.var 0,.var 2,rfl,rfl⟩
private def S' : BetaAt start [.arg] (.app (.lam (.lam (.var 1))) A) := ⟨.var 0,A,rfl,rfl⟩
private def T' : BetaAt (.app (.lam (.lam (.var 1))) A) [.arg] originalEnd := ⟨.var 0,.var 1,rfl,rfl⟩
private def copyHistory := ParallelHistory.cons (singleContraction S) (.single (singleContraction T))
private def originalHistory := ParallelHistory.cons (singleContraction S') (.single (singleContraction T'))
private def lift : ArgumentLift R copyHistory originalHistory where
  body := .lam (.var 1)
  argument := B
  redex := rfl
  occurrence := [.body]
  isVariable := rfl
  localPaths := [[],[]]
  copy_paths := rfl
  original_paths := rfl
  parallelization := StepProjection.exists_projection (singleContraction R) originalHistory
private theorem later : ExtractionStep (.of copyHistory (.cons S (.single T)))
    (.of (.single (singleContraction V)) (.single V)) := by
  apply ExtractionStep.residual (.nil _) (.nil _) S T V
  rw [ParallelStep.residual_iff]
  decide
example : binderDepth lift.occurrence=1 := rfl
private def copiedPoint : RedexWithHistory copied :=
  ⟨.lam shiftedA,.single (singleContraction S),⟨[.body],T.redex⟩⟩
private def originalPoint : RedexWithHistory start :=
  ⟨.app (.lam (.lam (.var 1))) A,.single (singleContraction S'),⟨[.arg],T'.redex⟩⟩
example : ∃prefixLift : ArgumentLift R copiedPoint.history originalPoint.history,
    prefixLift.occurrence=[.body] :=
  lift.pointed_prefix (.cons S (.single T)) (.cons S' (.single T')) copiedPoint originalPoint
    ⟨T,.single S,rfl⟩ ⟨T',.single S',rfl⟩
#print axioms ArgumentLift.pointed_prefix
example : ExtractionJoin (.of originalHistory (.cons S' (.single T')))
    (.of (.cons (singleContraction R) (.single (singleContraction V))) (.cons R (.single V))) :=
  argument_tail_peak R copyHistory (.cons S (.single T)) originalHistory (.cons S' (.single T')) lift later
example : ∃q,ExtractionStep (.of copyHistory (.cons S (.single T))) q ∧
    ((ExtractionRun.of (.single (singleContraction V)) (.single V)).rename (fun i => i+3))=
      q.rename (fun i => i+3) :=
  (later.rename (fun i => i+3)).shift_reflect 3
#print axioms ExtractionStep.rename_reflect
#print axioms ExtractionStep.shift_reflect
#print axioms argument_tail_peak
private def outerStart : Term := .app A start
private def outerEnd : Term := .app (.var 1) start
private def Q : BetaAt outerStart [.fn] outerEnd := ⟨.var 0,.var 1,rfl,rfl⟩
private def C : SyntaxContext := .frame (.arg A) .hole
private def D : SyntaxContext := .frame (.arg (.var 1)) .hole
private def localRun : ExtractionRun start := .of
  (.cons (singleContraction R) copyHistory) (.cons R (.cons S (.single T)))
private def localTarget : ExtractionRun start := .of originalHistory (.cons S' (.single T'))
private theorem localArgument : ExtractionStep localRun localTarget :=
  ExtractionStep.argumentPart (.nil _) (.nil _) R copyHistory (.cons S (.single T))
    originalHistory (.cons S' (.single T')) (by change 0<2; omega) lift
example : ExtractionStep (localRun.subst (fun _ => A)) (localTarget.subst (fun _ => A)) :=
  localArgument.subst (fun _ => A)
example : ExtractionNormal (.of (.single (singleContraction S')) (.single S')) := by
  let one : ArgumentLift R (.single (singleContraction S)) (.single (singleContraction S')) :=
    { body := .lam (.var 1), argument := B, redex := rfl, occurrence := [.body], isVariable := rfl,
      localPaths := [[]], copy_paths := rfl, original_paths := rfl,
      parallelization := StepProjection.exists_projection (singleContraction R) (.single (singleContraction S')) }
  exact one.normal_original (.single S) (.single S') (extraction_single_normal S)
example : ExtractionJoin (C.liftRun localRun)
    (.of (.cons (singleContraction Q) (D.liftRun localTarget).history)
      (.cons Q (D.liftRun localTarget).atomic)) := by
  have inside : Internal [.arg] (D.liftRun localRun).history := D.liftRun_internal localRun
  have apart : DisjointPositions [.fn] [.arg] := by
    constructor <;> rintro ⟨q,hq⟩ <;> cases hq
  obtain ⟨v,source,remaining,hs,sourcePaths,sourceInside,sourceRow⟩ :=
    (D.liftRun localRun).atomic.disjoint_row_pullback Q apart inside
  have sameSource : ExtractionRun.of source hs=C.liftRun localRun := by
    apply ExtractionRun.ext_paths
    change source.derivation.paths=(C.liftRun localRun).history.derivation.paths
    rw [sourcePaths,D.liftRun_paths,C.liftRun_paths]
    rfl
  have positive : 0<source.length := by
    have len := sourceRow.length
    have count : (D.liftRun localRun).history.length=3 := by
      rw [show (D.liftRun localRun).history=D.liftHistory localRun.history from rfl,
        D.liftHistory_length]
      rfl
    omega
  have joined := disjoint_tail_peak Q source hs (D.liftRun localRun).history
    (D.liftRun localRun).atomic sourceRow positive apart sourceInside (D.liftExtractionStep localArgument)
  rw [sameSource] at joined
  exact joined
#print axioms StepProjection.disjoint_paths
#print axioms disjoint_tail_peak
end Lamping.Checks.ArgumentTailAll

namespace Lamping.Checks.FunctionArgumentCore
open Lambda
private def I : Term := .lam (.var 0)
private def A : Term := .app I (.var 0)
private def body : Term := .app I A
private def start : Term := .app (.lam body) (.var 0)
private def mid : Term := .app (.lam A) (.var 0)
private def finish : Term := .app I (.var 0)
private def R : BetaAt start [] body := ⟨body,.var 0,rfl,rfl⟩
private def S' : BetaAt start [.fn,.body] mid := ⟨.var 0,A,rfl,rfl⟩
private def S : BetaAt body [] A := ⟨.var 0,A,rfl,rfl⟩
private def R' : BetaAt mid [] A := ⟨A,.var 0,rfl,rfl⟩
private def A' : BetaAt mid [.fn,.body] finish := ⟨.var 0,.var 0,rfl,rfl⟩
private def T : BetaAt A [] (.var 0) := ⟨.var 0,.var 0,rfl,rfl⟩
private def R1 : BetaAt finish [] (.var 0) := ⟨.var 0,.var 0,rfl,rfl⟩
private def V : BetaAt body [.arg] A := ⟨.var 0,.var 0,rfl,rfl⟩
private theorem front : StepProjection (singleContraction R) (.single (singleContraction S'))
    (.single (singleContraction S)) (singleContraction R') := by
  let sq : ParallelMovesSquare [[]] [[.fn,.body]] start body mid A :=
    ⟨singleContraction R,singleContraction S',by change ParallelStep [[]] _ _; exact singleContraction S,
      by change ParallelStep [[]] _ _; exact singleContraction R'⟩
  exact .cons sq (.nil _)
private theorem row : StepProjection (singleContraction R') (.single (singleContraction A'))
    (.single (singleContraction T)) (singleContraction R1) := by
  let sq : ParallelMovesSquare [[]] [[.fn,.body]] mid A finish (.var 0) :=
    ⟨singleContraction R',singleContraction A',by change ParallelStep [[]] _ _; exact singleContraction T,
      by change ParallelStep [[]] _ _; exact singleContraction R1⟩
  exact .cons sq (.nil _)
private def lift : ArgumentLift S (.single (singleContraction T)) (.single (singleContraction V)) where
  body := .var 0
  argument := A
  redex := rfl
  occurrence := []
  isVariable := rfl
  localPaths := [[]]
  copy_paths := rfl
  original_paths := rfl
  parallelization := StepProjection.exists_projection (singleContraction S) (.single (singleContraction V))
private def whole := ParallelHistory.cons (singleContraction S') (.single (singleContraction A'))
private theorem wholeInside : Internal [.fn] whole := by
  intro name hq
  change name∈[[.fn,.body],[.fn,.body]] at hq
  simp only [List.mem_cons,List.not_mem_nil,or_false,or_self] at hq
  subst name
  exact ⟨[.body],rfl⟩
private theorem wholeRow : StepProjection (singleContraction R) whole
    (.cons (singleContraction S) (.single (singleContraction T))) (singleContraction R1) := front.append row
private theorem early : ExtractionStep
    (.of (.cons (singleContraction R) (.cons (singleContraction S) (.single (singleContraction T))))
      (.cons R (.cons S (.single T)))) (.of whole (.cons S' (.single A'))) :=
  ExtractionStep.functionPart (.nil _) (.nil _) R whole (.cons S' (.single A'))
    _ (.cons S (.single T)) (singleContraction R1) wholeRow (by change 0<2; omega) wholeInside
private theorem late : ExtractionStep
    (.of (.cons (singleContraction R) (.cons (singleContraction S) (.single (singleContraction T))))
      (.cons R (.cons S (.single T))))
    (.of (.cons (singleContraction R) (.single (singleContraction V))) (.cons R (.single V))) := by
  exact ExtractionStep.argumentPart (.single (singleContraction R)) (.single R) S
    _ (.single T) _ (.single V) (by decide) lift
example : ExtractionStep
    ((ExtractionRun.of (.cons (singleContraction R) (.cons (singleContraction S) (.single (singleContraction T))))
      (.cons R (.cons S (.single T)))).subst (fun _ => A))
    ((ExtractionRun.of whole (.cons S' (.single A'))).subst (fun _ => A)) := early.subst (fun _ => A)
example : ExtractionJoin
    (.of (.cons (singleContraction S') (.single (singleContraction A'))) (.cons S' (.single A')))
    (.of (.cons (singleContraction R) (.single (singleContraction V))) (.cons R (.single V))) :=
  extraction_function_argument_long_peak R (.nil _) (.nil _) S _ (.single T)
    whole (.cons S' (.single A')) wholeRow wholeInside _ (.single V) (by decide) lift
example : ExtractionJoin (.of whole (.cons S' (.single A')))
    (.of (.cons (singleContraction R) (.single (singleContraction V))) (.cons R (.single V))) :=
  extraction_locally_confluent start early late
example : ExtractionConfluent start := extraction_church_rosser start
#print axioms StepProjection.function_paths
#print axioms StepProjection.function_paths_at
#print axioms StepProjection.function_paths_reflect_at
#print axioms function_argument_pullback
#print axioms RootExtraction.region_tail_join
#print axioms extraction_function_argument_long_peak
#print axioms RootExtraction.tail_join
#print axioms extraction_locally_confluent
#print axioms extraction_church_rosser
#print axioms extraction_normal_unique
end Lamping.Checks.FunctionArgumentCore

namespace Lamping.Checks.SubstitutionActual
open Lambda
private def I : Term := .lam (.var 0)
private def A : Term := .app I (.var 0)
private def inside : Term := .app I (.var 2)
private def start : Term := .app I inside
private def R : BetaAt start [] inside := ⟨.var 0,inside,rfl,rfl⟩
private def S : BetaAt inside [] (.var 2) := ⟨.var 0,.var 2,rfl,rfl⟩
private def V : BetaAt start [.arg] inside := ⟨.var 0,.var 2,rfl,rfl⟩
private theorem step : ExtractionStep
    (.of (.cons (singleContraction R) (.single (singleContraction S))) (.cons R (.single S)))
    (.of (.single (singleContraction V)) (.single V)) := by
  apply ExtractionStep.residual (.nil _) (.nil _) R S V
  rw [ParallelStep.residual_iff]
  decide
example : subst (fun _ => A) start=.app I (.app I A) := rfl
example : ExtractionStep
    ((ExtractionRun.of (.cons (singleContraction R) (.single (singleContraction S))) (.cons R (.single S))).subst (fun _ => A))
    ((ExtractionRun.of (.single (singleContraction V)) (.single V)).subst (fun _ => A)) := step.subst (fun _ => A)
private def invalid : ParallelStep [[]] (.var 0) (.var 0) where
  paths := []
  markedTarget := .var 0
  complete := (Marked.completeOld_iff _ _).mpr ⟨.nil _,by trivial⟩
  target_eq := rfl
example : invalid.paths=[] := rfl
example : ¬∃h : ParallelStep [[]] A A,h.paths=[] := by
  rintro ⟨h,paths⟩
  obtain ⟨history,normal⟩ := (Marked.completeOld_iff _ _).mp h.complete
  rw [paths] at history
  have equal := history.general.deterministic (.nil _)
  rw [equal] at normal
  exact normal
example : ExtractionNormal (.of (.single (singleContraction V)) (.single V)) :=
  extraction_single_normal V
example : RootExtraction R (.of (.single (singleContraction S)) (.single S))
    (.of (.single (singleContraction V)) (.single V)) :=
  step.root_of_normal_tail (extraction_single_normal S)
#print axioms BetaAt.subst
#print axioms Atomic.substitute
#print axioms ArgumentLift.run_contexts
#print axioms ArgumentLift.normal_original
#print axioms ArgumentOccurrence.substitute
#print axioms ArgumentLift.substitute
#print axioms StepProjection.substitute_region
#print axioms ExtractionStep.subst
#print axioms ExtractionNormal.subst_reflect
#print axioms StepProjection.function_normal_reflect
#print axioms RootExtraction.normal_target
#print axioms extraction_normal_head_decomposition
end Lamping.Checks.SubstitutionActual

namespace Lamping.Checks.CanonicalCreated
open Lambda
private def delta : Term := .lam (.app (.var 0) (.var 0))
private def omega : Term := .app delta delta
private def R : BetaAt omega [] omega := ⟨.app (.var 0) (.var 0),delta,rfl,rfl⟩
private def point : RedexWithHistory omega := ⟨omega,.single (singleContraction R),⟨[],R.redex⟩⟩
private def run : ExtractionRun omega := .of
  (.cons (singleContraction R) (.single (singleContraction R))) (.cons R (.single R))
private theorem fresh : ∀r : RedexOcc omega,¬(singleContraction R).derivation.Residual r ⟨[],R.redex⟩ := by
  intro r residual
  have selected := (mem_redexPositions omega r.val).mpr r.property
  change r.val∈[[]] at selected
  have position := List.mem_singleton.mp selected
  rw [ParallelStep.residual_iff] at residual
  rw [position] at residual
  exact (by decide : ¬([] : Path)∈Marked.tracePositions [] (singleContraction R).markedTarget) residual
private theorem canonical : CanonicalRun run := by
  refine ⟨by change 0<2; omega,?_,extraction_two_normal_of_fresh R R fresh⟩
  apply Standard.cons (singleContraction R) ⟨[],R.redex⟩ (leftmost_singleton _)
  · intro s before
    have noLeft : ∀q : Path,¬LeftOf q [] := by intro q h; cases h
    have impossible := noLeft s.val before
    contradiction
  · exact Standard.single_step _ ⟨[],R.redex⟩ (leftmost_singleton _)
private def empty := ParallelStep.empty omega
private def later : RedexWithHistory omega :=
  ⟨omega,point.history.append (.single empty),point.redex⟩
private theorem family : FamilyEq point later := by
  apply FamilyEq.of_permutation
  simpa only [ParallelHistory.append_nil] using
    PermEq.comp (PermEq.refl point.history) (PermEq.empty empty).symm
example : ¬(singleContraction R).derivation.Residual ⟨[],R.redex⟩ point.redex := fresh _
example : Copy point later :=
  (canonical_copy_iff_history_prefix canonical ⟨R,.single R,rfl⟩ family).mpr ⟨.single empty,.refl _⟩
#print axioms canonical_copy_of_standard
#print axioms canonical_copy_iff_history_prefix
#print axioms HistoryPrefix.projected_head_le
#print axioms Copy.prepend
#print axioms extraction_two_normal_of_fresh
end Lamping.Checks.CanonicalCreated

namespace Lamping.Checks.ArgumentTailAll
open Lambda
private def firstOriginalEvent : RedexWithHistory start := ⟨start,.nil _,⟨[.arg],S'.redex⟩⟩
example : FamilyUsed originalPoint.history firstOriginalEvent := .head (by simp) (.refl _)
example : FamilyUsed ((ParallelHistory.single (singleContraction R)).append copiedPoint.history)
    firstOriginalEvent := by
  have sourceRep : RunRepresents localRun
      (copiedPoint.prepend (.single (singleContraction R))) :=
    ⟨T,.cons R (.single S),rfl⟩
  have targetRep : RunRepresents localTarget originalPoint := ⟨T',.single S',rfl⟩
  exact localArgument.pointed_family_events sourceRep targetRep _ (.head (by simp) (.refl _))
-- Excluding the last contraction is substantive: its family was not used by
-- the one-step proper prefix, even though it is contracted by the full run.
example : ¬FamilyUsed originalPoint.history originalPoint := by
  intro used
  cases used with
  | head selected family =>
    have ep := List.mem_singleton.mp selected
    have er : _ = (⟨[.arg],S'.redex⟩ : RedexOcc start) := Subtype.ext ep
    subst er
    have residual := (initial_family_iff ⟨[.arg],S'.redex⟩ originalPoint).mp family
    change (singleContraction S').derivation.Residual ⟨[.arg],S'.redex⟩ ⟨[.arg],T'.redex⟩ at residual
    rw [ParallelStep.residual_iff] at residual
    exact (by decide : ¬([Step.arg] : Path)∈Marked.tracePositions [.arg] (singleContraction S').markedTarget) residual
  | tail impossible => cases impossible
end Lamping.Checks.ArgumentTailAll

namespace Lamping.Checks.CanonicalCreated
open Lambda
example : RelativeFamilies point.history (FamilyUsed later.history) :=
  canonical_prefix_relative canonical ⟨R,.single R,rfl⟩ family
example : FamilyUsed later.history ⟨omega,.nil _,⟨[],R.redex⟩⟩ := by
  exact canonical_prefix_relative canonical ⟨R,.single R,rfl⟩ family _ (.head (by simp) (.refl _))
end Lamping.Checks.CanonicalCreated

namespace Lamping.Checks.Extraction
open Lambda
private theorem outer_development : DevelopsFamilies outerPrefix (FamilyUsed outerPrefix) := by
  refine ⟨fun _ h => h,?_⟩
  intro r used
  cases used with
  | head selected family =>
    have ep := List.mem_singleton.mp selected
    have er : _ = outerOriginal := Subtype.ext ep
    subst er
    have residual := (initial_family_iff outerOriginal ⟨_,outerPrefix,r⟩).mp family
    change (singleContraction outerBeta).derivation.Residual outerOriginal r at residual
    rw [ParallelStep.residual_iff] at residual
    have empty : Marked.tracePositions outerOriginal.val (singleContraction outerBeta).markedTarget=[] := by decide
    rw [empty] at residual
    exact List.not_mem_nil residual
  | tail impossible => cases impossible
example : ∃run ancestor,CanonicalRun run ∧ RunRepresents run ancestor ∧
    Copy ancestor ⟨_,outerPrefix,leftCopy⟩ ∧
    ∀s,FamilyEq ⟨_,outerPrefix,leftCopy⟩ ⟨_,outerPrefix,s⟩ → Copy ancestor ⟨_,outerPrefix,s⟩ :=
  outer_development.common_copy_ancestor leftCopy
example : ∃F,CopySet outerPrefix F ∧ leftCopy.val∈F ∧ rightCopy.val∈F := by
  obtain ⟨F,copySet,left,members⟩ := outer_development.family_copySet leftCopy
  exact ⟨F,copySet,left,(members rightCopy).mpr two_copies_same_family⟩
#print axioms StepProjection.family_used_forward
#print axioms ArgumentLift.family_used_forward
#print axioms ExtractionStep.pointed_family_events
#print axioms Extraction.pointed_family_events
#print axioms canonical_prefix_relative
#print axioms canonical_copy_of_development
#print axioms DevelopsFamilies.common_copy_ancestor
#print axioms DevelopsFamilies.family_copySet
end Lamping.Checks.Extraction

namespace Lamping.Checks.CompleteFamilyAncestors
open Lambda
open Lamping.Checks.Extraction
example : ∃(ancestor : RedexWithHistory start) (extension : ParallelHistory ancestor.target (.app argTerm argTerm)),
    PermEq (ancestor.history.append extension) outerPrefix ∧
    ∀s : RedexOcc (.app argTerm argTerm),
      FamilyEq ⟨_,outerPrefix,leftCopy⟩ ⟨_,outerPrefix,s⟩ ↔
        extension.derivation.Residual ancestor.redex s :=
  outer_prefix_complete.family_residual_representation leftCopy
example : ∃F,CopySet outerPrefix F ∧ leftCopy.val∈F ∧ rightCopy.val∈F := by
  obtain ⟨F,copySet,left,members⟩ := outer_prefix_complete.family_copySet leftCopy
  exact ⟨F,copySet,left,(members rightCopy).mpr two_copies_same_family⟩
-- The complete-prefix theorem applies while an actual beta redex remains.
open Lamping.Checks.Families in
example : ∃(ancestor : RedexWithHistory omegaTerm) (extension : ParallelHistory ancestor.target omegaTerm),
    PermEq (ancestor.history.append extension) (.single omegaParallel) ∧
    ∀s : RedexOcc omegaTerm,
      FamilyEq ⟨_,.single omegaParallel,omegaRedex⟩ ⟨_,.single omegaParallel,s⟩ ↔
        extension.derivation.Residual ancestor.redex s := by
  have complete : CompleteDerivation (.single omegaParallel) := .step (.nil _) omega_complete_step
  exact complete.family_residual_representation omegaRedex
#print axioms CompleteDerivation.common_copy_ancestor
#print axioms CompleteDerivation.family_copySet
#print axioms CompleteDerivation.family_residual_representation
end Lamping.Checks.CompleteFamilyAncestors
