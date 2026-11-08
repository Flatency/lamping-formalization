import Lamping.Lambda.FunctionArgumentOccurrenceReflect
import Lamping.Lambda.PermutationCancellation
import Lamping.Lambda.ExtractionChurchRosser
import Lamping.Lambda.CopySetRepresentation
import Lamping.Lambda.PrefixProjection
import Lamping.Lambda.CopyRegionAncestry
import Lamping.Lambda.CopyRegionProjection
import Lamping.Lambda.ValidParallelSubstitution
import Lamping.Lambda.RenameProjectionStandardness
import Lamping.Lambda.CopyArgumentProjection
import Lamping.Lambda.InitialCompleteCopies
import Lamping.Lambda.ExtractionNormalHead
import Lamping.Lambda.CopyCommonExtraction
import Lamping.Lambda.ArgumentPointedPrefix
import Lamping.Lambda.RootPointedProjection
import Lamping.Lambda.CanonicalUniqueness
import Lamping.Lambda.RootProjectedCopyReflection
import Lamping.Lambda.CanonicalCopyAncestor
import Lamping.Lambda.FamilyDevelopments
import Lamping.Lambda.FamilyDevelopmentJoin
import Lamping.Lambda.FamilyStandardization
import Lamping.Lambda.FamilyCopyAncestor
import Lamping.Lambda.CompleteCopyCharacterization
import Lamping.Lambda.CompleteFamilyAncestors
import Lamping.Lamping.InitialOffsets
import Lamping.Lamping.InitialPatchRoutes
import Lamping.Lamping.InitialTraceShape
import Lamping.Lamping.InitialBoundaryProjection
import Lamping.Lamping.InitialOccurrencePaths
import Lamping.Lamping.InitialOffsetFormula
import Lamping.Lamping.InitialLoopProjection
import Lamping.Lambda.InitialFamilies
import Lamping.Lambda.SubstitutionTraceOrigins
import Lamping.Lambda.SubstitutionOrigins
import Lamping.Lambda.RootCreation
import Lamping.Lambda.DisjointCommutation
import Lamping.Lambda.HeadVariableInvariant
import Lamping.Lambda.ApplicationDiamond
import Lamping.Lambda.RootHeadGuard
import Lamping.Lambda.RootApplicationIdentity
import Lamping.Lambda.CreationSeparation
import Lamping.Lambda.DisjointCreationSeparation
import Lamping.Lambda.ProjectionFamilies
import Lamping.Lambda.ContextualCreationSeparation
import Lamping.Lambda.CreationIntersection
import Lamping.Lambda.ExtractionContexts
import Lamping.Lambda.StandardizationExistence
import Lamping.Lambda.StandardizationLeftResiduals
import Lamping.Lambda.ResidualExtractionPeak
import Lamping.Lambda.TraceNoDup
import Lamping.Lambda.StandardizationWeight
import Lamping.Lambda.AtomicRowExistence
import Lamping.Lambda.StandardizationCreation
import Lamping.Lambda.StepProjectionHead
import Lamping.Lambda.ExtractionFunctionResidualPeak
import Lamping.Lambda.ExtractionDisjointResidualPeak
import Lamping.Lambda.OrdinarySplits
import Lamping.Lambda.StandardizationGeneral
import Lamping.Lambda.ParallelPrefixScope
import Lamping.Lambda.StandardPrefixes
import Lamping.Lambda.ExtractionInternal
import Lamping.Lambda.ProjectionSplits
import Lamping.Lambda.ArgumentResidualScope
import Lamping.Lambda.ProjectionSingletonSelection
import Lamping.Lambda.ExtractionRowSplits
import Lamping.Lambda.ExtractionFunctionLongTail
import Lamping.Lambda.ArgumentCommutation
import Lamping.Lambda.ArgumentHeadPreservation
import Lamping.Lambda.ExtractionArgumentResidualPeak
import Lamping.Lambda.ExtractionDisjointLongTail
import Lamping.Lambda.RenameResiduals
import Lamping.Lambda.CanonicalPrefixStandard
import Lamping.Lambda.ArgumentParallelization
import Lamping.Lambda.ExtractionArgumentLongTail
import Lamping.Lambda.ExtractionFamilyInvariance
import Lamping.Lambda.ProjectionRowUniqueness
import Lamping.Lambda.ExtractionArgumentUniqueness
import Lamping.Lambda.ExtractionRegionArgumentExclusion
import Lamping.Lambda.ParallelContextLift
import Lamping.Lambda.ParallelPrefixResidualSet
import Lamping.Lambda.ExtractionStandardness
import Lamping.Lambda.ExtractionIndex
import Lamping.Lambda.ExtractionCuts
import Lamping.Lambda.RootTailResidualPeak
import Lamping.Lambda.ProjectionContextLift
import Lamping.Lambda.CanonicalExistence
import Lamping.Lambda.ExtractionContextLift
import Lamping.Lambda.ExtractionRename
import Lamping.Lambda.CopyInitialExtraction
import Lamping.Lambda.ProjectionContextReflect
import Lamping.Lambda.ExtractionContextReflect
import Lamping.Lambda.SingletonCube
import Lamping.Lambda.ExtractionFunctionRegionPeak
import Lamping.Lambda.AtomicScheduleSplit
import Lamping.Lambda.CopyLeftExtraction
import Lamping.Lambda.StandardProtectedBlocks
import Lamping.Lambda.DisjointHistoryPullback
import Lamping.Lambda.ResidualSetComposition
import Lamping.Lambda.RightSiblingExtraction
import Lamping.Lambda.ExtractionFunctionRegionLongTail
import Lamping.Lambda.ApplicationRowDiamond
import Lamping.Lambda.ProjectionPermutation
import Lamping.Lambda.RootArgumentTailPeak
import Lamping.Lambda.FunctionProjectionStandardness
import Lamping.Lambda.RootDisjointTailPeak
import Lamping.Lambda.MaximalCopies
import Lamping.Lambda.ExtractionConfluence
import Lamping.Lamping.InitialPatchFlow
import Lamping.Lamping.InitialPathProjection
import Lamping.Lambda.ResidualOrigins
import Lamping.Lamping.InitialFlow
import Lamping.Lamping.PathSiteBeta
import Lamping.Lambda.ArgumentPullback
import Lamping.Lambda.ContextualBeta
import Lamping.Lambda.ExtractionClosure
import Lamping.Lambda.CompleteFamilies
import Lamping.Lambda.OccurrenceRank
import Lamping.Lambda.FiniteSelections
import Lamping.Lambda.AtomicHistories
import Lamping.Lamping.LocalActionTransport
import Lamping.Lambda.ExtractionTermination
import Lamping.Lamping.LocalCancellation
import Lamping.Lambda.Extraction
import Lamping.Lamping.InitialPathControls
import Lamping.Lambda.SingleContraction
import Lamping.Lambda.PermutationResidual
import Lamping.Lambda.ReselectionIdentity
import Lamping.Lamping.PathSiteTransport
import Lamping.Lamping.PathSplicing
import Lamping.Lamping.InitialPaths
import Lamping.Lambda.Labels
import Lamping.Lamping.PathDefinitions
import Lamping.Lambda.DevelopmentTheory
namespace Lamping.Checks.Phase4Review
open Lambda

-- Same endpoint does not identify the histories: I (I I) has two
-- one-step contractions to I I, but the remaining old redex is different.
def ident : Term := .lam (.var 0)
def inner : Term := .app ident ident
def sameEnd : Term := .app ident inner

theorem sameEnd_closed : Closed sameEnd := by simp [Closed, Scoped, sameEnd, inner, ident]

theorem outer_step : BetaAt sameEnd [] inner := by
  exact ⟨.var 0, inner, rfl, rfl⟩
theorem inner_step : BetaAt sameEnd [.arg] inner := by
  exact ⟨.var 0, ident, rfl, rfl⟩
theorem histories_distinct : ([[]] : List Path) ≠ [[.arg]] := by decide

def outerTracked : Marked := Marked.app [[.arg]] (.lam (.var 0)) (.lam (.var 0))
def innerTracked : Marked := Marked.app [[]] (.lam (.var 0)) (.lam (.var 0))
theorem outer_tracking : Marked.History [[]] (Marked.mark [] sameEnd) outerTracked :=
  .cons (.appRoot _ _ _) (.nil _)
theorem inner_tracking : Marked.History [[.arg]] (Marked.mark [] sameEnd) innerTracked :=
  .cons (.appR (.appRoot _ _ _)) (.nil _)
example : Marked.tracePositions [] outerTracked = [] := by decide
example : Marked.tracePositions [] innerTracked = [[]] := by decide
example : Marked.tracePositions [.arg] outerTracked = [[]] := by decide
example : Marked.tracePositions [.arg] innerTracked = [] := by decide

-- Rejected X01's concrete closed obstruction: after outer duplication,
-- firing only the left copy leaves a real residual on the right.
def argRedex : Term := .app ident ident
def dup : Term := .app (.lam (.app (.var 0) (.var 0))) argRedex
def duplicated : Term := .app argRedex argRedex
def partiallyReduced : Term := .app ident argRedex
example : Closed dup := by simp [Closed, Scoped, dup, argRedex, ident]
example : BetaAt dup [] duplicated := ⟨.app (.var 0) (.var 0), argRedex, rfl, rfl⟩
example : BetaAt duplicated [.fn] partiallyReduced := ⟨.var 0, ident, rfl, rfl⟩
example : redexPositions partiallyReduced = [[], [.arg]] := by decide
-- This is a concrete obstruction fixture; no full family theorem is asserted here.

#print axioms sameEnd_closed
#print axioms outer_tracking
#print axioms inner_tracking
end Lamping.Checks.Phase4Review


namespace Lamping.Checks.Phase4GraphScratch
open Lamping.AG Lamping.Graph
def loopGraph : Net signature Unit Unit Empty where
  label := fun _ => label .app 0
  wire := {
    mate := fun e => match e with
      | .inl ⟨_, .inl _⟩ => .inl ⟨(),appCtx⟩
      | .inl ⟨_, .inr false⟩ => .inl ⟨(),.inl ()⟩
      | .inl ⟨_, .inr true⟩ => .inr (.inl ())
      | .inr (.inl _) => .inl ⟨(),appArg⟩
      | .inr (.inr ⟨e,_⟩) => nomatch e
    involutive := by
      rintro (⟨_,(_ | b)⟩ | (_ | ⟨e,_⟩))
      · rfl
      · cases b <;> rfl
      · rfl
      · exact nomatch e
    fixedPointFree := by
      rintro (⟨_,(_ | b)⟩ | (_ | ⟨e,_⟩))
      · intro h; cases h
      · cases b <;> (intro h; cases h)
      · intro h; cases h
      · exact nomatch e }
def e : Endpoint loopGraph := .inl ⟨(),appCtx⟩
example : Walk loopGraph [e,e,e] :=
  .cons (.node (g:=loopGraph) () (Sum.inl ()) appCtx (by intro h; cases h))
    (.cons (.node (g:=loopGraph) () (Sum.inl ()) appCtx (by intro h; cases h)) (.single e))
example : ProperPath loopGraph [e,e,e] := by
  refine ⟨Context.empty,Context.empty,?_⟩
  exact .cons (.node (g:=loopGraph) () (Sum.inl ()) appCtx (.inverse (.appFun _)))
    (.cons (.node (g:=loopGraph) () (Sum.inl ()) appCtx (.inverse (.appFun _))) (.single e _))
example : ¬ Walk loopGraph [e,loopGraph.wire e] := by
  intro h
  cases h with
  | cons h _ =>
    cases h with
    | node n p q hd => exact hd rfl
end Lamping.Checks.Phase4GraphScratch


namespace Lamping.Checks.Phase4ContextReview
open Lamping.AG
example : Context.empty.cons Level.empty = Context.empty := Context.cons_empty
example : Context.SameShell 1
    (Context.empty.cons (.o .empty))
    ((Context.empty.cons (.star .empty)).cons (.o .empty)) := by
  intro k hk; have he : k=0 := by omega
  subst k; rfl
example : (Context.empty.cons (.o .empty)) ≠
    ((Context.empty.cons (.star .empty)).cons (.o .empty)) := by
  intro h
  have hh := congrArg (fun c : Context => c.get 1) h
  cases hh
example (a b : Context) (x y : Level) :
    Passage 0 (.op .bra) (.inr ()) (.inl ())
      ((b.cons x).cons y) (b.cons (.pair x y)) := by
  simpa using Passage.bra (i:=0) a b x y
example (a b : Context) :
    Passage 0 (.op .cro) (.inr ()) (.inl ()) b (b.cons .empty) := by
  simpa using Passage.cro (i:=0) a b
end Lamping.Checks.Phase4ContextReview

namespace Lamping.Checks.Phase4LabelReview
open Lamping.Lambda Lamping.Lambda.Labelled
example (t : Term) : INIT (Lamping.Lambda.Labelled.initLabels t) := init_is_INIT t
example : LTerm.degree (.app (Label.atom 0) (.lam (Label.atom 1) (.var (Label.atom 2) 0))
    (.var (Label.atom 3) 0)) = some (Label.atom 1) := rfl
example : LTerm.degree (.app (Label.atom 0) (.lam (Label.atom 1) (.var (Label.atom 2) 0))
    (.var (Label.atom 3) 0)) ≠ some (Label.atom 0) := by decide
example (b a : LTerm) :
    (LTerm.contract (Label.atom 0) (Label.atom 1) b a).erase =
      Lambda.contract b.erase a.erase := LTerm.erase_contract _ _ _ _
example (b a : LTerm) : ¬ INIT (LTerm.contract (Label.atom 0) (Label.atom 1) b a) :=
  root_contract_not_INIT _ _ _ _
#print axioms init_is_INIT
#print axioms LTerm.erase_contract
#print axioms root_contract_not_INIT
end Lamping.Checks.Phase4LabelReview




namespace Lamping.Checks.Phase4InitialReview
open Lamping.AG Lamping.Graph Lamping.Lambda
example (t : Term) (n : Nat) (v : (encode n t).N) (f : Op)
    (h : ((encode n t).net.label v).sort = .op f) :
    n ≤ ((encode n t).net.label v).index := encode_level_lower t n v h
#print axioms encode_level_lower
#print axioms encode_label_range
end Lamping.Checks.Phase4InitialReview

namespace Lamping.Checks.FanScratch
open Lamping.AG
theorem fan_o_tag {a b : Context}
    (h : Traversal 0 (.op .fan) fanO (Sum.inl ()) a b) :
    ∃ x, b.get 0 = .o x := by
  cases h with
  | direct h => cases h with
    | fanO shell tail x => exact ⟨x,rfl⟩
  | inverse h => cases h

theorem fan_star_tag {a b : Context}
    (h : Traversal 0 (.op .fan) fanStar (Sum.inl ()) a b) :
    ∃ y, b.get 0 = .star y := by
  cases h with
  | direct h => cases h with
    | fanStar shell tail x => exact ⟨x,rfl⟩
  | inverse h => cases h
theorem distinct_branches {a b c : Context}
    (h : Traversal 0 (.op .fan) fanO (Sum.inl ()) a b)
    (k : Traversal 0 (.op .fan) (Sum.inl ()) fanStar b c) : False := by
  obtain ⟨x,hx⟩ := fan_o_tag h
  obtain ⟨y,hy⟩ := fan_star_tag k.reverse
  cases hx.symm.trans hy
end Lamping.Checks.FanScratch



namespace Lamping.Checks.Phase4SpliceReview
open Lamping.AG Lamping.Graph
example {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} {xs ys : List (Endpoint g)} {e : Endpoint g}
    {a b c : Context} (h : Labelling g (xs ++ [e]) a b)
    (k : Labelling g (e :: ys) b c) : Labelling g (xs ++ e :: ys) a c := h.join k
example {i : Nat} {p q : Port (.op .lam)} {a b : Context}
    (h : Traversal i (.op .lam) p q a b) : p ≠ lamBind ∧ q ≠ lamBind := h.no_binding
#print axioms Labelling.join
#print axioms Labelling.splice
#print axioms Traversal.no_binding
end Lamping.Checks.Phase4SpliceReview

namespace Lamping.Checks.Phase4SiteReview
open Lamping.AG Lamping.Graph
example {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
    [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
    (site : PathSite s kept (B:=B) (W:=W) (V:=V))
    {x y : s.Frontier} {a b : Context} (p : LocalPath s.right.net x y a b) :
    Labelling site.reduce (site.rhsEdges p) a b := site.rhs_labeling p
#print axioms plugRight_wire
#print axioms Labelling.plugRight
#print axioms PathSite.rhs_labeling
#print axioms PathSite.rhs_finish
end Lamping.Checks.Phase4SiteReview
namespace Lamping.Checks.Phase4RelabelReview
open Lamping.AG
example : Nonempty (LocalPath (Schema.fanAction .app 0 1 (by omega)).left
    (.inr false) (.inr true) Context.empty Context.empty) :=
  ⟨passiveAppLeft .fan 0 1 Context.empty⟩
example : ¬Nonempty (LocalPath (Schema.fanAction .app 0 1 (by omega)).right.net
    (.inr false) (.inr true) Context.empty Context.empty) :=
  no_empty_fanAction_passiveApp 1 (by omega)
#print axioms no_empty_fanAction_passiveApp
#print axioms fanActionPassiveApp
#print axioms fanActionPaths
#print axioms croActionPaths
#print axioms braActionPaths
end Lamping.Checks.Phase4RelabelReview

namespace Lamping.Checks.Phase4ReselectReview
open Lamping.Lambda Lamping.Lambda.Marked
def fresh : Marked := .app [] (.lam (.var 0)) (.var 0)
example (F : List Path) : activePositions (reselect F fresh) = [] := by
  simp [fresh, reselect, activePositions]
def twoCopies : Marked := .app [] (.app [[.arg]] (.lam (.var 0)) (.var 0))
    (.app [[.arg]] (.lam (.var 0)) (.var 0))
example : activePositions (reselect [[.arg]] twoCopies) = [[.fn], [.arg]] := by decide
example : tracePositions [.arg] (reselect [[.arg]] twoCopies) = [[.fn], [.arg]] := by decide
example (F G : List Path) (t : Term) : reselect F (mark G t) = mark F t :=
  reselect_mark F G t
#print axioms reselect_subst
#print axioms History.reselect
#print axioms reselect_mark
#print axioms Lamping.Lambda.ParallelStep.residual_iff
end Lamping.Checks.Phase4ReselectReview

namespace Lamping.Checks.Phase4PermutationReview
open Lamping.Lambda
example (F G : List Path) (t : Term) :
    ∃ u v w, Nonempty (ParallelMovesSquare F G t u v w) := by
  obtain ⟨u,⟨h⟩⟩ := ParallelStep.exists_target F t
  obtain ⟨v,⟨k⟩⟩ := ParallelStep.exists_target G t
  obtain ⟨w,hw⟩ := ParallelMovesSquare.exists h k
  exact ⟨u,v,w,hw⟩
example (h : Derivation t u) (k : Derivation u v) (r : RedexOcc t) (q : RedexOcc v) :
    (h.append k).Residual r q ↔
      ∃ s : RedexOcc u, h.Residual r s ∧ k.Residual s q := h.residual_append k r q
example {h k : ParallelHistory t u} (hp : PermEq h k) (r : RedexOcc t) (s : RedexOcc u) :
    h.derivation.Residual r s ↔ k.derivation.Residual r s := hp.residual r s
example {a b c : RedexWithHistory m} (h : Copy a b) (k : Copy b c) : Copy a c := h.trans k
#print axioms parallel_marked_diamond
#print axioms ParallelMovesSquare.exists
#print axioms ParallelMovesSquare.residual
#print axioms Derivation.residual_append
#print axioms PermEq.residual
#print axioms Copy.trans
end Lamping.Checks.Phase4PermutationReview
namespace Lamping.Checks.Phase4Review
open Lambda

def outerParallel : ParallelStep [[]] sameEnd inner :=
  ⟨[[]], outerTracked,
    (Marked.completeOld_iff [[]] sameEnd).mpr
      ⟨.cons (.root _ _ _) (.nil _), by trivial⟩, rfl⟩
def innerParallel : ParallelStep [[.arg]] sameEnd inner :=
  ⟨[[.arg]], innerTracked,
    (Marked.completeOld_iff [[.arg]] sameEnd).mpr
      ⟨.cons (.appR (.root _ _ _)) (.nil _), by trivial⟩, rfl⟩
def originalRoot : RedexOcc sameEnd := ⟨[], _, rfl, trivial⟩
def survivingRoot : RedexOcc inner := ⟨[], _, rfl, trivial⟩

theorem same_endpoint_not_permutation :
    ¬ PermEq (ParallelHistory.single outerParallel) (ParallelHistory.single innerParallel) := by
  intro hp
  have hinner : (ParallelHistory.single innerParallel).derivation.Residual originalRoot survivingRoot :=
    ⟨innerTracked, inner_tracking, rfl, by decide⟩
  have houter := (hp.residual originalRoot survivingRoot).mpr hinner
  have hh := ((ParallelHistory.single outerParallel).derivation.residual_iff_tracking
    outer_tracking originalRoot survivingRoot).mp houter
  change [] ∈ Marked.tracePositions [] outerTracked at hh
  simp [outerTracked, Marked.tracePositions] at hh
#print axioms same_endpoint_not_permutation
end Lamping.Checks.Phase4Review
namespace Lamping.Checks.Phase4Review
open Lambda

def duplicateTracked : Marked := .app []
    (.app [[.arg]] (.lam (.var 0)) (.lam (.var 0)))
    (.app [[.arg]] (.lam (.var 0)) (.lam (.var 0)))
def duplicateParallel : ParallelStep [[]] dup duplicated :=
  ⟨[[]], duplicateTracked,
    (Marked.completeOld_iff [[]] dup).mpr
      ⟨.cons (.root _ _ _) (.nil _), by trivial⟩, rfl⟩
def beforeCopy : RedexWithHistory dup :=
  ⟨dup, .nil dup, ⟨[.arg], _, rfl, trivial⟩⟩
def leftCopy : RedexWithHistory dup :=
  ⟨duplicated, .single duplicateParallel, ⟨[.fn], _, rfl, trivial⟩⟩
def rightCopy : RedexWithHistory dup :=
  ⟨duplicated, .single duplicateParallel, ⟨[.arg], _, rfl, trivial⟩⟩

theorem copies_same_family : FamilyEq leftCopy rightCopy := by
  have hl : Copy beforeCopy leftCopy := by
    refine ⟨.single duplicateParallel, .refl _, ?_⟩
    apply (duplicateParallel.residual_iff beforeCopy.redex leftCopy.redex).mpr
    decide
  have hr : Copy beforeCopy rightCopy := by
    refine ⟨.single duplicateParallel, .refl _, ?_⟩
    apply (duplicateParallel.residual_iff beforeCopy.redex rightCopy.redex).mpr
    decide
  exact .trans (.symm (.copy hl)) (.copy hr)
#print axioms copies_same_family
end Lamping.Checks.Phase4Review

namespace Lamping.Checks.Phase4NewBridgeReview
open Lamping.AG Lamping.Graph Lamping.Lambda
example (h : BetaAt t p u) : (singleContraction h).paths = [p] := rfl
example : (singleContraction Lamping.Checks.Phase4Review.outer_step).paths = [[]] := rfl
example (n : Nat) (shell tail : Context) :
    Context.SameShell n (shell.replace n tail) (shell.replace n (tail.cons .empty)) :=
  (identityBindingLoop n shell tail).shell
#print axioms identityBindingLoop
#print axioms initialVarPath
#print axioms Labelling.plugLeft
#print axioms Marked.StepAt.single_normal
#print axioms Marked.singleton_complete
#print axioms singleContraction
end Lamping.Checks.Phase4NewBridgeReview

namespace Lamping.Checks.Phase4ExtractionDefinitionReview
open Lamping.Lambda
example (h : BetaAt t p u) : Atomic (ParallelHistory.single (singleContraction h)) := Atomic.single h
example (h : Atomic ρ) : ρ.derivation.paths.length = ρ.length := h.paths_length
example (h : StepProjection step σ σ' last) : σ'.length = σ.length := h.length
#print axioms StepProjection.exists_projection
#print axioms StepProjection.permutation
#print axioms Atomic.paths_length
end Lamping.Checks.Phase4ExtractionDefinitionReview

namespace Lamping.Checks.Phase4CancellationReview
open Lamping.AG
example (i : Nat) (x y : Bool ⊕ Bool)
    (p : LocalPath (Schema.fanCancel i).left x y a b) :
    Nonempty (LocalPath (Schema.fanCancel i).right.net x y a b) := fanCancel_transport i x y p
example (i : Nat) (x y : Unit ⊕ Unit)
    (p : LocalPath (Schema.croCancel i).left x y a b) :
    Nonempty (LocalPath (Schema.croCancel i).right.net x y a b) := croCancel_transport i x y p
example (i : Nat) (x y : Unit ⊕ Unit)
    (p : LocalPath (Schema.braCancel i).left x y a b) :
    Nonempty (LocalPath (Schema.braCancel i).right.net x y a b) := braCancel_transport i x y p
#print axioms left_control_no_same_side
#print axioms fanCancel_transport
#print axioms croCancel_transport
#print axioms braCancel_transport
end Lamping.Checks.Phase4CancellationReview

namespace Lamping.Checks.Phase4ExtractionTerminationReview
open Lamping.Lambda
example (h : ExtractionStep r s) : s.rank < r.rank := h.rank_lt
example (m : Term) : ¬ ∃ f : Nat → ExtractionRun m,
    ∀ n, ExtractionStep (f n) (f (n+1)) := no_infinite_extraction m
example (m : Term) : WellFounded (fun s r : ExtractionRun m => ExtractionStep r s) :=
  extraction_wellFounded m
#print axioms ArgumentLift.length
#print axioms ExtractionStep.rank_lt
#print axioms no_infinite_extraction
#print axioms extraction_wellFounded
end Lamping.Checks.Phase4ExtractionTerminationReview

namespace Lamping.Checks.Phase4ActionReview
open Lamping.AG Lamping.Graph
example (f : Op) (i j : Nat) (lt : i<j) (x y : Bool ⊕ Aux f)
    (p : LocalPath (Schema.fanAction f i j lt).left x y a b) :
    ShellRelabel (Schema.fanAction f i j lt).right.net x y i a b :=
  fanAction_transport f i j lt x y p
example (f : Op) (i j : Nat) (lt : i<j) (x y : Unit ⊕ Aux f)
    (p : LocalPath (Schema.croAction f i j lt).left x y a b) :
    ShellRelabel (Schema.croAction f i j lt).right.net x y i a b :=
  croAction_transport f i j lt x y p
example (f : Op) (i j : Nat) (lt : i<j) (x y : Unit ⊕ Aux f)
    (p : LocalPath (Schema.braAction f i j lt).left x y a b) :
    ShellRelabel (Schema.braAction f i j lt).right.net x y i a b :=
  braAction_transport f i j lt x y p
example {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} (r : BetaEdge g) {loop : List (Endpoint g)}
    (h : ExpandedLabelling g loop a b)
    (ends : loop.getLast?=some (g.wire (.inl ⟨r.lam,r.lamBind⟩))) :
    ExpandedLabelling g (loop ++ r.reverseRoute ++ [r.argEnd]) a b :=
  r.expand_loop_labeling h ends
#print axioms fanAction_transport
#print axioms croAction_transport
#print axioms braAction_transport
#print axioms BetaEdge.principal_labeling
#print axioms BetaEdge.expand_loop_labeling
end Lamping.Checks.Phase4ActionReview

namespace Lamping.Checks.DisjointExtractionFixture
open Lamping.Lambda
def I : Term := .lam (.var 0)
def A : Term := .app I I
def T : Term := .app A A
def U : Term := .app I A
def V : Term := .app A I
def W : Term := .app I I
def R : BetaAt T [.fn] U := ⟨.var 0,I,rfl,rfl⟩
def S : BetaAt T [.arg] V := ⟨.var 0,I,rfl,rfl⟩
def SR : BetaAt U [.arg] W := ⟨.var 0,I,rfl,rfl⟩
def RS : BetaAt V [.fn] W := ⟨.var 0,I,rfl,rfl⟩
def square : ParallelMovesSquare [[.fn]] [[.arg]] T U V W :=
  ⟨singleContraction R,singleContraction S,singleContraction SR,singleContraction RS⟩
def row : StepProjection (singleContraction R) (.single (singleContraction S))
    (.single (singleContraction SR)) (singleContraction RS) :=
  .cons square (.nil _)
example : ExtractionStep
    (.of ((ParallelHistory.nil T |>.append (.single (singleContraction R))).append
      (.single (singleContraction SR))) ((Atomic.nil T |>.append (.single R)).append (.single SR)))
    (.of ((ParallelHistory.nil T).append (.single (singleContraction S)))
      ((Atomic.nil T).append (.single S))) := by
  apply ExtractionStep.disjoint (.nil T) (.nil T) R (.single (singleContraction S))
    (.single S) (.single (singleContraction SR)) (.single SR) (singleContraction RS) row
    (by decide) [.arg]
  · constructor <;> rintro ⟨s,h⟩ <;> cases h
  · intro q hq
    change q ∈ [[.arg]] at hq
    have he := List.mem_singleton.mp hq
    subst q
    exact ⟨[],rfl⟩
end Lamping.Checks.DisjointExtractionFixture
namespace Lamping.Checks.FunctionExtractionFixture
open Lamping.Lambda
def I : Term := .lam (.var 0)
def T : Term := .app (.lam (.app I (.var 0))) I
def U : Term := .app I I
def W : Term := I
def R : BetaAt T [] U := ⟨.app I (.var 0),I,rfl,rfl⟩
def S : BetaAt T [.fn,.body] U := ⟨.var 0,.var 0,rfl,rfl⟩
def SR : BetaAt U [] W := ⟨.var 0,I,rfl,rfl⟩
def RS : BetaAt U [] W := ⟨.var 0,I,rfl,rfl⟩
def square : ParallelMovesSquare [[]] [[.fn,.body]] T U U W :=
  ⟨singleContraction R,singleContraction S,singleContraction SR,singleContraction RS⟩
def row : StepProjection (singleContraction R) (.single (singleContraction S))
    (.single (singleContraction SR)) (singleContraction RS) :=
  .cons square (.nil _)
example : ExtractionStep
    (.of ((ParallelHistory.nil T |>.append (.single (singleContraction R))).append
      (.single (singleContraction SR))) ((Atomic.nil T |>.append (.single R)).append (.single SR)))
    (.of ((ParallelHistory.nil T).append (.single (singleContraction S)))
      ((Atomic.nil T).append (.single S))) := by
  apply ExtractionStep.functionPart (.nil T) (.nil T) R (.single (singleContraction S))
    (.single S) (.single (singleContraction SR)) (.single SR) (singleContraction RS) row (by decide)
  intro q hq
  change q ∈ [[.fn,.body]] at hq
  have he := List.mem_singleton.mp hq
  subst q
  exact ⟨[.body],rfl⟩
example : ¬DisjointPositions [] [.fn,.body] := by
  intro h
  exact h.1 ⟨[.fn,.body],rfl⟩
end Lamping.Checks.FunctionExtractionFixture

namespace Lamping.Checks.Phase4SubstitutionReview
open Lamping.Lambda
def newlyCreated : Term := .app (.lam (.var 0)) (.var 0)
-- An invalid source name may become active after substitution. Preserving
-- the old endpoint would fail, even before asking for the old empty schedule.
example : ¬ Nonempty (ParallelStep [[]] newlyCreated newlyCreated) := by
  rintro ⟨k⟩
  have R : BetaAt newlyCreated [] (.var 0) := ⟨.var 0,.var 0,rfl,rfl⟩
  have impossible := k.endpoint (singleContraction R)
  cases impossible
example (h : ParallelStep F t u) (σ : Nat → Term) (valid : SelectionValid t F) :
    ∃ k : ParallelStep F (subst σ t) (subst σ u),k.paths=h.paths :=
  h.substitute_exists σ valid
#print axioms Marked.StepAt.substitute
#print axioms Marked.ReductionAt.substitute
#print axioms ParallelStep.substitute_exists
#print axioms ParallelStep.substitution_residualSet_eq
#print axioms UsedSource.region_rename_reflect
#print axioms Atomic.region_rename_standard_project
#print axioms CompleteFamilyStep.maximal_of_common_ancestor
#print axioms MaxCopySet.complete_of_common_ancestor
end Lamping.Checks.Phase4SubstitutionReview

namespace Lamping.Checks.DisjointExtractionFixture
open Lamping.Lambda
example : ¬ Internal [.fn] (ParallelHistory.single (singleContraction S)) := by
  intro h
  obtain ⟨s,hs⟩ := h ([Step.arg] : Path) (by change ([Step.arg] : Path) ∈ ([[Step.arg]] : List Path); simp)
  cases hs
end Lamping.Checks.DisjointExtractionFixture


namespace Lamping.Checks.Phase4OccurrenceReview
open Lamping.Lambda
example (t : Term) (p q : Path) (hp : (subtermAt t p).isSome)
    (hq : (subtermAt t q).isSome) : p=q ∨ LeftOf p q ∨ LeftOf q p := compare_positions t p q hp hq
example (t : Term) : WellFounded (fun p q : RedexOcc t => LeftOf p.val q.val) := redex_left_wellFounded t
example : ¬LeftOf [Step.fn] [Step.body] := by intro h; cases h
example : ¬LeftOf [Step.body] [Step.fn] := by intro h; cases h
example (h : ParallelStep F t u) (k : ParallelStep G t u) (he : ∀p,p∈F↔p∈G) :
    PermEq (ParallelHistory.single h) (.single k) := PermEq.selection h k he
example (h : Derivation t u) : ∃ρ : ParallelHistory t u, Atomic ρ ∧ ρ.derivation=h := h.atomic
#print axioms compare_positions
#print axioms leftmost_selected_exists
#print axioms LeftOf.rank_lt
#print axioms redex_left_wellFounded
#print axioms PermEq.selection
#print axioms Atomic.last
end Lamping.Checks.Phase4OccurrenceReview

namespace Lamping.Checks.Phase4LatestReview
open Lamping.AG Lamping.Graph Lamping.Lambda
example (a : Context) : ∃ xs, Context.normalise xs=xs ∧ Context.ofList xs=a ∧
    ∀ys, Context.normalise ys=ys → Context.ofList ys=a → ys=xs := a.canonical_representation
example {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} {root es} (h : ExpandedProperPath g root es) :
    ExpandedForward g es := h.forward
example (h : ParallelStep F t u) (k : ParallelStep G t v) (he : ∀p,p∈F↔p∈G) :
    u=v := h.endpoint_selection k he
example (r : ExtractionRun m) (hr : 0<r.rank) :
    ∃s, Extraction r s ∧ ExtractionNormal s ∧ 0<s.rank := extraction_normal_exists_positive r hr
#print axioms Context.canonical_representation
#print axioms ExpandedProperPath.forward
#print axioms ParallelStep.endpoint_selection
#print axioms extraction_normal_exists_positive
#print axioms CompleteFamilyStep.maximal
end Lamping.Checks.Phase4LatestReview
namespace Lamping.Checks.Phase4CompletePrefixReview
open Lamping.Lambda
def D : Term := .lam (.app (.var 0) (.var 0))
def O : Term := .app D D
def step : BetaAt O [] O := ⟨.app (.var 0) (.var 0),D,rfl,rfl⟩
def r : RedexOcc O := ⟨[],_,rfl,trivial⟩
theorem complete_step : CompleteFamilyStep (ParallelHistory.nil O) (singleContraction step) := by
  constructor
  · intro p hp
    have he := List.mem_singleton.mp hp
    subst p
    exact r.property
  · refine ⟨r,List.mem_singleton_self _,?_⟩
    intro s
    have hs := (mem_redexPositions O s.val).mpr s.property
    have hr : redexPositions O = [[]] := by decide
    rw [hr] at hs
    have he : s = r := Subtype.ext (List.mem_singleton.mp hs)
    subst s
    exact ⟨fun _ => FamilyEq.refl _,fun _ => List.mem_singleton_self _⟩
example : CompleteDerivation (ParallelHistory.single (singleContraction step)) :=
  .step (.nil O) complete_step
example : IsRedex O := by trivial
example : Closed O := by simp [O,D,Closed,Scoped]
#print axioms complete_step
end Lamping.Checks.Phase4CompletePrefixReview

namespace Lamping.Checks.Phase4ContextualBetaReview
open Lamping.Lambda
example (hp : subtermAt t pre=some a) (h : BetaAt a q b) :
    ∃t', BetaAt t (pre++q) t' ∧ subtermAt t' pre=some b ∧ replaceAt t pre b=some t' :=
  h.prefix_lift hp
example (h : BetaAt (rename ρ t) p v) : ∃u, BetaAt t p u ∧ rename ρ u=v := h.rename_reflect
-- Noninjective free-variable renaming still reflects the contraction shape.
example : ∃u, BetaAt (.app (.lam (.var 0)) (.var 1)) [] u ∧ rename (fun _ => 0) u=.var 0 := by
  apply BetaAt.rename_reflect (ρ:=fun _ => 0)
  exact ⟨.var 0,.var 0,rfl,rfl⟩
#print axioms BetaAt.prefix_lift
#print axioms BetaAt.prefix_reflect
#print axioms BetaAt.rename_reflect
end Lamping.Checks.Phase4ContextualBetaReview

namespace Lamping.Checks.Phase4DeepArgumentReview
open Lamping.Lambda
def I : Term := .lam (.var 0)
def arg : Term := .app I (.var 0)
def body : Term := .lam (.app (.var 1) (.var 0))
def source : Term := .app (.lam body) arg
def afterOuter : Term := .lam (.app (.app I (.var 1)) (.var 0))
def afterCopy : Term := .lam (.app (.var 1) (.var 0))
def R : BetaAt source [] afterOuter := ⟨body,arg,rfl,rfl⟩
def S : BetaAt afterOuter [.body,.fn] afterCopy := ⟨.var 0,.var 1,rfl,rfl⟩
example : subtermAt (contract body arg) [.body,.fn] = some (.app I (.var 1)) := rfl
example : ¬ArgumentOccurrence body [.body,.arg] := by
  simp [ArgumentOccurrence,body,subtermAt,binderDepth]
example : ∃ (w : Term) (σ' : ParallelHistory source w), Atomic σ' ∧
    ∃ lift : ArgumentLift R (ParallelHistory.single (singleContraction S)) σ',
      lift.occurrence=[.body,.fn] := by
  apply argument_lift_exists R rfl (show ArgumentOccurrence body [.body,.fn] from rfl)
  intro q hq
  change q ∈ [[.body,.fn]] at hq
  have he := List.mem_singleton.mp hq
  subst q
  exact ⟨[],rfl⟩
#print axioms argument_copy
#print axioms BetaHistory.rename_reflect
#print axioms argument_lift_exists
end Lamping.Checks.Phase4DeepArgumentReview

namespace Lamping.Checks.Phase4ArgumentScopeReview
open Lamping.Lambda
open Lamping.Checks.Phase4DeepArgumentReview

def old : RedexOcc source := ⟨[.arg],by exact ⟨arg,rfl,True.intro⟩⟩

-- Under a surviving lambda the copied old argument is shifted, while the
-- inner var 0 leaf is excluded from argument occurrences.
example : ∃ z : RedexOcc afterOuter, z.val=[.body,.fn] ∧
    (singleContraction R).derivation.Residual old z := by
  exact R.argument_residual_exists rfl old rfl (show ArgumentOccurrence body [.body,.fn] from rfl)

example (r : RedexOcc t) (R : BetaAt t p u)
    (lookup : subtermAt t p=some (.app (.lam b) a))
    (source : r.val=(p++[.arg])++q) (z : RedexOcc u) :
    (singleContraction R).derivation.Residual r z ↔
      ∃ occ, ArgumentOccurrence b occ ∧ z.val=(p++occ)++q :=
  R.argument_residual_iff lookup r source z

#print axioms BetaAt.argument_residual_source
#print axioms BetaAt.argument_residual_exists
#print axioms BetaAt.argument_residual_iff
#print axioms ArgumentOccurrence.context_disjoint

def beforeRoot : BetaAt source [.arg] (.app (.lam body) (.var 0)) :=
  ⟨.var 0,.var 0,rfl,rfl⟩
example : ∃ a' ps,
    subtermAt (.app (.lam body) (.var 0)) []=some (.app (.lam body) a') ∧
    BetaHistory ps arg a' ∧
    (ParallelHistory.single (singleContraction beforeRoot)).derivation.paths=
      ps.map (fun q => ([.arg] : Path)++q) := by
  apply (ParallelHistory.single (singleContraction beforeRoot)).argument_head_preserved rfl
  intro q hq
  change q∈[[.arg]] at hq
  cases List.mem_singleton.mp hq
  exact ⟨[],rfl⟩

#print axioms ParallelStep.paths_apart
#print axioms ParallelStep.selected_factor_apart
#print axioms ParallelStep.pull_inside_step
#print axioms Atomic.pull_inside_step
#print axioms ApartHistory.pull_inside
#print axioms ApartHistory.inside_survives
#print axioms SyntaxFrame.history_reflect
#print axioms ParallelHistory.argument_head_preserved
#print axioms ParallelHistory.argument_root_residual_iff
#print axioms ParallelHistory.argument_root_exists
#print axioms ArgumentLift.singleton_residual
#print axioms residual_argument_target_unique
#print axioms Marked.markAt_rename
#print axioms Marked.ReductionAt.rename
#print axioms Marked.History.rename
#print axioms Derivation.rename_residual_iff
end Lamping.Checks.Phase4ArgumentScopeReview


namespace Lamping.Checks.Phase4PrincipalRouteReview
open Lamping.AG Lamping.Graph
example {V : Type} {p : Pairing (Bool ⊕ (V × Bool))}
    (h : InternalReach p (.inl false) (.inl true)) : PrincipalRoute p (.inl true) := h.principal_route
example {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
    {kept : K → Label signature} (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V)) :
    Nonempty (BetaEdge site.net) := site.betaEdge_exists
#print axioms InternalReach.principal_route
#print axioms PrincipalRoute.realize
#print axioms PathSite.internalEnd_wire
#print axioms PathSite.betaEdge_exists
end Lamping.Checks.Phase4PrincipalRouteReview

namespace Lamping.Checks.Phase4InitialFlowReview
open Lamping.AG Lamping.Graph Lamping.Lambda
example (t : Term) (n : Nat) :
    ∃vp : (encode n t).W→Bool, FlowOn (encode n t).net initialBoundaryPolarity vp := encode_flow t n
example (t : Term) (n : Nat) (es : List (Endpoint (encode n t).net))
    (rooted : es.head?=some (.inr (.inl (.inl ())))) (h : ProperPath (encode n t).net es) :
    Forward (encode n t).net es := encode_root_forward t n es rooted h
example {i : Nat} {p q : Port .garbage} {a b : Context} : ¬Traversal i .garbage p q a b := by
  intro h; cases h with
  | direct h => cases h
  | inverse h => cases h
#print axioms encode_flow
#print axioms encode_root_initial
#print axioms encode_root_forward
end Lamping.Checks.Phase4InitialFlowReview

namespace Lamping.Checks.Phase4OriginsReview
open Lamping.Lambda
example (h : Derivation t u) (r s : RedexOcc t) (q : RedexOcc u)
    (hr : h.Residual r q) (hs : h.Residual s q) : r=s := h.residual_unique_source r s q hr hs
example : Marked.SingleTags (.app [] (.lam (.var 0)) (.var 0)) := by trivial
example : Marked.tagsAt (.app [] (.lam (.var 0)) (.var 0)) [] = [] := rfl
#print axioms Marked.History.singleTags
#print axioms Marked.mem_tagsAt
#print axioms Derivation.residual_unique_source
end Lamping.Checks.Phase4OriginsReview

namespace Lamping.Checks.Phase4OffsetZeroReview
open Lamping.AG Lamping.Graph Lamping.Lambda
def term : Term := .lam (.app (.var 0) (.var 0))
abbrev g := (encode 0 term).net
def lamN : (encode 0 term).N := .inl ()
def appN : (encode 0 term).N := .inr (.inl (.inl ()))
def croN : (encode 0 term).N := .inr (.inr (.inl ()))
def fanN : (encode 0 term).N := .inr (.inl (.inr (.inr ⟨⟨0,rfl⟩,rfl⟩)))
def wRoot : (encode 0 term).W := .inr (.inl ())
def wFnRoot : (encode 0 term).W := .inl (.inr (.inr (.inl (.inl ()))))
def wFnFV : (encode 0 term).W := .inl (.inr (.inr (.inl (.inr ⟨0,rfl⟩))))
def wLamFV : (encode 0 term).W := .inr (.inr ⟨0,Or.inl rfl⟩)
def B : Context := Context.empty.cons (.o .empty)
def es : List (Endpoint g) := [
  .inl ⟨lamN,lamBody⟩,
  .inr (.inr (wRoot,true)),
  .inl ⟨appN,.inl ()⟩,
  .inr (.inr (wFnRoot,true)),
  .inl ⟨croN,.inl ()⟩,
  .inr (.inr (wFnFV,false)),
  .inl ⟨fanN,.inl ()⟩,
  .inr (.inr (wLamFV,false))]
theorem labels : Labelling g es Context.empty B := by
  apply Labelling.cons (LabelledTurn.transparent (g:=g) wRoot false Context.empty)
  apply Labelling.cons (LabelledTurn.node (g:=g) appN appCtx (.inl ()) (.direct (.appFun _)))
  apply Labelling.cons (LabelledTurn.transparent (g:=g) wFnRoot false Context.empty)
  apply Labelling.cons (LabelledTurn.node (g:=g) croN (.inr ()) (.inl ()) (.direct (by
    simpa using Passage.cro (i:=0) Context.empty Context.empty)))
  apply Labelling.cons (LabelledTurn.transparent (g:=g) wFnFV true Context.empty)
  apply Labelling.cons (LabelledTurn.node (g:=g) fanN fanO (.inl ()) (.direct (by
    simpa [B] using Passage.fanO (i:=0) Context.empty Context.empty Level.empty)))
  apply Labelling.cons (LabelledTurn.transparent (g:=g) wLamFV true B)
  exact .single _ _
example : es.head?=some (.inl ⟨lamN,lamBody⟩) := rfl
example : es.getLast?=some (g.wire (.inl ⟨lamN,lamBind⟩)) := rfl
example : (g.label lamN).index = 0 := rfl
example : B.get 0 = .o .empty := rfl
example : B ≠ Context.empty.replace 0 (Context.empty.cons .empty) := by
  intro h; have hh := congrArg (fun a : Context => a.get 0) h; cases hh
end Lamping.Checks.Phase4OffsetZeroReview


namespace Lamping.Checks.Phase4ProtectedOccurrenceReview
open Lamping.Lambda
-- An inserted lambda's own zero is not the protected surrounding binder.
example : ¬ ArgumentOccurrence
    (subst (liftSub (fun _ => Term.lam (.var 0))) (.var 1)) [.body] := by
  change ¬ (some (Term.var 0) = some (.var 1))
  decide
-- The protected outer variable remains the same literal occurrence under a binder.
example (σ : Nat → Term) : ArgumentOccurrence
    (subst (liftSub σ) (.lam (.app (.var 1) (.var 2)))) [.body,.fn] := rfl
example (σ : Nat → Term)
    (h : ArgumentOccurrence (subst (liftSub σ) b) occurrence) :
    ArgumentOccurrence b occurrence := h.subst_reflect
#check BetaAt.function_argument_occurrence_reflect
#print axioms subst_protected_occurrence_reflect
#print axioms ArgumentOccurrence.subst_reflect
#print axioms BetaAt.function_argument_occurrence_reflect
#print axioms PermEq.projection_coherence
#print axioms PermEq.cancel_beta_head
#print axioms Copy.cancel_beta_head
end Lamping.Checks.Phase4ProtectedOccurrenceReview

namespace Lamping.Checks.Phase4LatestInterfacesReview
open Lamping.Lambda

-- The strengthened output is genuinely constructed ordinary history; neither
-- atomicity nor standardness is required of the input parallel schedule.
example (ρ : ParallelHistory t u) :
    ∃ σ : ParallelHistory t u, Atomic σ ∧ Standard σ ∧ PermEq ρ σ :=
  atomic_standardization_exists ρ

example (ρ : ParallelHistory t u) (σ : ParallelHistory u v)
    (h : Standard (ρ.append σ)) : Standard ρ ∧ Standard σ :=
  ⟨h.prefix,h.suffix⟩

example (h : Extraction r s) (inside : Internal site r.history) :
    Internal site s.history := h.internal inside

#print axioms atomic_standardization_exists
#print axioms Standard.prefix
#print axioms Standard.suffix
#print axioms StepProjection.internal_reflect
#print axioms ExtractionStep.internal
#print axioms Extraction.internal
#print axioms Atomic.append_iff
#print axioms StepProjection.split_bottom
#print axioms Atomic.split_mapped_program
#print axioms StepProjection.extraction_prefix
#print axioms function_residual_pullback
#print axioms extraction_function_residual_prefixed_peak
#print axioms extraction_function_residual_long_peak
#print axioms disjoint_residual_pullback
#print axioms extraction_disjoint_residual_prefixed_peak
#print axioms extraction_disjoint_residual_long_peak
#print axioms ArgumentLift.split_prefix
#print axioms Derivation.region_rename_target
#print axioms Derivation.region_rename_residual_iff
#print axioms extraction_argument_residual_long_peak
#print axioms normal_no_old_last
#print axioms DoesNotReturnLeft.append_last
#print axioms normal_standard_append
#print axioms canonical_of_normal_prefix
end Lamping.Checks.Phase4LatestInterfacesReview

namespace Lamping.Checks.Phase4EmptyMaxCopyReview
open Lamping.Lambda
def source : Term := .app (.lam (.var 0)) (.var 0)
def R : BetaAt source [] (.var 0) := ⟨.var 0,.var 0,rfl,rfl⟩
def history := ParallelHistory.single (singleContraction R)
private theorem no_target_redex (r : RedexOcc (.var 0)) : False := by
  have mem := (mem_redexPositions (.var 0) r.val).mpr r.property
  exact List.not_mem_nil mem
private theorem source_redex_path (r : RedexOcc source) : r.val=[] := by
  have mem := (mem_redexPositions source r.val).mpr r.property
  exact List.mem_singleton.mp mem
theorem prefix_complete : CompleteDerivation history := by
  apply CompleteDerivation.step (.nil source)
  constructor
  · intro p hp
    cases List.mem_singleton.mp hp
    exact R.redex
  · refine ⟨⟨[],R.redex⟩,by simp,?_⟩
    intro s
    constructor
    · intro _
      have same : s=⟨[],R.redex⟩ := Subtype.ext (source_redex_path s)
      cases same
      exact .refl _
    · intro _
      exact List.mem_singleton.mpr (source_redex_path s)
theorem empty_copy_set : CopySet history [] := by
  refine ⟨?_,⟨⟨source,.nil source,⟨[],R.redex⟩⟩,history,.refl _,?_⟩⟩
  · intro p hp; cases hp
  · intro r; exact False.elim (no_target_redex r)
theorem empty_max_copy_set : MaxCopySet history [] := by
  refine ⟨empty_copy_set,?_⟩
  intro G hG _ p hp
  exact False.elim (no_target_redex ⟨p,hG.1 p hp⟩)
def emptyStep : ParallelStep [] (.var 0) (.var 0) :=
  ⟨[],.var 0,(Marked.completeOld_iff _ _).mpr ⟨.nil _,True.intro⟩,rfl⟩
theorem empty_not_complete_family : ¬CompleteFamilyStep history emptyStep := by
  intro h
  exact h.nonempty rfl
#print axioms prefix_complete
#print axioms empty_max_copy_set
#print axioms empty_not_complete_family
end Lamping.Checks.Phase4EmptyMaxCopyReview

namespace Lamping.Checks.Phase4ParallelPrefixReview
open Lamping.Lambda
def invalidGlobal : ParallelStep [[.fn,.fn]] (.app (.var 0) (.var 0)) (.app (.var 0) (.var 0)) :=
  ⟨[],.app [] (.var 0) (.var 0),(Marked.completeOld_iff _ _).mpr ⟨.nil _,by trivial⟩,rfl⟩
example : ∃ b, ∃ k : ParallelStep [[.fn]] (.var 0) b,
    subtermAt (.app (.var 0) (.var 0)) [.fn]=some b ∧
      invalidGlobal.paths=k.paths.map (fun q => [.fn]++q) :=
  invalidGlobal.prefix_scope (pre:=[.fn]) (G:=[[.fn]]) rfl
#print axioms ParallelStep.prefix_scope
#print axioms ParallelStep.paths_scope
end Lamping.Checks.Phase4ParallelPrefixReview

namespace Lamping.Checks.DisjointExtractionFixture
open Lamping.Lambda
def rightThenLeft := (ParallelHistory.single (singleContraction S)).append (.single (singleContraction RS))
theorem rightThenLeft_not_standard : ¬Standard rightThenLeft := by
  intro h
  change Standard (.cons (singleContraction S) (.single (singleContraction RS))) at h
  cases h with
  | cons step r selected noReturn tail =>
    have rpath : r.val=[.arg] := List.mem_singleton.mp selected.1
    have before : LeftOf ([.fn] : Path) r.val := by rw [rpath]; exact .branch [] []
    apply noReturn ⟨[.fn],R.redex⟩ before (.single (singleContraction S))
      (singleContraction RS) (.nil W) rfl ⟨[.fn],RS.redex⟩ (leftmost_singleton _)
    exact ((singleContraction S).residual_iff _ _).mpr (by decide)
example : ∃ σ, Standard σ ∧ PermEq rightThenLeft σ := standardization_exists rightThenLeft
def pointedRun : ExtractionRun T := .of rightThenLeft ((Atomic.single S).append (.single RS))
theorem pointedRun_prefix_standard : PrefixStandard pointedRun := by
  refine ⟨⟨V,.single (singleContraction S),⟨[.fn],RS.redex⟩⟩,?_,?_⟩
  · exact ⟨RS,.single S,rfl⟩
  · exact Standard.single_step _ ⟨[.arg],S.redex⟩ (leftmost_singleton _)
-- Two copies of a surviving old name retain their literal order, while an
-- invalid old name contributes nothing after actual context lifting.
example : ∃ u, ∃ H : ParallelStep [[.body,.fn]] (.lam T) u,
    H.residualSet [[.body,.arg],[.body,.arg],[.body,.body]]=
      [[.body,.arg],[.body,.arg]] := by
  obtain ⟨u,H,_,paths⟩ := (singleContraction R).prefix_lift (pre:=[.body]) (t:=.lam T) rfl
  refine ⟨u,H,?_⟩
  calc
    _ = ((singleContraction R).residualSet [[.arg],[.arg],[.body]]).map
        (fun q => [.body]++q) :=
      (singleContraction R).residualSet_prefix_eq H rfl paths [[.arg],[.arg],[.body]]
    _ = _ := rfl
#print axioms Marked.trace_eq_of_members
#print axioms Marked.subtree_trace_eq
#print axioms ParallelStep.trace_prefix_eq
#print axioms ParallelStep.residualSet_prefix_eq
-- A standard pointed prefix need not make the full history standard.
-- Normality in canonical_of_normal_prefix is therefore essential.
example : ¬ExtractionNormal pointedRun := by
  intro normal
  exact rightThenLeft_not_standard (canonical_of_normal_prefix normal pointedRun_prefix_standard).2.1
-- This input has a standard pointed prefix and a nonstandard full run.
-- The canonical-extraction existence API must accept exactly that scope.
example : ∃ s, Extraction pointedRun s ∧ CanonicalRun s :=
  canonical_extraction_exists pointedRun_prefix_standard
example : Extraction pointedRun (.of (.single (singleContraction R)) (.single R)) := by
  apply (Atomic.single S).extract_initial_residual ⟨[.fn],R.redex⟩ RS _ R
  exact ((singleContraction S).residual_iff _ _).mpr (by decide)
#print axioms Atomic.extract_initial_residual
#print axioms Copy.initial_extraction
#print axioms Copy.source_head_deleted
#print axioms Copy.head_order
#print axioms Copy.protected_target_head
#print axioms RightHistory.left_pointed_ancestor
#print axioms Copy.common_of_left_pointed
#print axioms Copy.ne_protected_target_head
#print axioms Atomic.app_first_fn
#print axioms Atomic.app_arg_stays
#print axioms Atomic.standard_app_blocks
#print axioms Atomic.standard_internal_reflect
#print axioms DisjointBlocks.mapped
#print axioms ProtectedBlocks.mapped
#print axioms Atomic.standard_root_blocks
#print axioms Atomic.standard_internal_right_reflect
#print axioms ProtectedBlocks.append_disjoint
#print axioms Atomic.standard_protected_blocks
#print axioms ParallelStep.eq_of_paths
#print axioms StepProjection.last_congr
#print axioms Atomic.apart_pointed_ancestor
#print axioms Atomic.extract_apart_suffix
#print axioms ProtectedBlocks.extract_function_pointed
#print axioms Atomic.disjoint_row_pullback
#print axioms Atomic.extract_disjoint_prefix
#print axioms ProtectedBlocks.extract_argument_pointed
#print axioms LeftOf.right_sibling
#print axioms Atomic.extract_local_program
#print axioms RightHistory.extract_right_pointed
#print axioms ParallelStep.rename
#print axioms ParallelStep.rename_residualSet
#print axioms StepProjection.rename
#print axioms occurrenceRenaming_binder_iff
#print axioms ArgumentLift.rename
#print axioms ExtractionStep.rename
#print axioms Extraction.rename
#print axioms UsedSource.region_rename
#print axioms Atomic.region_rename_standard_reflect
#print axioms argument_used_inclusion
#print axioms UsedSource.cons_iff
#print axioms UsedSource.common_prefix
#print axioms Standard.replace_suffix_used
#print axioms ArgumentLift.prefix_standard
#print axioms ExtractionStep.prefix_standard
#print axioms Extraction.prefix_standard
#print axioms canonical_extraction_exists
#check standardization_exists
#print axioms RightHistory.permutation
#print axioms ParallelHistory.extract_minimal
#print axioms HistoryCost.wellFounded
#print axioms standardization_exists
#print axioms rightThenLeft_not_standard
end Lamping.Checks.DisjointExtractionFixture

namespace Lamping.Checks.Phase4ArgumentNoDirectCopyReview
open Lamping.Lambda
#print axioms Atomic.split_at
#print axioms Atomic.prefix_alignment
#print axioms Atomic.prefix_comparable
#print axioms ExtractionRun.ext_paths
#print axioms StepProjection.split_append
end Lamping.Checks.Phase4ArgumentNoDirectCopyReview

namespace Lamping.Checks.Phase4DisjointPeakReview
open Lamping.Lambda
#print axioms extraction_disjoint_residual_peak
end Lamping.Checks.Phase4DisjointPeakReview

namespace Lamping.Checks.Phase4FunctionPeakReview
open Lamping.Lambda
#print axioms creation_predecessor_pullback
#print axioms singleton_projection_row
#print axioms StepProjection.final_selection
#print axioms extraction_function_residual_peak
end Lamping.Checks.Phase4FunctionPeakReview

namespace Lamping.Checks.Phase4StandardCreationReview
open Lamping.Lambda
#print axioms LeftOf.no_between_fn
#print axioms BetaAt.redex_reflect_before
#print axioms StepProjection.head_square
end Lamping.Checks.Phase4StandardCreationReview

namespace Lamping.Checks.FunctionExtractionFixture
open Lamping.Lambda
example : ∃ (w : Term) (G : List Path) (projected : ParallelHistory U w)
    (last : ParallelStep G U w), Atomic projected ∧
    StepProjection (singleContraction R) (.single (singleContraction S)) projected last := by
  apply (Atomic.single S).function_projection R
  intro q hq
  change q∈[[.fn,.body]] at hq
  have he := List.mem_singleton.mp hq
  subst q
  exact ⟨[.body],rfl⟩
#print axioms BetaAt.function_residualSet_singleton
#print axioms BetaAt.outside_residualSet_singleton
#print axioms ParallelStep.eq_single_contraction
#print axioms Atomic.disjoint_projection
#print axioms Atomic.function_projection
-- The final vertical singleton is recovered from the actual row and source
-- scope; no Atomic witness for its bottom horizontal history is supplied.
example : ([[]] : List Path)=[[]] := by
  apply row.final_selection_singleton (site:=[.fn]) rfl ⟨[],R.redex⟩ rfl (.single S)
  · intro p hp
    change p∈[[.fn,.body]] at hp
    cases List.mem_singleton.mp hp
    exact ⟨[.body],rfl⟩
  · rintro ⟨p,hp⟩
    cases hp
#print axioms ParallelStep.residualSet_eq_of_paths
#print axioms StepProjection.final_selection_singleton
example : ∃ (U V W : Term) (H : ParallelStep [[.body]] (.lam T) U)
    (top : ParallelHistory (.lam T) V) (bottom : ParallelHistory U W)
    (last : ParallelStep [[.body]] V W),
    StepProjection H top bottom last ∧ Atomic top ∧ Atomic bottom := by
  obtain ⟨U,V,W,H,top,bottom,last,hr,_,_,_,_,_,_,_,ha,hb⟩ :=
    row.prefix_lift (pre:=[.body]) (T:=.lam T) rfl
  exact ⟨U,V,W,H,top,bottom,last,hr,ha (.single S),hb (.single SR)⟩
#print axioms SyntaxFrame.liftStep_residualSet
#print axioms SyntaxFrame.liftProjection
#print axioms SyntaxContext.of_lookup
#print axioms SyntaxContext.liftProjection
#print axioms StepProjection.prefix_lift
def arbitraryNames : Marked :=
  .app [[.arg],[.arg]] (.lam (.app [[.arg]] (.lam (.var 0)) (.var 0))) (.lam (.var 0))
-- Repeated names unrelated to positions are deliberately accepted; this is
-- physical-position activity selection, not old-name reselection.
example : ∃ target : Marked,
    Marked.History ((singleContraction R).derivation.append
      (ParallelHistory.single (singleContraction SR)).derivation).paths arbitraryNames.passive target ∧
    Marked.History ((ParallelHistory.single (singleContraction S)).derivation.append
      (singleContraction RS).derivation).paths arbitraryNames.passive target :=
  row.passive_tracking_diamond arbitraryNames rfl
#print axioms Marked.selectPositionsAt_skeleton
#print axioms Marked.selectPositionsAt_passive
#print axioms ParallelMovesSquare.passive_tracking_diamond
#print axioms StepProjection.passive_tracking_diamond
example : Standard ((ParallelHistory.single (singleContraction R)).append
    (.single (singleContraction SR))) ∧ Standard (.single (singleContraction SR)) := by
  apply (Atomic.single S).function_projection_standard R _ row (.single SR)
    (Standard.single_step _ ⟨[.fn,.body],S.redex⟩ (leftmost_singleton _))
  intro q hq
  change q∈[[.fn,.body]] at hq
  cases List.mem_singleton.mp hq
  exact ⟨[.body],rfl⟩
#print axioms UsedSource.region_project_reflect
#print axioms BetaAt.region_left_reflect
#print axioms Atomic.region_standard_project
#print axioms Atomic.function_projection_standard
#print axioms StepProjection.disjoint_paths
#print axioms disjoint_tail_peak
end Lamping.Checks.FunctionExtractionFixture

namespace Lamping.Checks.Phase4CompletePrefixReview
open Lamping.Lambda
-- Omega has the same beta endpoint, while the *old selected set* is consumed.
example (e : Nat → Nat) :
    Marked.weight e (Marked.mark ((singleContraction step).residualSet [[]]) O) <
      Marked.weight e (Marked.mark [[]] O) :=
  step.selected_residual_weight_lt (by decide) e
#print axioms Marked.weight_skeleton
#print axioms BetaAt.selected_residual_weight_lt
end Lamping.Checks.Phase4CompletePrefixReview

namespace Lamping.Checks.Phase4TraceNoDupReview
open Lamping.Lambda
-- Repeating an annotation name does not repeat an occurrence path.
example : Marked.tracePositions [] (.app [[],[]] (.var 0) (.var 0))=[[]] := rfl
example : (Marked.tracePositions [] (.app [[],[]] (.var 0) (.var 0))).Nodup :=
  Marked.tracePositions_nodup _ _
#print axioms Marked.tracePositions_nodup
#print axioms Marked.trace_singleton_of_members
#print axioms Marked.initial_trace_singleton
#print axioms Marked.initial_trace_singleton_at
end Lamping.Checks.Phase4TraceNoDupReview

namespace Lamping.Checks.Phase4ArgumentNoDirectCopyReview
open Lamping.Lambda
def I : Term := .lam (.var 0)
def B : Term := .app I (.var 0)
def A : Term := .app I B
def body : Term := .app (.var 0) (.var 0)
def source : Term := .app (.lam body) A
def afterR : Term := .app A A
def originalTerm : Term := .app (.lam body) B
def copyTerm : Term := .app B A
def R : BetaAt source [] afterR := ⟨body,A,rfl,rfl⟩
def O : BetaAt source [.arg] originalTerm := ⟨.var 0,B,rfl,rfl⟩
def L : BetaAt afterR [.fn] copyTerm := ⟨.var 0,B,rfl,rfl⟩
def S : BetaAt copyTerm [.fn] (.app (.var 0) A) := ⟨.var 0,.var 0,rfl,rfl⟩
def OS : BetaAt originalTerm [.arg] (.app (.lam body) (.var 0)) := ⟨.var 0,.var 0,rfl,rfl⟩
def originalPrefix := ParallelHistory.single (singleContraction O)
def copyPrefix := (ParallelHistory.single (singleContraction R)).append (.single (singleContraction L))
def original : RedexWithHistory source := ⟨originalTerm,originalPrefix,⟨[.arg],OS.redex⟩⟩
def copied : RedexWithHistory source := ⟨copyTerm,copyPrefix,⟨[.fn],S.redex⟩⟩
def rootOld : RedexOcc source := ⟨[],R.redex⟩
def argumentOld : RedexOcc source := ⟨[.arg],O.redex⟩
def innerOld : RedexOcc source := ⟨[.arg,.arg],by exact ⟨B,rfl,trivial⟩⟩
private theorem selected_consumed (h : ParallelStep F t u) (r : RedexOcc t)
    (selected : r.val∈F) (s : RedexOcc u) : ¬h.derivation.Residual r s := by
  intro hs
  have mem := (Marked.mem_setResidualPositions F h.markedTarget s.val).mpr
    ⟨r.val,selected,(h.residual_iff r s).mp hs⟩
  rw [h.complete.2] at mem
  exact List.not_mem_nil mem
private theorem no_copy_of_spent (a b : RedexWithHistory m) (r : RedexOcc m)
    (spent : ∀ s, ¬a.history.derivation.Residual r s)
    (q : RedexOcc b.target) (alive : b.history.derivation.Residual r q) : ¬Copy a b := by
  rintro ⟨tail,perm,_⟩
  have total := (perm.residual r q).mpr alive
  rw [ParallelHistory.derivation_append,Derivation.residual_append] at total
  obtain ⟨s,hs,_⟩ := total
  exact spent s hs
theorem original_not_copy : ¬Copy original copied := by
  apply no_copy_of_spent original copied argumentOld
    (fun s hs => selected_consumed (singleContraction O) argumentOld (by decide) s hs)
    ⟨[.arg],by exact ⟨A,rfl,trivial⟩⟩
  apply (Derivation.residual_append _ _ _ _).mpr
  refine ⟨⟨[.arg],by exact ⟨A,rfl,trivial⟩⟩,?_,?_⟩
  · exact ((singleContraction R).residual_iff _ _).mpr (by decide)
  · exact ((singleContraction L).residual_iff _ _).mpr (by decide)
theorem copied_not_copy : ¬Copy copied original := by
  refine no_copy_of_spent copied original rootOld ?_ ⟨[],by exact ⟨originalTerm,rfl,trivial⟩⟩ ?_
  · intro s hs
    obtain ⟨middle,first,_⟩ := (Derivation.residual_append _ _ rootOld s).mp hs
    exact selected_consumed (singleContraction R) rootOld (by decide) middle first
  · exact ((singleContraction O).residual_iff _ _).mpr (by decide)
theorem same_family : FamilyEq original copied := by
  apply FamilyEq.trans (FamilyEq.symm ((initial_family_iff innerOld original).mpr ?_))
    ((initial_family_iff innerOld copied).mpr ?_)
  · exact ((singleContraction O).residual_iff _ _).mpr (by decide)
  · apply (Derivation.residual_append _ _ _ _).mpr
    refine ⟨⟨[.fn,.arg],by exact ⟨B,rfl,trivial⟩⟩,?_,?_⟩
    · exact ((singleContraction R).residual_iff _ _).mpr (by decide)
    · exact ((singleContraction L).residual_iff _ _).mpr (by decide)
def copyFull := (ParallelHistory.single (singleContraction L)).append (.single (singleContraction S))
def originalFull := originalPrefix.append (.single (singleContraction OS))
def actualLift : ArgumentLift R copyFull originalFull where
  body := body
  argument := A
  redex := rfl
  occurrence := [.fn]
  isVariable := rfl
  localPaths := [[],[]]
  copy_paths := rfl
  original_paths := rfl
  parallelization := StepProjection.exists_projection (singleContraction R) originalFull
def beforeRun : ExtractionRun source :=
  .of ((ParallelHistory.single (singleContraction R)).append copyFull)
    ((Atomic.single R).append ((Atomic.single L).append (.single S)))
def afterRun : ExtractionRun source := .of originalFull ((Atomic.single O).append (.single OS))
example : RunRepresents beforeRun copied :=
  ⟨S,(Atomic.single R).append (.single L),rfl⟩
example : RunRepresents afterRun original := ⟨OS,Atomic.single O,rfl⟩
theorem actual_argument_extraction : ExtractionStep beforeRun afterRun :=
  .argumentPart (.nil _) (.nil _) R copyFull ((Atomic.single L).append (.single S))
    originalFull ((Atomic.single O).append (.single OS)) (by decide) actualLift
-- Retain both hard non-Copy directions above; the new result constructs a
-- third pointed successor for this exact independently built nonlinear case.
theorem common_copy_successor : ∃ common : RedexWithHistory source,
    Copy original common ∧ Copy copied common := by
  apply actualLift.pointed_join ((Atomic.single L).append (.single S))
    ((Atomic.single O).append (.single OS)) (by decide) (.nil source) (.nil source)
    original copied
  · exact ⟨OS,Atomic.single O,rfl⟩
  · exact ⟨S,(Atomic.single R).append (.single L),rfl⟩
#print axioms Atomic.argument_projection_factor
#print axioms ArgumentLift.factor_projection
#print axioms ArgumentLift.parallelized_factor
#print axioms argument_pointed_join
#print axioms ArgumentLift.pointed_join
#print axioms ArgumentLift.pointed_family
#print axioms common_copy_successor
def outer : SyntaxContext := .frame .body (.frame (.arg (.lam (.var 0))) .hole)
example : ExtractionStep (outer.liftRun beforeRun) (outer.liftRun afterRun) :=
  outer.liftExtractionStep actual_argument_extraction
example : (outer.liftRun beforeRun).history.derivation.paths=
    [[.body,.arg],[.body,.arg,.fn],[.body,.arg,.fn]] := by
  rw [outer.liftRun_paths]
  rfl
#print axioms SyntaxContext.liftBeta
#print axioms SyntaxContext.liftStep_single_heq
#print axioms SyntaxContext.liftArgument
#print axioms SyntaxContext.liftExtractionStep
#print axioms SyntaxContext.liftExtraction
#print axioms SyntaxContext.liftExtractionJoin
#print axioms SyntaxContext.normal_of_lift
example : ∃ h : ParallelHistory source beforeRun.target,
    Atomic h ∧ (outer.liftRun beforeRun).history=outer.liftHistory h := by
  apply outer.reflectHistory_fixed _ (outer.liftAtomic beforeRun.atomic)
  intro q hq
  rw [outer.liftHistory_paths] at hq
  obtain ⟨localPath,_,rfl⟩ := List.mem_map.mp hq
  exact ⟨localPath,rfl⟩
#print axioms SyntaxContext.reflectStep
#print axioms SyntaxContext.reflectHistory
#print axioms SyntaxContext.reflectHistory_fixed
#print axioms SyntaxContext.reflectProjection
#print axioms SyntaxContext.reflectScopedProjection
example : ∃ q, ExtractionStep beforeRun q ∧ outer.liftRun afterRun=outer.liftRun q :=
  outer.reflectExtractionStep (outer.liftExtractionStep actual_argument_extraction)
#print axioms SyntaxContext.reflectRootExtraction
#print axioms SyntaxContext.reflectExtractionStep
#print axioms SyntaxContext.reflectExtraction
example : FamilyEq copied original :=
  actual_argument_extraction.family copied original
    ⟨S,(Atomic.single R).append (.single L),rfl⟩ ⟨OS,Atomic.single O,rfl⟩
#print axioms ExtractionStep.family
#print axioms Extraction.family
#print axioms common_extraction_family
#print axioms StepProjection.atomic_top_paths_unique
#print axioms StepProjection.atomic_top_run_unique
#print axioms ArgumentLift.head_residual
#print axioms ArgumentLift.copy_occurrence_unique
#print axioms ArgumentLift.original_run_unique
#print axioms ArgumentLift.no_region_projection
#print axioms DoesNotReturnLeft.no_used_left
#print axioms DoesNotReturnLeft.permutation
#print axioms Standard.replace_suffix_extension
#print axioms UsedSource.internal
#print axioms UsedSource.project_unique
#print axioms BetaAt.region_left_image
#print axioms Atomic.region_standard_reflect
#print axioms prefixStandard_append_last_iff
#print axioms residual_prefix_standard
#print axioms region_prefix_standard
#print axioms ExtractionStep.root_factor
#print axioms RootExtraction.target_unique
#print axioms RootExtraction.same_index_target_unique
#print axioms ExtractionStep.indexed_iff
#print axioms ExtractionAt.target_unique
#print axioms ExtractionAt.peak_join
#print axioms ExtractionAt.uncons
#print axioms ExtractionAt.strip_prefix
#print axioms ExtractionAt.strict_fork_factor
#print axioms RootExtraction.residual_tail_join
#print axioms GeneralCubeFront.bottom_coherence
#print axioms StepProjection.moves_coherence
#print axioms ExtractionStep.rename_reflect
#print axioms ExtractionStep.shift_reflect
#print axioms argument_tail_peak
#print axioms ParallelMovesSquare.singleton_residualSet
#print axioms ParallelStep.trace_source_valid
#print axioms ParallelStep.residualSet_redex
#print axioms ParallelStep.residualSet_compose_iff
#print axioms ParallelMovesSquare.composite_residualSet_members
#print axioms singleton_cube_back
#print axioms BetaAt.function_residual_coordinates
#print axioms BetaAt.function_disjoint_reflect
#print axioms BetaAt.function_internal_reflect
#print axioms extraction_function_region_peak
#print axioms StepProjection.region_head
#print axioms function_region_pullback_tile
#print axioms function_region_pullback
#print axioms function_region_site
#print axioms extraction_function_region_prefixed_peak
#print axioms extraction_function_region_long_peak
example (a : RedexWithHistory m) :
    ∃ (r : ExtractionRun m) (b : RedexWithHistory m),
      CanonicalRun r ∧ RunRepresents r b ∧ FamilyEq a b := a.canonical_exists
#print axioms RedexWithHistory.canonical_exists
#print axioms original_not_copy
#print axioms copied_not_copy
#print axioms same_family
#print axioms actual_argument_extraction
example : ∃ (v : Term) (pre : ParallelHistory afterR v)
    (post : ParallelHistory v (.app (.var 0) A)),
    Atomic pre ∧ Atomic post ∧ copyFull=pre.append post ∧ pre.length=1 :=
  ((Atomic.single L).append (.single S)).split_at 1 (by decide)
end Lamping.Checks.Phase4ArgumentNoDirectCopyReview

namespace Lamping.Checks.Phase4ExtractionLeafReview
open Lamping.Lambda
#print axioms StepProjection.singleton_residual
#print axioms residual_extraction_target_unique
#print axioms residual_extraction_peak_join
#print axioms residual_projection_peak_join
#print axioms ExtractionJoin.prepend
end Lamping.Checks.Phase4ExtractionLeafReview

namespace Lamping.Checks.Phase4StandardBaseReview
open Lamping.Lambda
def invalidSelection : ParallelStep [[.fn]] (.var 0) (.var 0) :=
  ⟨[],.var 0,(Marked.completeOld_iff _ _).mpr ⟨.nil _,by trivial⟩,rfl⟩
example : ∃ u, ∃ k : ParallelStep [[.body,.fn]] (.lam (.var 0)) u,
    subtermAt u [.body]=some (.var 0) ∧ k.paths=[] := by
  obtain ⟨u,k,lookup,paths⟩ := invalidSelection.prefix_lift (pre:=[.body]) (t:=.lam (.var 0)) rfl
  exact ⟨u,k,lookup,paths⟩
#print axioms SyntaxFrame.parallel_lift
#print axioms ParallelStep.prefix_lift
example : ∃ σ, Standard σ ∧ PermEq (.single invalidSelection) σ :=
  standardize_single invalidSelection
example : PermEq (.single invalidSelection) (.nil (.var 0)) := by
  apply PermEq.no_actual_selection invalidSelection
  intro r
  have mem := (mem_redexPositions (.var 0) r.val).mpr r.property
  have empty : redexPositions (.var 0)=[] := by decide
  rw [empty] at mem
  exact False.elim (List.not_mem_nil mem)
#print axioms Standard.single_step
#print axioms standardize_single
#print axioms ParallelStep.selected_factor
#print axioms BetaAt.left_residual_iff
#print axioms BetaAt.left_residual_exists
end Lamping.Checks.Phase4StandardBaseReview

namespace Lamping.Checks.Phase4ExtractionPrefixReview
open Lamping.Lambda
#print axioms ExtractionStep.prepend
#print axioms Extraction.prepend
#print axioms ExtractionNormal.of_prepend
end Lamping.Checks.Phase4ExtractionPrefixReview

namespace Lamping.Checks.Phase4GeneralCreationReview
open Lamping.Lambda
def I : Term := .lam (.var 0)
def A : Term := .app I I
def source : Term := .app (.lam (.app A A)) I
def left : Term := .app (.lam (.app I A)) I
def right : Term := .app (.lam (.app A I)) I
def target : Term := .app (.lam (.app I I)) I
def R : BetaAt source [.fn,.body,.fn] left := ⟨.var 0,I,rfl,rfl⟩
def S : BetaAt source [.fn,.body,.arg] right := ⟨.var 0,I,rfl,rfl⟩
def SR : BetaAt left [.fn,.body,.arg] target := ⟨.var 0,I,rfl,rfl⟩
def RS : BetaAt right [.fn,.body,.fn] target := ⟨.var 0,I,rfl,rfl⟩
def sq : ParallelMovesSquare [[.fn,.body,.fn]] [[.fn,.body,.arg]] source left right target :=
  ⟨singleContraction R,singleContraction S,singleContraction SR,singleContraction RS⟩
def T1 : RedexOcc left := ⟨[],by exact ⟨_,rfl,trivial⟩⟩
def T2 : RedexOcc right := ⟨[],by exact ⟨_,rfl,trivial⟩⟩
def T : RedexOcc target := ⟨[],by exact ⟨_,rfl,trivial⟩⟩
-- Both contractions are below fn/body, while the pointed final redex is the
-- outer root: this exercises the common-context outside-target case.
example : ∃ T0 : RedexOcc source,
    ((singleContraction R).derivation.append sq.afterFirst.derivation).Residual T0 T := by
  apply creation_separation R S (by decide) sq.afterFirst sq.afterSecond T1 T2 T
  · exact (SR.outside_residual_iff T1 (by rintro ⟨q,h⟩; cases h) T).mpr rfl
  · exact (RS.outside_residual_iff T2 (by rintro ⟨q,h⟩; cases h) T).mpr rfl
#print axioms Derivation.prefix_residual_iff
#print axioms ParallelStep.residualSet_prefix_members
#print axioms ParallelStep.app_left_scope
#print axioms creation_separation_outside_prefix
#print axioms SyntaxFrame.creation_separation
#print axioms creation_separation
#print axioms creation_common_ancestor
#print axioms creation_residual_intersection
#print axioms creation_common_ancestor_unique
end Lamping.Checks.Phase4GeneralCreationReview

namespace Lamping.Checks.FunctionExtractionFixture
open Lamping.Lambda
example : ∃ a b : RedexWithHistory T,
    RunRepresents (.of ((ParallelHistory.nil T).append (.single (singleContraction S)))
      ((Atomic.nil T).append (.single S))) a ∧
    RunRepresents (.of (((ParallelHistory.nil T).append (.single (singleContraction R))).append
      (.single (singleContraction SR))) (((Atomic.nil T).append (.single R)).append (.single SR))) b ∧
    Copy a b := row.pointed_copy R (.single S) (.single SR) (by decide) (.nil T) (.nil T)
#print axioms StepProjection.split_last
#print axioms ParallelStep.first_selected
#print axioms ParallelStep.singleton_projection_residual
#print axioms StepProjection.atomic_last_copy
#print axioms StepProjection.pointed_copy
end Lamping.Checks.FunctionExtractionFixture

namespace Lamping.Checks.Phase4InitialSummaryReview
open Lamping.AG.InitialOffsets
#print axioms Shape.markerWords_length
#print axioms Shape.first_event
#print axioms corrected_initial_invariants
end Lamping.Checks.Phase4InitialSummaryReview
namespace Lamping.Checks.Phase4OffsetZeroReview
open Lamping.AG Lamping.Graph Lamping.Lambda
def mu : List (Endpoint g) := es.drop 4
def offset (route : List (Endpoint g)) : Nat :=
  ((route.zip route.tail).filter (fun z => match g.wire z.1 with
    | .inl ⟨n,_⟩ => match (g.label n).sort with | .op .bra => true | _ => false
    | _ => false)).length
theorem offset_zero : offset mu = 0 := by decide
theorem mu_labels : Labelling g mu Context.empty B := by
  apply Labelling.cons (LabelledTurn.transparent (g:=g) wFnFV true Context.empty)
  apply Labelling.cons (LabelledTurn.node (g:=g) fanN fanO (.inl ()) (.direct (by
    simpa [B] using Passage.fanO (i:=0) Context.empty Context.empty Level.empty)))
  apply Labelling.cons (LabelledTurn.transparent (g:=g) wLamFV true B)
  exact .single _ _
example : mu.head?=some (.inl ⟨croN,.inl ()⟩) := rfl
example : (reverseEdges mu).head?=some (.inl ⟨lamN,lamBind⟩) := rfl
example : (reverseEdges mu).getLast?=some (g.wire (.inl ⟨croN,.inl ()⟩)) := rfl
example : (g.label croN).sort=.op .cro := rfl
example : (g.label fanN).sort=.op .fan := rfl

theorem forward : Forward g es := by
  obtain ⟨vp,flow⟩ := encode_flow term 0
  apply (labels.initial_of_flow flow ?_).forward
  intro e he
  have hh : e=.inl ⟨lamN,lamBody⟩ := by simpa [es] using he.symm
  subst e
  rfl

def binding : BindingLoop g es Context.empty B where
  binder := lamN
  isLam := rfl
  body := lamBody
  bind := lamBind
  body_role := HEq.rfl
  bind_role := HEq.rfl
  start := rfl
  finish := rfl
  proper := labels
  forward := forward
  shell := by intro k hk; change k<0 at hk; omega

theorem printed_p0_formula_false : ¬ ∃ C : Context,
    Context.empty = Context.empty.replace 0 C ∧
    B = Context.empty.replace 0 (C.cons .empty) := by
  rintro ⟨C,hA,hB⟩
  simp only [Context.replace_zero] at hA hB
  rw [←hA,Context.cons_empty] at hB
  have hh := congrArg (fun a : Context => a.get 0) hB
  cases hh
#print axioms binding
#print axioms printed_p0_formula_false
end Lamping.Checks.Phase4OffsetZeroReview

namespace Lamping.Checks.Phase4OffsetZeroReview
open Lamping.AG Lamping.Graph Lamping.Lambda
-- Including the Cro traversal in the control suffix does not change offset.
def muIncludingCro : List (Endpoint g) := es.drop 3
example : offset muIncludingCro = 0 := by decide
example : offset es = 0 := by decide
example : (reverseEdges muIncludingCro).head?=some (.inl ⟨lamN,lamBind⟩) := rfl
example : (reverseEdges muIncludingCro).getLast?=some (.inl ⟨croN,.inr ()⟩) := rfl
example : Closed term := by simp [Closed,Scoped,term]
end Lamping.Checks.Phase4OffsetZeroReview

namespace Lamping.Checks.Phase4OffsetZeroReview
open Lamping.AG Lamping.Graph Lamping.Lambda
def croArgN : (encode 0 term).N := .inr (.inr (.inr ()))
def braN : (encode 0 term).N := .inr (.inl (.inr (.inl ⟨0,rfl⟩)))
def wArgRoot : (encode 0 term).W := .inl (.inr (.inr (.inr (.inl ()))))
def wArgFV : (encode 0 term).W := .inl (.inr (.inr (.inr (.inr ⟨0,rfl⟩))))
def pairB : Context := Context.empty.cons (.pair .empty .empty)
def rightB : Context := Context.empty.cons (.star (.pair .empty .empty))
def rightEs : List (Endpoint g) := [
  .inl ⟨lamN,lamBody⟩,.inr (.inr (wRoot,true)),.inl ⟨appN,appArg⟩,
  .inr (.inr (wArgRoot,true)),.inl ⟨croArgN,.inl ()⟩,
  .inr (.inr (wArgFV,false)),.inl ⟨braN,.inl ()⟩,
  .inl ⟨fanN,.inl ()⟩,.inr (.inr (wLamFV,false))]
theorem right_labels : Labelling g rightEs Context.empty rightB := by
  have hc : Passage 1 (.op .cro) (.inr ()) (.inl ()) Context.empty Context.empty := by
    have he : Context.empty.replace 1 Context.empty = Context.empty := by
      ext k; simp [Context.replace,Context.empty]
    simpa only [Context.cons_empty,he] using Passage.cro (i:=1) Context.empty Context.empty
  have hb : Passage 0 (.op .bra) (.inr ()) (.inl ()) Context.empty pairB := by
    simpa [pairB] using Passage.bra (i:=0) Context.empty Context.empty Level.empty Level.empty
  have hf : Passage 0 (.op .fan) fanStar (.inl ()) pairB rightB := by
    simpa [pairB,rightB] using Passage.fanStar (i:=0) Context.empty Context.empty (Level.pair .empty .empty)
  apply Labelling.cons (LabelledTurn.transparent (g:=g) wRoot false Context.empty)
  apply Labelling.cons (LabelledTurn.node (g:=g) appN appCtx appArg (.direct (.appArg _)))
  apply Labelling.cons (LabelledTurn.transparent (g:=g) wArgRoot false Context.empty)
  apply Labelling.cons (LabelledTurn.node (g:=g) croArgN (.inr ()) (.inl ()) (.direct hc))
  apply Labelling.cons (LabelledTurn.transparent (g:=g) wArgFV true Context.empty)
  apply Labelling.cons (LabelledTurn.node (g:=g) braN (.inr ()) (.inl ()) (.direct hb))
  apply Labelling.cons (LabelledTurn.node (g:=g) fanN fanStar (.inl ()) (.direct hf))
  apply Labelling.cons (LabelledTurn.transparent (g:=g) wLamFV true rightB)
  exact .single _ _
theorem right_forward : Forward g rightEs := by
  obtain ⟨vp,flow⟩ := encode_flow term 0
  apply (right_labels.initial_of_flow flow ?_).forward
  intro e he
  have hh : e=.inl ⟨lamN,lamBody⟩ := by simpa [rightEs] using he.symm
  subst e; rfl
def right_binding : BindingLoop g rightEs Context.empty rightB where
  binder := lamN
  isLam := rfl
  body := lamBody
  bind := lamBind
  body_role := HEq.rfl
  bind_role := HEq.rfl
  start := rfl
  finish := rfl
  proper := right_labels
  forward := right_forward
  shell := by intro k hk; change k<0 at hk; omega
def rightMu : List (Endpoint g) := rightEs.drop 3
example : offset rightMu = 1 := by decide
example : (reverseEdges rightMu).head?=some (.inl ⟨lamN,lamBind⟩) := rfl
example : (reverseEdges rightMu).getLast?=some (.inl ⟨croArgN,.inr ()⟩) := rfl
theorem printed_p1_shape_false (C : Context) (x y : Level) : rightB ≠ C.cons (.pair x y) := by
  intro h; have hh := congrArg (fun c : Context => c.get 0) h; cases hh
#print axioms right_binding
#print axioms printed_p1_shape_false
end Lamping.Checks.Phase4OffsetZeroReview




namespace Lamping.Checks.Phase4ProjectionReview
open Lamping.AG Lamping.Graph
example {K R B F W V : Type} [FiniteNames K] [FiniteNames R] [FiniteNames B]
    [FiniteNames F] [FiniteNames W] [FiniteNames V]
    (c : Net signature K (B⊕F) W) (r : Net signature R F V)
    {x : Endpoint c} {es : List (Endpoint (plug c r))} {a b : Context}
    (h : Labelling (plug c r) (AG.plugLeft c r x::es) a b) :
    (∃xs : List (Endpoint c),es=xs.map (AG.plugLeft c r) ∧ Labelling c (x::xs) a b) ∨
    ∃(xs : List (Endpoint c)) (z : F) (tail : List (Endpoint (plug c r))) (mid : Context),
      es=xs.map (AG.plugLeft c r)++AG.plugRight c r (.inr (.inl z))::tail ∧
      Labelling c (x::xs) a mid ∧ (x::xs).getLast?=some (c.wire (.inr (.inl (.inr z)))) ∧
      Labelling (plug c r) (AG.plugRight c r (.inr (.inl z))::tail) mid b :=
  h.plugLeft_first c r
#print axioms LabelledTurn.plug_cross
#print axioms Labelling.plugLeft_first
#print axioms Labelling.plugRight_first
end Lamping.Checks.Phase4ProjectionReview

namespace Lamping.Checks.Phase4CorrectedOffsetsReview
open Lamping.AG Lamping.AG.InitialOffsets Lamping.Graph
-- The corrected shape lets a final fan decorate the whole Pair.
example : Shape.level (.base [false]) Context.empty 0 = .o .empty := rfl
example : Shape.level (.lower (.base []) [true]) Context.empty 0 =
    .star (.pair .empty .empty) := rfl
example : Shape.offset (.lower (.base []) [true]) = 1 := rfl
example : Shape.events (.lower (.base []) [true]) 0 =
    [.cro 1,.bra 0,.fan 0 true] := rfl
-- No shell or forward certificate is required for the actual raw-loop formula.
example (t : Lamping.Lambda.Term) (n : Nat)
    (es : List (Endpoint (encode n t).net)) {a b : Context}
    (h : RawLoop (encode n t).net es a b) :
    b=executeEvents (eventsOfEdges (encode n t).net es) a :=
  encode_rawLoop_composition t n es h
example (shape : Shape) (n : Nat) (a b : Context)
    (h : Run (shape.events n) a b) :
    b=a.replace n ((a.tail (n+shape.offset)).cons (shape.level a n)) :=
  corrected_program_all_runs shape n a b h
-- The variable/proper separation belongs to a patch, not the entire encoding.
example : ¬VariableSeparated (encode 0 (.var 0)).net variableBoundary Empty.elim := by
  intro h
  have impossible := h (.inr (.inl (.inl ())))
  cases impossible
example (n : Nat) (f a : Lamping.Lambda.Term)
    (x : FV f ⊕ FV a) (side : Bool)
    {A B : Context}
    (h : LocalPath (appPatch n f a) (appChildVariable x) (appChildRoot f a side) A B) : False :=
  appPatch_FV_no_child_root n f a x side h
#print axioms encode_rawLoop_composition
#print axioms corrected_program_all_runs
#print axioms translation_level_binding
#print axioms Labelling.no_proper_visit
#print axioms lambdaUsed_FV_no_child_root
#print axioms lambdaUnused_FV_no_child_root
#print axioms appPatch_FV_no_child_root
end Lamping.Checks.Phase4CorrectedOffsetsReview

namespace Lamping.Checks.Phase4FamilyBoundaryReview
open Lamping.Lambda
example {m : Term} (R S : RedexOcc m) :
    FamilyEq ⟨m,.nil m,R⟩ ⟨m,.nil m,S⟩ ↔ R=S := initial_families_injective R S
example {m : Term} (r : ExtractionRun m) (hp : 0<r.rank) :
    ∃ a, RunRepresents r a := r.represents_exists hp
-- The confluence conclusion still explicitly needs actual critical pairs.
example (m : Term) (criticalPairs : ExtractionLocallyConfluent m) :
    ExtractionConfluent m := extraction_newman criticalPairs
#print axioms Copy.initial_residual
#print axioms initial_families_injective
#print axioms CompleteFamilyStep.maximal_copySet
#print axioms ExtractionRun.represents_exists
#print axioms RunRepresents.unique
#print axioms extraction_newman
end Lamping.Checks.Phase4FamilyBoundaryReview

namespace Lamping.Checks.Phase4NoEscapeReview
open Lamping.AG Lamping.Graph
example {K R B F W V : Type} [FiniteNames K] [FiniteNames R] [FiniteNames B]
    [FiniteNames F] [FiniteNames W] [FiniteNames V]
    (c : Net signature K (B⊕F) W) (r : Net signature R F V)
    {bp : B → Bool} {fp : F → Bool} {wp : W → Bool} {vp : V → Bool}
    (hc : FlowOn c (Sum.elim bp (fun z => !(fp z))) wp) (hr : FlowOn r fp vp)
    (separated : ∀ (z z' : F) (a b : Context), fp z=false → fp z'=true →
      LocalPath c (.inr z) (.inr z') a b → False)
    {x y : Endpoint r} {tail : List (Endpoint (plug c r))} {a b : Context}
    (out : endPolarity fp vp x=true)
    (h : Labelling (plug c r) (AG.plugRight c r x::tail) a b)
    (last : (AG.plugRight c r x::tail).getLast?=some (AG.plugRight c r y)) :
    ∃ xs : List (Endpoint r),tail=xs.map (AG.plugRight c r) ∧ Labelling r (x::xs) a b :=
  h.child_no_escape c r hc hr separated out last
#print axioms Labelling.all_outgoing
#print axioms Labelling.finish_sink
#print axioms Labelling.patch_exit_stays_left
#print axioms Labelling.child_no_escape
#check Labelling.outer_child_decompose
#print axioms Labelling.outer_child_decompose
end Lamping.Checks.Phase4NoEscapeReview

namespace Lamping.Checks.Phase4SubstitutionOriginsReview
open Lamping.Lambda
-- A function variable becoming lambda creates a redex shape, never an old tag.
example : ([] : Path) ∉ Marked.tracePositions []
    (Marked.subst (fun _ => .lam (.var 0)) (.app [] (.var 0) (.var 1))) := by decide
-- An inserted tagged application below a binder keeps its tag and shifted site.
example : ([.body] : Path) ∈ Marked.tracePositions [.arg]
    (Marked.subst (fun _ => .app [[.arg]] (.lam (.var 0)) (.var 0)) (.lam (.var 1))) := by decide
#print axioms BetaAt.creation_locality
#print axioms subst_redex_source
#print axioms Marked.subst_trace_iff_source
#print axioms Marked.trace_subst_preserve
#print axioms Marked.trace_subst_insert
end Lamping.Checks.Phase4SubstitutionOriginsReview

namespace Lamping.Checks.Phase4RootCreationReview
open Lamping.Lambda
def body : Term := .lam (.app (.var 1) (.var 0))
def ident : Term := .lam (.var 0)
def created : RedexOcc (contract body ident) := ⟨[.body],by
  exact ⟨.app ident (.var 0),rfl,trivial⟩⟩
theorem no_old_ancestor : ¬∃ r, (rootContraction body ident).Residual r created := by
  rintro ⟨r,hr⟩
  rw [root_residual_iff] at hr
  have hb : redexPositions body=[] := by decide
  have ha : redexPositions ident=[] := by decide
  rw [hb,ha] at hr
  simp at hr
-- The created head variable is var 1 below the nested binder, never inner var 0.
example : ∃ b inner, ident=.lam b ∧
    subtermAt body created.val=some (.app (.var (binderDepth created.val)) inner) :=
  root_new_redex_source created no_old_ancestor
example : subtermAt body created.val ≠ some (.app (.var 0) (.var 0)) := by decide
#print axioms root_residual_iff
#print axioms root_new_redex_source
#print axioms no_old_ancestor
#print axioms replaceAt_disjoint_square
#print axioms BetaAt.disjoint_square
#print axioms BetaAt.disjoint_residual
end Lamping.Checks.Phase4RootCreationReview

namespace Lamping.Checks.Phase4HeadVariableReview
open Lamping.Lambda Lamping.Lambda.Marked
def before : Marked := .lam (.app [[.arg]] (.var 1)
  (.app [] (.lam (.var 0)) (.var 0)))
def after : Marked := .lam (.app [[.arg]] (.var 1) (.var 0))
def history : Marked.History [[.body,.arg]] before after :=
  .cons (.lam (.appR (.appRoot [] (.var 0) (.var 0)))) (.nil _)
theorem outer_head : HeadVariable [.arg] 0 before := by simp [HeadVariable,before]
example : ¬∃ z, subtermAt after.erase [.body]=some z ∧ IsRedex z :=
  history.headVariable_no_redex outer_head (by decide)
-- The substitution guard cannot be omitted: replacing the free head by lambda
-- creates precisely a tagged redex, outside this invariant's intended domain.
example : ¬HeadVariable [.arg] 0
    (Marked.subst (fun _ => .lam (.var 0)) (.app [[.arg]] (.var 0) (.var 0))) := by
  simp [HeadVariable,Marked.subst]
#print axioms HeadVariable.rename
#print axioms HeadVariable.subst
#print axioms ReductionAt.headVariable
#print axioms History.headVariable_no_redex
#print axioms outer_head
end Lamping.Checks.Phase4HeadVariableReview

namespace Lamping.Checks.Phase4NestedLoopReview
open Lamping.AG Lamping.AG.InitialOffsets Lamping.Graph
example (t : Lamping.Lambda.Term) (n : Nat)
    (es : List (Endpoint (encode n t).net)) {a b : Context}
    (loop : RawLoop (encode n t).net es a b) :
    Context.SameShell ((encode n t).net.label loop.binder).index a b :=
  encode_rawLoop_shell t n es a b loop
example (t : Lamping.Lambda.Term) (n : Nat)
    (es : List (Endpoint (encode n t).net)) {a b : Context}
    (loop : RawLoop (encode n t).net es a b) (c : Context) :
    ∃ d, Nonempty (BindingLoop (encode n t).net es c d) :=
  encode_rawLoop_transparent t n es loop c
#print axioms rawLoop_plugRight
#print axioms rawLoop_unionL
#print axioms rawLoop_unionR
#print axioms encode_rawLoop_shell
#print axioms encode_rawLoop_binding
#print axioms encode_rawLoop_transparent
#print axioms lambdaUsed_body_to_child
#print axioms lambdaUnused_body_to_child
#print axioms lambdaUsed_child_to_binding
#print axioms lambdaUnused_child_not_binding
#print axioms lambdaUsed_root_to_child
#print axioms lambdaUnused_root_to_child
end Lamping.Checks.Phase4NestedLoopReview

namespace Lamping.Checks.Phase4ApplicationDiamondReview
open Lamping.Lambda
def source : Term := .app (.var 0) (.app (.lam (.var 0)) (.var 1))
def target : Term := .app (.var 0) (.var 1)
def annotations : Marked := .app [[]] (.var 0) (.red [] (.var 0) (.var 1))
theorem step : BetaAt source [.arg] target := ⟨.var 0,.var 1,rfl,rfl⟩
-- The root application is tagged even though its head is variable, not lambda.
example : ∃ (w : Term)
    (sq : ParallelMovesSquare [[.arg]] [[.arg]] source target target w) (z : Marked),
    Marked.History (sq.first.derivation.append sq.afterFirst.derivation).paths annotations z ∧
    Marked.History (sq.second.derivation.append sq.afterSecond.derivation).paths annotations z := by
  obtain ⟨w,⟨sq⟩⟩ := ParallelMovesSquare.exists (singleContraction step) (singleContraction step)
  obtain ⟨z,hz,kz⟩ := sq.tracking_diamond annotations (by decide)
  exact ⟨w,sq,z,hz,kz⟩
#print axioms ParallelStep.composite_relative_union
#print axioms ParallelMovesSquare.tracking_diamond
end Lamping.Checks.Phase4ApplicationDiamondReview

namespace Lamping.Checks.Phase4RootHeadGuardReview
open Lamping.Lambda Lamping.Lambda.Marked
def source : Marked := .app [] (.lam Phase4HeadVariableReview.before) (.var 1)
def target : Marked := .app [] (.lam Phase4HeadVariableReview.after) (.var 1)
def otherStep : ReductionAt [.fn,.body,.body,.arg] source target :=
  .appL (.lam (.lam (.appR (.appRoot [] (.var 0) (.var 0)))))
theorem guarded : RootHeadGuard [.arg] source := by
  exact ⟨Phase4HeadVariableReview.outer_head,by simp,by rfl⟩
example : RootHeadGuard [.arg] target := otherStep.rootHeadGuard (by decide) guarded
example : ¬∃ z, subtermAt target.erase [.fn,.body,.body]=some z ∧ IsRedex z :=
  (otherStep.rootHeadGuard (by decide) guarded).no_redex (by decide)
#print axioms ReductionAt.trace_outside
#print axioms ReductionAt.trace_empty
#print axioms ReductionAt.rootHeadGuard
#print axioms RootHeadGuard.no_redex
#print axioms BetaAt.disjoint_residual_iff
#print axioms BetaAt.disjoint_residualSet
end Lamping.Checks.Phase4RootHeadGuardReview

namespace Lamping.Checks.Phase4NoBinderRevisitReview
open Lamping.AG Lamping.AG.InitialOffsets Lamping.Graph
example (t : Lamping.Lambda.Term) (n : Nat)
    (es : List (Endpoint (encode n t).net)) (a b : Context)
    (loop : RawLoop (encode n t).net es a b) :
    ∀ e, e∈es.drop 1 → ¬∃ p, e=.inl ⟨loop.binder,p⟩ :=
  encode_rawLoop_no_revisit t n es a b loop
#print axioms lambdaUsed_rawLoop_child
#print axioms lambdaUnused_no_rawLoop
#print axioms lambdaUsed_rawLoop_events
#print axioms encode_rawLoop_no_revisit
end Lamping.Checks.Phase4NoBinderRevisitReview

namespace Lamping.Checks.Phase4RootApplicationIdentityReview
open Lamping.Lambda Lamping.Lambda.Marked
-- The same pending application identity is guarded before beta and survives it.
example : RootHeadGuard [.fn,.body,.body]
    (markAll [[]] (.app (.lam Phase4RootCreationReview.body) Phase4RootCreationReview.ident)) :=
  rootHeadGuard_markAll (site:=[.body]) (inner:=.var 0) rfl
example : ([.body] : Path)∈tracePositions [.fn,.body,.body]
    (allRootTarget [[]] Phase4RootCreationReview.body Phase4RootCreationReview.ident) :=
  allRoot_created_identity (site:=[.body]) (inner:=.var 0) rfl
#print axioms tagsAt_markAllAt
#print axioms headVariable_markAllAt
#print axioms EveryApplicationTagged.redex_tag
#print axioms rootHeadGuard_markAll
#print axioms allRootTracking
#print axioms allRoot_created_identity
#print axioms Derivation.tracking_erase
end Lamping.Checks.Phase4RootApplicationIdentityReview

namespace Lamping.Checks.Phase4RootSeparationReview
open Lamping.Lambda
#check root_creation_separation
#print axioms Marked.History.trace_inclusion
#print axioms root_creation_separation
end Lamping.Checks.Phase4RootSeparationReview

namespace Lamping.Checks.Phase4PatchBoundaryReview
open Lamping.AG Lamping.AG.InitialOffsets
#print axioms Labelling.one_turn_boundary
#print axioms appPatch_function_FV_shape
#print axioms appPatch_argument_FV_shape
#print axioms appPatch_root_to_child
#print axioms lambdaUsed_FV_external_shape
#print axioms lambdaUnused_FV_external_shape
#print axioms LocalPath.outer_child
end Lamping.Checks.Phase4PatchBoundaryReview

namespace Lamping.Checks.Phase4DisjointSeparationReview
open Lamping.Lambda
#check disjoint_creation_separation
#print axioms ParallelStep.singleton_paths
#print axioms BetaAt.outside_residual_iff
#print axioms disjoint_creation_separation
end Lamping.Checks.Phase4DisjointSeparationReview

namespace Lamping.Checks.Phase4OffsetZeroReview
open Lamping.AG Lamping.AG.InitialOffsets Lamping.Graph
def ownRightRaw : RawLoop g rightEs Context.empty rightB :=
  ⟨lamN,rfl,lamBody,lamBind,HEq.rfl,HEq.rfl,rfl,rfl,right_labels⟩
-- Apply the universal corrected theorem to the independently constructed
-- counterexample to the printed formula, with its physical offset one.
example : ∃ shape : Shape, shape.offset=1 ∧ eventsOfEdges g rightEs=shape.events 0 ∧
    rightB=Context.empty.replace 0 ((Context.empty.tail shape.offset).cons
      (shape.level Context.empty 0)) := by
  obtain ⟨shape,word,count,formula⟩ := encode_rawLoop_offset term 0 rightEs Context.empty rightB ownRightRaw
  have physical : bracketOffset g rightEs=1 := rfl
  refine ⟨shape,count.trans physical,word,?_⟩
  exact formula
#print axioms encode_FV_shape
#print axioms encode_rawLoop_shape
#print axioms encode_rawLoop_corrected
#print axioms encode_rawLoop_offset
end Lamping.Checks.Phase4OffsetZeroReview

namespace Lamping.Checks.Phase4ArgumentNoDirectCopyReview
open Lamping.Lambda
def innerBeforeCopy : BetaAt afterR [.fn,.arg] copyTerm := ⟨.var 0,.var 0,rfl,rfl⟩
def residualTarget : ExtractionRun source := .of
  (.cons (singleContraction R) (.single (singleContraction innerBeforeCopy)))
  (.cons R (.single innerBeforeCopy))
theorem independent_late_residual : ExtractionStep beforeRun residualTarget := by
  have old : (singleContraction L).derivation.Residual
      ⟨[.fn,.arg],innerBeforeCopy.redex⟩ ⟨[.fn],S.redex⟩ := by
    rw [ParallelStep.residual_iff]
    decide
  exact ExtractionStep.residual (.single (singleContraction R)) (.single R)
    L S innerBeforeCopy old
example : ExtractionJoin afterRun residualTarget :=
  extraction_locally_confluent source actual_argument_extraction independent_late_residual
example (r s t : ExtractionRun source) (h : Extraction r s) (k : Extraction r t)
    (hs : ExtractionNormal s) (ht : ExtractionNormal t) : s=t :=
  extraction_normal_unique h k hs ht
#print axioms function_argument_pullback
#print axioms extraction_function_argument_long_peak
#print axioms RootExtraction.tail_join
#print axioms extraction_locally_confluent
#print axioms extraction_church_rosser
#print axioms extraction_normal_unique
#print axioms PermEq.cancel_prefix
#print axioms HistoryPrefix.copy_interpolation
#print axioms HistoryPrefix.project_beta
#print axioms Copy.extension_residual_iff
#print axioms Copy.family_copySet
#print axioms Copy.project_target_head
#print axioms PruningStep.copy
#print axioms Pruning.copy
#print axioms Pruning.extraction
#print axioms Atomic.prune_initial_residual
#print axioms Atomic.prune_disjoint_prefix
#print axioms ProtectedBlocks.prune_function_pointed
#print axioms ProtectedBlocks.prune_argument_pointed
#print axioms RightHistory.prune_right_pointed
#print axioms Copy.project_region_run
#print axioms Atomic.argument_forward_mirror
#print axioms Copy.project_argument_run
#print axioms initial_complete_iff_max_copies
#print axioms BetaAt.subst
#print axioms ArgumentOccurrence.substitute
#print axioms ArgumentLift.normal_original
#print axioms ExtractionStep.subst
#print axioms StepProjection.function_normal_reflect
#print axioms RootExtraction.normal_target
#print axioms extraction_normal_head_decomposition
#print axioms Copy.standard_common_extraction
#print axioms ArgumentLift.pointed_prefix
#print axioms StepProjection.pointed_prefix_row
#print axioms RootExtraction.pointed_prefix_projection
#print axioms FamilyEq.standardize
#print axioms family_iff_common_extraction
#print axioms canonical_family_unique
#print axioms FamilyEq.extract_canonical
#print axioms RedexWithHistory.canonical_exists_unique
#print axioms ApartHistory.residual_inside_fixed
#print axioms argument_pointed_projection_fiber
#print axioms RootExtraction.pointed_prefix_fiber
#print axioms HistoryPrefix.projected_head_le
#print axioms canonical_copy_of_standard
#print axioms canonical_copy_iff_history_prefix
#print axioms FamilyUsedAt.append_iff
#print axioms StepProjection.final_selection_actual
#print axioms HistoryProjection.used_left
#print axioms FamilyUsedAt.empty_of_absent
#print axioms RelativeFamilies.prefix_development
#print axioms RightHistory.pull_projection
#print axioms StepProjection.used_bottom
#print axioms RightHistory.pull_selected_supported
#print axioms atomic_standardization_exists_supported
#print axioms atomic_standardization_exists_relative
#print axioms StepProjection.family_used_forward
#print axioms ArgumentLift.family_used_forward
#print axioms Extraction.pointed_family_events
#print axioms canonical_prefix_relative
#print axioms DevelopsFamilies.common_copy_ancestor
#print axioms DevelopsFamilies.family_copySet
#print axioms CompleteDerivation.no_future_family
#print axioms CompleteDerivation.develops_used
#print axioms CompleteDerivation.complete_step_iff_max_copies
#print axioms complete_derivation_iff_max_copies
#print axioms CompleteDerivation.family_residual_representation
-- Apply the stronger fiber to the same nonlinear example with both direct
-- Copy directions refuted above. The full projection supplies the remainder.
example : ∃ z, ∃ program : ParallelHistory afterR z, ∃ q : RedexOcc z,
    Copy original ⟨z,(ParallelHistory.single (singleContraction R)).append program,q⟩ ∧
    ∀ q' : RedexOcc z, Copy ⟨copyTerm,.single (singleContraction L),⟨[.fn],S.redex⟩⟩
      ⟨z,program,q'⟩ → q'=q := by
  let a0 : RedexWithHistory afterR := ⟨copyTerm,.single (singleContraction L),⟨[.fn],S.redex⟩⟩
  have root : RootExtraction R (.of copyFull ((Atomic.single L).append (.single S))) afterRun :=
    .argumentPart copyFull ((Atomic.single L).append (.single S)) originalFull
      ((Atomic.single O).append (.single OS)) (by decide) actualLift
  obtain ⟨z,F,program,last,q,_,_,copy,unique⟩ := root.pointed_prefix_fiber a0 original
    ⟨S,.single L,rfl⟩ ⟨OS,.single O,rfl⟩
  exact ⟨z,program,q,copy,unique⟩
end Lamping.Checks.Phase4ArgumentNoDirectCopyReview

namespace Lamping.Checks.DisjointExtractionFixture
open Lamping.Lambda
-- Keep the earlier hard ¬Standard rightThenLeft result. Only its pointed
-- prefix is standard, which is exactly the new common-extraction API scope.
example : ExtractionJoin (.of (.single (singleContraction R)) (.single R)) pointedRun := by
  let a : RedexWithHistory T := ⟨T,.nil T,⟨[.fn],R.redex⟩⟩
  let b : RedexWithHistory T := ⟨V,.single (singleContraction S),⟨[.fn],RS.redex⟩⟩
  have copy : Copy a b := by
    refine ⟨.single (singleContraction S),.refl _,?_⟩
    rw [ParallelHistory.single_derivation,ParallelStep.residual_iff]
    decide
  exact copy.standard_common_extraction ⟨R,.nil T,rfl⟩ ⟨RS,.single S,rfl⟩
    (.nil T) (Standard.single_step _ ⟨[.arg],S.redex⟩ (leftmost_singleton _))
end Lamping.Checks.DisjointExtractionFixture

namespace Lamping.Checks.FunctionExtractionFixture
open Lamping.Lambda
example : ∃ s : ExtractionRun U, ∃ image : RedexWithHistory U,
    RunRepresents s image ∧ Standard image.history ∧
    Copy image ⟨U,.nil U,⟨[],SR.redex⟩⟩ ∧
    Extraction (s.prepend (.single (singleContraction R)) (.single R))
      (.of (.single (singleContraction S)) (.single S)) := by
  let a : RedexWithHistory T := ⟨T,.nil T,⟨[.fn,.body],S.redex⟩⟩
  let b : RedexWithHistory U := ⟨U,.nil U,⟨[],SR.redex⟩⟩
  have old : (singleContraction R).derivation.Residual a.redex b.redex := by
    rw [ParallelStep.residual_iff]
    decide
  have copy : Copy a ⟨b.target,(ParallelHistory.single (singleContraction R)).append b.history,b.redex⟩ :=
    ⟨.single (singleContraction R),.refl _,old⟩
  apply copy.project_region_run R a b ⟨S,.nil T,rfl⟩ (.nil T) (.inr rfl)
  intro q hq
  change q∈[[.fn,.body]] at hq
  exact ⟨[.body],(List.mem_singleton.mp hq)⟩
end Lamping.Checks.FunctionExtractionFixture

namespace Lamping.Checks.Phase4CompletePrefixReview
open Lamping.Lambda
def oldRootFamily (a : RedexWithHistory O) : Prop := FamilyEq ⟨O,.nil O,r⟩ a
theorem real_event_relative : RelativeFamilies (.single (singleContraction step)) oldRootFamily := by
  intro a used
  cases used with
  | @head _ _ _ _ _ _ _ _ q selected family =>
    have same : q=r := Subtype.ext (List.mem_singleton.mp selected)
    cases same
    exact family
  | tail impossible => cases impossible
-- The self-loop keeps a redex, while exhausting the selected OLD family.
-- This is a given development with a real event, not a completion theorem.
theorem real_event_development : DevelopsFamilies (.single (singleContraction step)) oldRootFamily := by
  refine ⟨real_event_relative,?_⟩
  intro q family
  have old := (initial_family_iff r ⟨O,.single (singleContraction step),q⟩).mp family
  exact (singleContraction step).no_selected_residual r (by simp [r]) q old
example : HistoryPrefix (.single (singleContraction step)) (.single (singleContraction step)) :=
  real_event_relative.prefix_development real_event_development
end Lamping.Checks.Phase4CompletePrefixReview

