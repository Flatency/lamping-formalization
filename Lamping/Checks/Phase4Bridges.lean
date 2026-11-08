import Lamping.Lamping.InitialPaths
import Lamping.Lamping.PathSiteTransport
import Lamping.Lamping.InitialPathControls
import Lamping.Lamping.LocalCancellation
import Lamping.Lambda.Labels
import Lamping.Lambda.SingleContraction
import Lamping.Lambda.ExtractionTermination
import Lamping.Lambda.ResidualOrigins
import Lamping.Lambda.ParallelMovesResidual
import Lamping.Lambda.ProjectionFamilies
import Lamping.Lambda.CreationSeparation
import Lamping.Lambda.DisjointCreationSeparation
import Lamping.Lambda.TraceNoDup
import Lamping.Lambda.StandardizationWeight
import Lamping.Lambda.StandardizationCreation
import Lamping.Lambda.AtomicRowExistence
import Lamping.Lambda.StepProjectionHead
import Lamping.Lambda.ExtractionDisjointResidualPeak
import Lamping.Lambda.ParallelPrefixScope
import Lamping.Lambda.ExtractionDisjointLongTail
import Lamping.Lambda.ArgumentHeadPreservation
import Lamping.Lambda.ArgumentResidualScope
import Lamping.Lambda.CanonicalPrefixStandard
import Lamping.Lambda.ExtractionFamilyInvariance
import Lamping.Lambda.ParallelContextLift
import Lamping.Lambda.ParallelPrefixResidualSet
import Lamping.Lambda.MaximalCopies
import Lamping.Lambda.ProjectionContextLift
import Lamping.Lambda.ExtractionContextLift
import Lamping.Lambda.ProjectionContextReflect
import Lamping.Lambda.AtomicScheduleSplit
import Lamping.Lambda.ExtractionContextReflect
import Lamping.Lambda.FunctionArgumentOccurrenceReflect
import Lamping.Lambda.HistoryPreorder
import Lamping.Lambda.PrefixProjection
import Lamping.Lambda.CopySetRepresentation
import Lamping.Lambda.InitialCompleteCopies
import Lamping.Lambda.RootProjectedCopyReflection
import Lamping.Lambda.RightHistoryProjection
namespace Lamping.Checks.Phase4Bridges
open Lamping.Lambda Lamping.AG

example (t : Term) (n : Nat) (v : (encode n t).N) (h : ((encode n t).net.label v).sort = .op f) :
    n ≤ ((encode n t).net.label v).index := encode_level_lower t n v h
example : (encode 4 (.lam (.var 0))).net.label (.inr ()) = label .cro 4 := rfl
example : (encode 4 (.app (.var 0) (.var 0))).net.label (.inr (.inr ())) = label .cro 5 := rfl

open Lamping.Lambda.Labelled
private def a := Label.atom 0
private def b := Label.atom 1
private def c := Label.atom 2
private def d := Label.atom 3
private def e := Label.atom 4
example : (a.concat b).concat c = a.concat (b.concat c) := Label.concat_assoc _ _ _
example : LTerm.degree (.app a (.lam b (.var c 0)) (.var d 0)) = some b := rfl
example : LTerm.degree (.app a (.lam b (.var c 0)) (.var d 0)) ≠ some a := by decide
example : LTerm.contract a b (.lam c (.var d 1)) (.var e 0) =
    .lam ((a.concat b.over).concat c) (.var (d.concat (b.under.concat e)) 1) := rfl
example (t : Term) : INIT (initLabels t) := init_is_INIT t
example (t : Term) : (initLabels t).erase = t := erase_initLabels t
example : ¬ INIT (LTerm.contract a b (.var c 0) (.var d 0)) := root_contract_not_INIT _ _ _ _

example (h : BetaAt t p u) : (singleContraction h).paths = [p] := rfl
example (n : Nat) (s t : Context) :
    (identityBindingLoop n s t).binder = Sum.inl () := rfl
example (t : Term) (r : ExtractionRun t) :
    ¬ ExtractionStep (.of (.nil t) (.nil t)) r := by
  intro h
  have := h.rank_lt
  change r.rank < 0 at this
  omega

private def I : Term := .lam (.var 0)
private def creatorSource : Term := .app (.app I I) I
private def creatorTarget : Term := .app I I
private theorem creator : BetaAt creatorSource [.fn] creatorTarget := ⟨.var 0,I,rfl,rfl⟩
private def created : RedexOcc creatorTarget := ⟨[],creatorTarget,rfl,True.intro⟩
private def creatorTracked : Marked := .app [] (.lam (.var 0)) (.lam (.var 0))
private theorem creatorTracking : Marked.History (singleContraction creator).paths
    (Marked.mark [] creatorSource) creatorTracked := by
  change Marked.History [[.fn]]
    (.app [] (.app [[.fn]] (.lam (.var 0)) (.lam (.var 0))) (.lam (.var 0))) creatorTracked
  exact .cons (.appL (.appRoot [[.fn]] (.var 0) (.lam (.var 0)))) (.nil _)
/-- Ex5.2.6 requires distinct R/S: if R=S, a redex created by that one
contraction has both middle witnesses but no initial residual ancestor. -/
theorem created_no_initial_ancestor :
    ¬ ∃ r : RedexOcc creatorSource, (singleContraction creator).derivation.Residual r created := by
  rintro ⟨r,hr⟩
  have ht := (Derivation.residual_iff_tracking _ creatorTracking r created).mp hr
  simp [created,creatorTracked,Marked.tracePositions] at ht

#print axioms Lamping.AG.encode_level_lower
#print axioms Lamping.AG.Labelling.join
#print axioms Lamping.AG.Labelling.plugRight
#print axioms Lamping.AG.PathSite.rhs_labeling
#print axioms Lamping.Lambda.Labelled.Label.concat_assoc
#print axioms Lamping.Lambda.Labelled.LTerm.erase_subst
#print axioms Lamping.Lambda.Labelled.LBETA.erase
#print axioms Lamping.Lambda.Labelled.init_is_INIT
#print axioms Lamping.Lambda.Labelled.root_contract_not_INIT
#print axioms Lamping.Lambda.singleContraction
#print axioms Lamping.Lambda.Marked.StepAt.single_normal
#print axioms Lamping.AG.initialVarPath
#print axioms Lamping.AG.identityBindingLoop
#print axioms Lamping.AG.fanCancel_transport
#print axioms Lamping.AG.croCancel_transport
#print axioms Lamping.AG.braCancel_transport
#print axioms Lamping.Lambda.ExtractionStep.rank_lt
#print axioms Lamping.Lambda.no_infinite_extraction
#print axioms Lamping.Lambda.extraction_wellFounded
#print axioms Lamping.Lambda.Derivation.residual_unique_source
#print axioms created_no_initial_ancestor
#print axioms Lamping.Lambda.root_creation_separation
#print axioms Lamping.Lambda.disjoint_creation_separation
#print axioms Lamping.Lambda.StepProjection.split_last
#print axioms Lamping.Lambda.StepProjection.atomic_last_copy
#print axioms Lamping.Lambda.StepProjection.pointed_copy
#print axioms Lamping.Lambda.Marked.tracePositions_nodup
#print axioms Lamping.Lambda.Marked.initial_trace_singleton
#print axioms Lamping.Lambda.Marked.initial_trace_singleton_at
#print axioms Lamping.Lambda.Marked.trace_singleton_of_members
#print axioms Lamping.Lambda.BetaAt.selected_residual_weight_lt
#print axioms Lamping.Lambda.BetaAt.redex_reflect_before
#print axioms Lamping.Lambda.Atomic.disjoint_projection
#print axioms Lamping.Lambda.Atomic.function_projection
#print axioms Lamping.Lambda.StepProjection.head_square
#print axioms Lamping.Lambda.StepProjection.final_selection_singleton
#print axioms Lamping.Lambda.BetaAt.argument_residual_iff
#print axioms Lamping.Lambda.ParallelHistory.argument_head_preserved
#print axioms Lamping.Lambda.normal_standard_append
#print axioms Lamping.Lambda.canonical_of_normal_prefix
#print axioms Lamping.Lambda.ExtractionStep.family
#print axioms Lamping.Lambda.Extraction.family
#print axioms Lamping.Lambda.common_extraction_family

namespace DisjointCore
private def argInner : Term := .app I (.var 0)
private def start : Term := .app (.app I I) (.app I argInner)
private def lowerStart : Term := .app I (.app I argInner)
private def upperMid : Term := .app (.app I I) argInner
private def lowerMid : Term := .app I argInner
private def upperEnd : Term := .app (.app I I) (.var 0)
private def lowerEnd : Term := .app I (.var 0)
private def R : BetaAt start [.fn] lowerStart := ⟨.var 0,I,rfl,rfl⟩
private def S : BetaAt lowerStart [.arg] lowerMid := ⟨.var 0,argInner,rfl,rfl⟩
private def T : BetaAt lowerMid [.arg] lowerEnd := ⟨.var 0,.var 0,rfl,rfl⟩
private def S' : BetaAt start [.arg] upperMid := ⟨.var 0,argInner,rfl,rfl⟩
private def T' : BetaAt upperMid [.arg] upperEnd := ⟨.var 0,.var 0,rfl,rfl⟩
private def R' : BetaAt upperMid [.fn] lowerMid := ⟨.var 0,I,rfl,rfl⟩
private def R'' : BetaAt upperEnd [.fn] lowerEnd := ⟨.var 0,I,rfl,rfl⟩
private def V : BetaAt lowerStart [.arg,.arg] lowerMid := ⟨.var 0,.var 0,rfl,rfl⟩
private def sq1 : ParallelMovesSquare [[.fn]] [[.arg]] start lowerStart upperMid lowerMid where
  first := singleContraction R
  second := singleContraction S'
  afterFirst := by change ParallelStep [[.arg]] lowerStart lowerMid; exact singleContraction S
  afterSecond := by change ParallelStep [[.fn]] upperMid lowerMid; exact singleContraction R'
private def sq2 : ParallelMovesSquare [[.fn]] [[.arg]] upperMid lowerMid upperEnd lowerEnd where
  first := singleContraction R'
  second := singleContraction T'
  afterFirst := by change ParallelStep [[.arg]] lowerMid lowerEnd; exact singleContraction T
  afterSecond := by change ParallelStep [[.fn]] upperEnd lowerEnd; exact singleContraction R''
private def top := ParallelHistory.cons (singleContraction S') (.single (singleContraction T'))
private theorem atom : Atomic top := .cons S' (.single T')
private theorem row : StepProjection (singleContraction R) top
    (.cons (singleContraction S) (.single (singleContraction T))) (singleContraction R'') :=
  .cons sq1 (.cons sq2 (.nil _))
private theorem inside : Internal [.arg] top := by
  intro q hq
  change q∈[[.arg],[.arg]] at hq
  simp only [List.mem_cons,List.not_mem_nil,or_false,or_self] at hq
  subst q
  exact ⟨[],rfl⟩
private theorem predecessor : (singleContraction S).derivation.Residual ⟨[.arg,.arg],V.redex⟩ ⟨[.arg],T.redex⟩ := by
  rw [ParallelStep.residual_iff]
  decide
example : ExtractionJoin (.of top atom)
    (.of (.cons (singleContraction R) (.single (singleContraction V))) (.cons R (.single V))) :=
  extraction_disjoint_residual_peak R S T S' T' row
    (by constructor <;> rintro ⟨tail,he⟩ <;> cases he) inside V predecessor
#print axioms extraction_disjoint_residual_peak
private def start3 : Term := .app (.app I I) (.app I (.app I argInner))
private def lowerStart3 : Term := .app I (.app I (.app I argInner))
private def R3 : BetaAt start3 [.fn] lowerStart3 := ⟨.var 0,I,rfl,rfl⟩
private def S0 : BetaAt lowerStart3 [.arg] lowerStart := ⟨.var 0,.app I argInner,rfl,rfl⟩
private def S0' : BetaAt start3 [.arg] start := ⟨.var 0,.app I argInner,rfl,rfl⟩
private def sq0 : ParallelMovesSquare [[.fn]] [[.arg]] start3 lowerStart3 start lowerStart where
  first := singleContraction R3
  second := singleContraction S0'
  afterFirst := by change ParallelStep [[.arg]] lowerStart3 lowerStart; exact singleContraction S0
  afterSecond := by change ParallelStep [[.fn]] start lowerStart; exact singleContraction R
private def top3 := ParallelHistory.cons (singleContraction S0') top
private theorem atom3 : Atomic top3 := .cons S0' atom
private theorem row3 : StepProjection (singleContraction R3) top3
    ((ParallelHistory.single (singleContraction S0)).append
      (.cons (singleContraction S) (.single (singleContraction T)))) (singleContraction R'') :=
  .cons sq0 row
private theorem inside3 : Internal [.arg] top3 := by
  intro q hq
  change q∈[[.arg],[.arg],[.arg]] at hq
  simp only [List.mem_cons,List.not_mem_nil,or_false,or_self] at hq
  subst q
  exact ⟨[],rfl⟩
example : ExtractionJoin (.of top3 atom3)
    (.of (.cons (singleContraction R3)
      ((ParallelHistory.single (singleContraction S0)).append (.single (singleContraction V))))
      (.cons R3 ((Atomic.single S0).append (.single V)))) :=
  extraction_disjoint_residual_long_peak R3 (.single (singleContraction S0)) (.single S0)
    S T top3 atom3 row3 (by constructor <;> rintro ⟨tail,he⟩ <;> cases he) inside3 V predecessor
#print axioms disjoint_residual_pullback
#print axioms extraction_disjoint_residual_long_peak
example : ∃ U V W,
    ∃ H : ParallelStep [[.body,.arg,.fn]] (.lam (.app I start3)) U,
    ∃ top : ParallelHistory (.lam (.app I start3)) V,
    ∃ bottom : ParallelHistory U W,
    ∃ last : ParallelStep [[.body,.arg,.fn]] V W,
      StepProjection H top bottom last ∧
      top.derivation.paths=[[.body,.arg,.arg],[.body,.arg,.arg],[.body,.arg,.arg]] ∧
      Atomic top ∧ Atomic bottom := by
  obtain ⟨U,V,W,H,top,bottom,last,globalRow,_,_,_,_,topPaths,_,_,topAtomic,bottomAtomic⟩ :=
    row3.prefix_lift (T:=.lam (.app I start3)) (pre:=[.body,.arg]) (by rfl)
  exact ⟨U,V,W,H,top,bottom,last,globalRow,topPaths,topAtomic atom3,
    bottomAtomic ((Atomic.single S0).append (.cons S (.single T)))⟩
#print axioms SyntaxContext.liftProjection
#print axioms StepProjection.prefix_lift
private theorem extraction3 : ExtractionStep
    (.of (.cons (singleContraction R3)
      ((ParallelHistory.single (singleContraction S0)).append
        (.cons (singleContraction S) (.single (singleContraction T)))))
      (.cons R3 ((Atomic.single S0).append (.cons S (.single T)))))
    (.of top3 atom3) := by
  exact .disjoint (.nil start3) (.nil start3) R3 top3 atom3 _
    ((Atomic.single S0).append (.cons S (.single T))) (singleContraction R'') row3
    (by decide) [.arg] (by constructor <;> rintro ⟨tail,he⟩ <;> cases he) inside3
private def nested : SyntaxContext := .frame .body (.frame (.arg I) .hole)
example : ExtractionStep (nested.liftRun
    (.of (.cons (singleContraction R3)
      ((ParallelHistory.single (singleContraction S0)).append
        (.cons (singleContraction S) (.single (singleContraction T)))))
      (.cons R3 ((Atomic.single S0).append (.cons S (.single T))))))
    (nested.liftRun (.of top3 atom3)) := nested.liftExtractionStep extraction3
example : ∃ u v w, ∃ h : ParallelStep [[.fn]] start3 u,
    ∃ top : ParallelHistory start3 v, ∃ bottom : ParallelHistory u w,
    ∃ last : ParallelStep [[.fn]] v w,
      StepProjection h top bottom last ∧ Atomic top ∧ Atomic bottom ∧ top.length=3 := by
  obtain ⟨U,V,W,H,top,bottom,last,globalRow,_,_,_,_,topPaths,bottomPaths,_,topAtomic,bottomAtomic⟩ :=
    row3.prefix_lift (T:=.lam (.app I start3)) (pre:=[.body,.arg]) (by rfl)
  have ht : Atomic top := topAtomic atom3
  have hb : Atomic bottom := bottomAtomic ((Atomic.single S0).append (.cons S (.single T)))
  have insideTop : Internal nested.path top := by
    intro q hq
    rw [topPaths] at hq
    change q∈[[.body,.arg,.arg],[.body,.arg,.arg],[.body,.arg,.arg]] at hq
    simp only [List.mem_cons,List.not_mem_nil,or_false,or_self] at hq
    subst q
    exact ⟨[.arg],rfl⟩
  have insideBottom : Internal nested.path bottom := by
    intro q hq
    rw [bottomPaths] at hq
    change q∈[[.body,.arg,.arg],[.body,.arg,.arg],[.body,.arg,.arg]] at hq
    simp only [List.mem_cons,List.not_mem_nil,or_false,or_self] at hq
    subst q
    exact ⟨[.arg],rfl⟩
  have topLength : top.length=3 := by
    have same := ht.paths_length
    rw [topPaths] at same
    exact same.symm
  obtain ⟨u,v,w,h,localTop,localBottom,localLast,ha,hb,localRow,_,veq,_,_,topEq,_,_⟩ :=
    nested.reflectScopedProjection (F:=[[.fn]]) (G:=[[.fn]]) globalRow ht hb insideTop insideBottom
  cases veq
  have localLength : localTop.length=3 := by
    rw [←nested.liftHistory_length localTop,←eq_of_heq topEq]
    exact topLength
  exact ⟨u,v,w,h,localTop,localBottom,localLast,localRow,ha,hb,localLength⟩
#print axioms SyntaxContext.reflectHistory
#print axioms SyntaxContext.reflectProjection
#print axioms SyntaxContext.reflectScopedProjection
example : ∃ M, ∃ first : ParallelHistory (nested.plug start3) M,
    ∃ last : ParallelHistory M (nested.plug upperEnd),
      nested.liftHistory top3=first.append last ∧
      first.derivation.paths=[[.body,.arg,.arg]] ∧
      last.derivation.paths=[[.body,.arg,.arg],[.body,.arg,.arg]] := by
  obtain ⟨M,first,last,_,_,whole,_,firstPaths,lastPaths⟩ :=
    (nested.liftAtomic atom3).split_mapped_program (Atomic.single S0') atom
      (site:=nested.path) (nested.liftHistory_paths top3)
  exact ⟨M,first,last,whole,firstPaths,lastPaths⟩
example : ∃ M, ∃ first : ParallelHistory (nested.plug start3) M,
    ∃ last : ParallelHistory M (nested.plug upperEnd),
      nested.liftHistory top3=first.append last ∧ first.derivation.paths=[] := by
  obtain ⟨M,first,last,_,_,whole,_,firstPaths,_⟩ :=
    (nested.liftAtomic atom3).split_mapped_program (Atomic.nil start3) atom3
      (site:=nested.path) (nested.liftHistory_paths top3)
  exact ⟨M,first,last,whole,firstPaths⟩
#print axioms Atomic.split_mapped_program
example : ExtractionStep
    (.of (.cons (singleContraction R3)
      ((ParallelHistory.single (singleContraction S0)).append
        (.cons (singleContraction S) (.single (singleContraction T)))))
      (.cons R3 ((Atomic.single S0).append (.cons S (.single T)))))
    (.of top3 atom3) := by
  obtain ⟨q,step,equal⟩ := nested.reflectExtractionStep (nested.liftExtractionStep extraction3)
  have same := nested.liftRun_injective equal
  rw [←same] at step
  exact step
end DisjointCore

namespace PrefixScope
private def start : Term := .lam (.app I (.app I (.var 0)))
private def finish : Term := .lam (.app I (.var 0))
private def step : BetaAt start [.body,.arg] finish := ⟨.var 0,.var 0,rfl,rfl⟩
example : ∃ b, ∃ k : ParallelStep [[]] (.app I (.var 0)) b,
    subtermAt finish [.body,.arg]=some b ∧
    (singleContraction step).paths=k.paths.map (fun q => [.body,.arg]++q) :=
  (singleContraction step).prefix_scope (G:=[[]]) (pre:=[.body,.arg]) (by rfl)
private def invalid : ParallelStep [[.body,.fn],[.body,.fn]] (.lam (.var 0)) (.lam (.var 0)) where
  paths := []
  markedTarget := Marked.mark [[.body,.fn],[.body,.fn]] (.lam (.var 0))
  complete := (Marked.completeOld_iff _ _).mpr ⟨.nil _,True.intro⟩
  target_eq := Marked.erase_mark _ _
example : ∃ b, ∃ k : ParallelStep [[.fn],[.fn]] (.var 0) b,
    subtermAt (.lam (.var 0)) [.body]=some b ∧ invalid.paths=k.paths.map (.body::·) :=
  invalid.prefix_scope (G:=[[.fn],[.fn]]) (pre:=[.body]) (by rfl)
#print axioms ParallelStep.prefix_scope
#print axioms ParallelStep.paths_scope
end PrefixScope

namespace ContextLift
private def a : Term := .app I (.var 0)
private def beta : BetaAt a [] (.var 0) := ⟨.var 0,.var 0,rfl,rfl⟩
private def repeated : ParallelStep [[],[]] a (.var 0) :=
  (singleContraction beta).reindex [[],[]] (by intro p; simp)
example : ∃ u, ∃ k : ParallelStep [[.body,.arg],[.body,.arg]]
    (.lam (.app I a)) u, subtermAt u [.body,.arg]=some (.var 0) ∧
    k.paths=[[.body,.arg]] :=
  repeated.prefix_lift (pre:=[.body,.arg]) (by rfl)
private def invalid : ParallelStep [[.fn],[.fn]] (.var 0) (.var 0) where
  paths := []
  markedTarget := .var 0
  complete := (Marked.completeOld_iff _ _).mpr ⟨.nil _,True.intro⟩
  target_eq := rfl
example : ∃ u, ∃ k : ParallelStep [[.body,.fn],[.body,.fn]] (.lam (.var 0)) u,
    subtermAt u [.body]=some (.var 0) ∧ k.paths=[] :=
  invalid.prefix_lift (pre:=[.body]) (by rfl)
#print axioms SyntaxFrame.parallel_lift
#print axioms ParallelStep.prefix_lift
private def dupBody : Term := .app (.var 0) (.var 0)
private def dupSource : Term := .app (.lam dupBody) a
private def dup : BetaAt dupSource [] (.app a a) := ⟨dupBody,a,rfl,rfl⟩
private def globalDup : BetaAt (.lam dupSource) [.body] (.lam (.app a a)) :=
  ⟨dupBody,a,rfl,rfl⟩
private def repeatedGlobal : ParallelStep [[.body],[.body]] (.lam dupSource) (.lam (.app a a)) :=
  (singleContraction globalDup).reindex [[.body],[.body]] (by intro p; simp)
-- The different selection list and repeated old names retain exact copy order.
example : repeatedGlobal.residualSet [[.body,.arg],[.body,.arg],[.body,.body]]=
    [[.body,.fn],[.body,.arg],[.body,.fn],[.body,.arg]] :=
  (singleContraction dup).residualSet_prefix_eq repeatedGlobal
    (pre:=[.body]) (by rfl) (by rfl) [[.arg],[.arg],[.body]]
#print axioms Marked.trace_eq_of_members
#print axioms ParallelStep.trace_prefix_eq
#print axioms ParallelStep.residualSet_prefix_eq
private def copyStep : BetaAt (.app a a) [.fn] (.app (.var 0) a) :=
  ⟨.var 0,.var 0,rfl,rfl⟩
private def argumentStep : BetaAt dupSource [.arg] (.app (.lam dupBody) (.var 0)) :=
  ⟨.var 0,.var 0,rfl,rfl⟩
private def chosenLift : ArgumentLift dup (.single (singleContraction copyStep))
    (.single (singleContraction argumentStep)) where
  body := dupBody
  argument := a
  redex := rfl
  occurrence := [.fn]
  isVariable := rfl
  localPaths := [[]]
  copy_paths := rfl
  original_paths := rfl
  parallelization := StepProjection.exists_projection (singleContraction dup)
    (.single (singleContraction argumentStep))
private theorem argumentExtraction : ExtractionStep
    (.of (.cons (singleContraction dup) (.single (singleContraction copyStep)))
      (.cons dup (.single copyStep)))
    (.of (.single (singleContraction argumentStep)) (.single argumentStep)) :=
  .argumentPart (.nil dupSource) (.nil dupSource) dup _ (.single copyStep) _ (.single argumentStep)
    (by decide) chosenLift
private def nested : SyntaxContext := .frame .body (.frame (.arg I) .hole)
example : ExtractionStep (nested.liftRun
    (.of (.cons (singleContraction dup) (.single (singleContraction copyStep)))
      (.cons dup (.single copyStep))))
    (nested.liftRun (.of (.single (singleContraction argumentStep)) (.single argumentStep))) :=
  nested.liftExtractionStep argumentExtraction
#print axioms SyntaxContext.liftExtractionStep
#print axioms SyntaxContext.liftExtraction
#print axioms SyntaxContext.liftArgument
private def preSource : Term := .app I dupSource
private def P : BetaAt preSource [] dupSource := ⟨.var 0,dupSource,rfl,rfl⟩
private def actualPrefix := ParallelHistory.single (singleContraction P)
private def sourceWithPrefix : ExtractionRun preSource :=
  (ExtractionRun.of (.cons (singleContraction dup) (.single (singleContraction copyStep)))
    (.cons dup (.single copyStep))).prepend actualPrefix (.single P)
private def targetWithPrefix : ExtractionRun preSource :=
  (ExtractionRun.of (.single (singleContraction argumentStep)) (.single argumentStep)).prepend
    actualPrefix (.single P)
private theorem prefixedArgument : ExtractionStep sourceWithPrefix targetWithPrefix :=
  argumentExtraction.prepend actualPrefix (.single P)
example : ExtractionStep sourceWithPrefix targetWithPrefix := by
  obtain ⟨q,step,equal⟩ := nested.reflectExtractionStep (nested.liftExtractionStep prefixedArgument)
  have same := nested.liftRun_injective equal
  rw [←same] at step
  exact step
example : Extraction sourceWithPrefix targetWithPrefix := by
  obtain ⟨q,steps,equal⟩ := nested.reflectExtraction
    (Extraction.single (nested.liftExtractionStep prefixedArgument))
  have same := nested.liftRun_injective equal
  rw [←same] at steps
  exact steps
#print axioms SyntaxContext.reflectRootExtraction
#print axioms SyntaxContext.reflectExtractionStep
#print axioms SyntaxContext.reflectExtraction
end ContextLift

namespace EmptyMaxCopies
private def start : Term := .app I (.var 0)
private def head : BetaAt start [] (.var 0) := ⟨.var 0,.var 0,rfl,rfl⟩
private def pre := ParallelHistory.single (singleContraction head)
private def idle : ParallelStep [] (.var 0) (.var 0) where
  paths := []
  markedTarget := .var 0
  complete := (Marked.completeOld_iff _ _).mpr ⟨.nil _,True.intro⟩
  target_eq := rfl
private theorem noRedex (r : RedexOcc (.var 0)) : False := by
  rcases r with ⟨p,t,lookup,redex⟩
  cases p with
  | nil => simp only [subtermAt,Option.some.injEq] at lookup; subst t; exact redex
  | cons e p => cases e <;> simp [subtermAt] at lookup
-- Current MaxCopySet deliberately records inclusion maximality alone; source
-- complete-step equivalences also need the source's nonempty-step convention.
example : MaxCopySet pre [] ∧ ¬CompleteFamilyStep pre idle := by
  constructor
  · constructor
    · refine ⟨(by intro p hp; cases hp),⟨start,.nil start,⟨[],head.redex⟩⟩,pre,.refl _,?_⟩
      intro r; exact False.elim (noRedex r)
    · intro G valid _ p hp
      exact False.elim (noRedex ⟨p,valid.1 p hp⟩)
  · intro complete
    exact complete.nonempty rfl
end EmptyMaxCopies
namespace ProtectedOccurrence
private def innerBody : Term := .lam (.app (.var 1) (.var 2))
private def innerArgument : Term := .var 0
private def outerBody : Term := .app (.lam innerBody) innerArgument
private def outerArgument : Term := .lam (.var 0)
private def source : Term := .app (.lam outerBody) outerArgument
private def target := contract outerBody outerArgument
private def R : BetaAt source [] target := ⟨outerBody,outerArgument,rfl,rfl⟩
private def S' : BetaAt source [.fn,.body]
    (.app (.lam (contract innerBody innerArgument)) outerArgument) :=
  ⟨innerBody,innerArgument,rfl,rfl⟩
private def targetBody : Term := .lam (.app (.var 1) (.lam (.var 0)))
private def S : BetaAt target [] (contract targetBody outerArgument) :=
  ⟨targetBody,outerArgument,rfl,rfl⟩
private theorem old : (singleContraction R).derivation.Residual ⟨_,S'.redex⟩ ⟨_,S.redex⟩ := by
  have selected := (root_body_residualSet_members R (⟨[],⟨_,rfl,True.intro⟩⟩ : RedexOcc outerBody) []).mpr rfl
  apply ((singleContraction R).residual_iff ⟨_,S'.redex⟩ ⟨_,S.redex⟩).mpr
  exact selected
-- The inner bound occurrence survives; the external argument is a lambda,
-- whose own new bound occurrence must never be mistaken for this binder.
example : ∃ b' a',subtermAt source [.fn,.body]=some (.app (.lam b') a') ∧
    ArgumentOccurrence b' [.body,.fn] :=
  R.function_argument_occurrence_reflect S' S ⟨[.body],rfl⟩ old rfl rfl
example : ¬ ArgumentOccurrence targetBody [.body,.arg,.body] := by
  simp [ArgumentOccurrence,targetBody,subtermAt,binderDepth]
example (σ : Nat → Term) :
    ArgumentOccurrence (subst (liftSub σ) innerBody) [.body,.fn] := rfl
example (σ : Nat → Term) (b : Term) (p : Path)
    (h : ArgumentOccurrence (subst (liftSub σ) b) p) : ArgumentOccurrence b p := h.subst_reflect
#print axioms BetaAt.function_argument_occurrence_reflect
#print axioms subst_protected_occurrence_reflect
end ProtectedOccurrence
namespace PrefixInterpolation
private def delta : Term := .lam (.app (.var 0) (.var 0))
private def omegaTerm : Term := .app delta delta
private def start : Term := .app omegaTerm omegaTerm
private def right : BetaAt start [.arg] start := ⟨.app (.var 0) (.var 0),delta,rfl,rfl⟩
private def one := ParallelHistory.single (singleContraction right)
private def two := one.append one
private def left : RedexOcc start := ⟨[.fn],⟨omegaTerm,rfl,True.intro⟩⟩
private theorem residual : one.derivation.Residual left left := by
  apply (one.residual_outside_internal (site := [.arg]) ?_ left left ?_).mpr rfl
  · intro p hp
    change p∈[[Step.arg]] at hp
    exact ⟨[],by rw [List.mem_singleton.mp hp]; rfl⟩
  · rintro ⟨q,hq⟩
    cases hq
private theorem copy : Copy ⟨start,.nil start,left⟩ ⟨start,two,left⟩ := by
  refine ⟨two,.refl _,?_⟩
  change (one.append one).derivation.Residual left left
  rw [ParallelHistory.derivation_append,Derivation.residual_append]
  exact ⟨left,residual,residual⟩
-- A real middle redex is reconstructed between one and two right Ω steps.
example : ∃ q : RedexOcc start,Copy ⟨start,.nil start,left⟩ ⟨start,one,q⟩ ∧
    Copy ⟨start,one,q⟩ ⟨start,two,left⟩ :=
  HistoryPrefix.copy_interpolation ⟨one,.refl _⟩ ⟨one,.refl _⟩ left left copy
example (a b : ParallelHistory start u) (p : PermEq (two.append a) (two.append b)) :
    PermEq a b := p.cancel_prefix two
example {a b : Term} {left : ParallelHistory start a} {rightBottom : ParallelHistory start b}
    {lastLeft : ParallelStep G start a} {lastRight : ParallelStep H start b}
    (rowLeft : StepProjection (singleContraction right) one left lastLeft)
    (rowRight : StepProjection (singleContraction right) two rightBottom lastRight) :
    HistoryPrefix left rightBottom :=
  HistoryPrefix.project_beta ⟨one,.refl _⟩ right rowLeft rowRight
example : ∃ F, CopySet two F ∧ left.val∈F ∧ ∀ s : RedexOcc start,
    s.val∈F ↔FamilyEq ⟨start,two,left⟩ ⟨start,two,s⟩ := by
  apply Copy.family_copySet ⟨start,.nil start,left⟩ left copy
  intro s family
  refine ⟨two,.refl _,?_⟩
  exact (initial_family_iff left ⟨start,two,s⟩).mp (.trans (.copy copy) family)
#print axioms PermEq.cancel_prefix
#print axioms HistoryPrefix.copy_interpolation
#print axioms HistoryPrefix.project
#print axioms Copy.family_copySet
private def leftStep : BetaAt start [.fn] start :=
  ⟨.app (.var 0) (.var 0),delta,rfl,rfl⟩
private theorem rightProtected : RightHistory [.fn] two := by
  have head : ∀ r : RedexOcc start,r.val∈[[Step.arg]] →LeftOf [Step.fn] r.val := by
    intro r hr
    rw [List.mem_singleton.mp hr]
    exact .branch [] []
  exact .cons (singleContraction right) _ head (.cons (singleContraction right) _ head (.nil _))
example : ∃ (v : Term) (source : BetaAt start [.fn] v) (tail : ParallelHistory v start)
    (K : List Path) (last : ParallelStep K start start),
    StepProjection (singleContraction source) two tail last ∧
    tail.length=two.length ∧last.paths=[[.fn]] ∧
    PermEq (.single last) (.single (singleContraction leftStep)) :=
  rightProtected.pull_projection left rfl leftStep
#print axioms RightHistory.pull_projection
end PrefixInterpolation
namespace InitialCopies
private def start : Term := .app I (.var 0)
private def R : BetaAt start [] (.var 0) := ⟨.var 0,.var 0,rfl,rfl⟩
private def selected : ParallelStep [[],[]] start (.var 0) :=
  (singleContraction R).reindex [[],[]] (fun p => by simp)
private def r : RedexOcc start := ⟨[],R.redex⟩
private theorem complete : CompleteFamilyStep (.nil start) selected := by
  refine ⟨?_,r,(by simp [r]),?_⟩
  · intro p hp
    have same : p=[] := by simpa using hp
    cases same
    exact R.redex
  · intro s
    rw [initial_families_injective]
    constructor
    · intro hs
      apply Subtype.ext
      exact (show s.val=[] by simpa using hs).symm
    · intro same
      cases same
      simp [r]
example : MaxCopySet (.nil start) [[],[]] :=
  ((initial_complete_iff_max_copies selected).mp complete).2
#print axioms initial_complete_iff_max_copies
end InitialCopies
namespace PointedFiber
private def arg0 : Term := .app I (.app I (.var 0))
private def arg1 : Term := .app I (.var 0)
private def body : Term := .app (.var 0) (.var 0)
private def start : Term := .app (.lam body) arg0
private def afterRoot : Term := .app arg0 arg0
private def R : BetaAt start [] afterRoot := ⟨body,arg0,rfl,rfl⟩
private def firstOriginal : BetaAt start [.arg] (.app (.lam body) arg1) := ⟨.var 0,arg1,rfl,rfl⟩
private def lastOriginal : BetaAt (.app (.lam body) arg1) [.arg] (.app (.lam body) (.var 0)) :=
  ⟨.var 0,.var 0,rfl,rfl⟩
private def firstCopy : BetaAt afterRoot [.fn] (.app arg1 arg0) := ⟨.var 0,arg1,rfl,rfl⟩
private def lastCopy : BetaAt (.app arg1 arg0) [.fn] (.app (.var 0) arg0) := ⟨.var 0,.var 0,rfl,rfl⟩
private def original := ParallelHistory.cons (singleContraction firstOriginal) (.single (singleContraction lastOriginal))
private def copy := ParallelHistory.cons (singleContraction firstCopy) (.single (singleContraction lastCopy))
private theorem ho : Atomic original := .cons firstOriginal (.single lastOriginal)
private theorem hc : Atomic copy := .cons firstCopy (.single lastCopy)
private def lift : ArgumentLift R copy original := {
  body := body
  argument := arg0
  redex := rfl
  occurrence := [.fn]
  isVariable := rfl
  localPaths := [[],[]]
  copy_paths := rfl
  original_paths := rfl
  parallelization := StepProjection.exists_projection (singleContraction R) original }
private def a0 : RedexWithHistory afterRoot :=
  ⟨.app arg1 arg0,.single (singleContraction firstCopy),⟨[.fn],lastCopy.redex⟩⟩
private def a : RedexWithHistory start :=
  ⟨.app (.lam body) arg1,.single (singleContraction firstOriginal),⟨[.arg],lastOriginal.redex⟩⟩
-- Proper prefixes are nonempty. Full projection also reduces the other
-- argument copy; only the designated point can be its Copy image.
example : ∃ (z : Term) (F : List Path) (program : ParallelHistory afterRoot z)
    (last : ParallelStep F a.target z) (q : RedexOcc z),
    StepProjection (singleContraction R) a.history program last ∧
    HistoryPrefix a0.history program ∧
    Copy a ⟨z,(ParallelHistory.single (singleContraction R)).append program,q⟩ ∧
    ∀ q' : RedexOcc z,Copy a0 ⟨z,program,q'⟩ → q'=q :=
  (RootExtraction.argumentPart copy hc original ho (by decide) lift).pointed_prefix_fiber
    a0 a ⟨lastCopy,.single firstCopy,rfl⟩ ⟨lastOriginal,.single firstOriginal,rfl⟩
#print axioms RootExtraction.pointed_prefix_fiber
#print axioms argument_pointed_projection_fiber
end PointedFiber
end Lamping.Checks.Phase4Bridges
