import Lamping.Lambda.CopyInitialExtraction
import Lamping.Lambda.NoTagTransport
import Lamping.Lambda.CopyLeftExtraction
import Lamping.Lambda.StandardProtectedBlocks
import Lamping.Lambda.DisjointHistoryPullback
import Lamping.Lambda.RightSiblingExtraction
import Lamping.Lambda.FunctionProjectionStandardness
import Lamping.Lambda.ApplicationRowDiamond
namespace Lamping.Checks.CopyExtraction
open Lambda
example (initial : RedexOcc m) (b : RedexWithHistory m)
    (copy : Copy ⟨m,.nil m,initial⟩ b) (represented : RunRepresents r b)
    (initialStep : BetaAt m initial.val w) :
    Extraction r (.of (.single (singleContraction initialStep)) (.single initialStep)) :=
  copy.initial_extraction initial b represented initialStep
abbrev delta : Term := .lam (.app (.var 0) (.var 0))
abbrev omegaTerm : Term := .app delta delta
abbrev twins : Term := .app omegaTerm omegaTerm
def rightStep : BetaAt twins [.arg] twins := ⟨.app (.var 0) (.var 0),delta,rfl,rfl⟩
def leftStep : BetaAt twins [.fn] twins := ⟨.app (.var 0) (.var 0),delta,rfl,rfl⟩
example : Extraction
    (.of (((ParallelHistory.single (singleContraction rightStep)).append (.single (singleContraction rightStep))).append (.single (singleContraction leftStep)))
      (((Atomic.single rightStep).append (.single rightStep)).append (.single leftStep)))
    (.of (.single (singleContraction leftStep)) (.single leftStep)) := by
  let initial : RedexOcc twins := ⟨[.fn],leftStep.redex⟩
  have alive : (singleContraction rightStep).derivation.Residual initial initial :=
    (rightStep.disjoint_residual_iff initial (DisjointPositions.head_ne (by intro eq; cases eq)) initial).mpr rfl
  apply ((Atomic.single rightStep).append (.single rightStep)).extract_initial_residual initial leftStep _ leftStep
  rw [ParallelHistory.derivation_append,Derivation.residual_append]
  exact ⟨initial,by simpa only [ParallelHistory.single_derivation] using alive,
    by simpa only [ParallelHistory.single_derivation] using alive⟩
#print axioms Atomic.extract_initial_residual
#print axioms Copy.initial_extraction

def leftThenRight : ParallelHistory twins twins :=
  .cons (singleContraction leftStep) (.single (singleContraction rightStep))
theorem leftThenRight_standard : Standard leftThenRight := by
  refine .cons _ ⟨[.fn],leftStep.redex⟩ (leftmost_singleton _) ?_ (Standard.single_step _ ⟨[.arg],rightStep.redex⟩ (leftmost_singleton _))
  apply DoesNotReturnLeft.of_right
  intro old before
  apply (Atomic.cons leftStep (Atomic.single rightStep)).right_of_paths
  intro p hp
  change p∈[[.fn],[.arg]] at hp
  rcases List.mem_cons.mp hp with same | same
  · simpa [same] using before
  · have eq : p=[.arg] := by simpa using same
    rw [eq]
    exact before.trans (.branch [] [])
example : ∃ mid, ∃ f : ParallelHistory twins mid, ∃ a : ParallelHistory mid twins,
    leftThenRight=f.append a ∧ Internal [.fn] f ∧ Internal [.arg] a := by
  obtain ⟨mid,f,a,_,_,whole,fi,ai⟩ := (Atomic.cons leftStep (Atomic.single rightStep)).standard_app_blocks
    rfl (by intro p hp; change p∈[[.fn],[.arg]] at hp; simp only [List.mem_cons,List.not_mem_nil,or_false] at hp; rcases hp with rfl | rfl <;> simp)
    leftThenRight_standard
  exact ⟨mid,f,a,whole,fi,ai⟩
example : ¬Standard (ParallelHistory.cons (singleContraction rightStep) (.single (singleContraction leftStep))) := by
  intro standard
  have inside := (Atomic.single leftStep).app_arg_stays rightStep
    (by intro p hp; change p∈[[.arg],[.fn]] at hp; simp only [List.mem_cons,List.not_mem_nil,or_false] at hp; rcases hp with rfl | rfl <;> simp) standard
  obtain ⟨q,eq⟩ := inside [.fn] (by simp [ParallelHistory.derivation,Derivation.append,ParallelStep.derivation,singleContraction])
  cases eq
example {ρ : ParallelHistory t u} (ordinary : Atomic ρ) (root : BetaAt t cut v) (right : RightHistory cut ρ) (standard : Standard ρ) :
    ProtectedBlocks cut ρ := ordinary.standard_protected_blocks root right standard
#print axioms Copy.head_order
#print axioms Copy.protected_target_head
#print axioms Copy.common_of_left_pointed
#print axioms Atomic.app_arg_stays
#print axioms Atomic.standard_app_blocks
#print axioms Atomic.standard_internal_right_reflect
#print axioms DisjointBlocks.mapped
#print axioms ProtectedBlocks.mapped
#print axioms Atomic.standard_protected_blocks

/-- An actual disjoint inverse row and rule (ii) recover the left program
from a right contraction followed by two left contractions. -/
example : ∃ v, ∃ source : ParallelHistory twins v, ∃ ordinary : Atomic source,
    source.derivation.paths=[[.fn],[.fn]] ∧
    Extraction (.of ((ParallelHistory.single (singleContraction rightStep)).append
      (.cons (singleContraction leftStep) (.single (singleContraction leftStep))))
      ((Atomic.single rightStep).append (.cons leftStep (.single leftStep)))) (.of source ordinary) := by
  let program : ParallelHistory twins twins := .cons (singleContraction leftStep) (.single (singleContraction leftStep))
  have atomic : Atomic program := .cons leftStep (.single leftStep)
  have inside : Internal [.fn] program := by
    intro p hp
    change p∈[[.fn],[.fn]] at hp
    have eq : p=[.fn] := by simpa using hp
    exact ⟨[],eq⟩
  obtain ⟨v,source,ordinary,paths,_,removed⟩ := (Atomic.single rightStep).extract_disjoint_prefix
    program atomic inside (by decide) (by
      intro p hp
      have eq : p=[.arg] := by simpa [ParallelHistory.single_derivation,ParallelStep.derivation,singleContraction] using hp
      rw [eq]
      exact DisjointPositions.head_ne (by intro eq; cases eq))
  exact ⟨v,source,ordinary,paths,removed⟩
#print axioms Atomic.apart_pointed_ancestor
#print axioms Atomic.extract_apart_suffix
#print axioms ProtectedBlocks.extract_function_pointed
#print axioms Atomic.disjoint_row_pullback
#print axioms Atomic.extract_disjoint_prefix

abbrev triples : Term := .app twins omegaTerm
def innerRight : BetaAt triples [.fn,.arg] triples :=
  ⟨.app (.var 0) (.var 0),delta,rfl,rfl⟩
def outerRight : BetaAt triples [.arg] triples :=
  ⟨.app (.var 0) (.var 0),delta,rfl,rfl⟩
/-- The two right siblings of cut fn/fn are genuinely different subtrees.
The final pointed occurrence selects the outer sibling and deletes the
earlier inner-sibling contraction by an actual extraction. -/
example : ∃ site, DisjointPositions [.fn,.fn] site ∧
    ∃ w, ∃ source : ParallelHistory triples w, ∃ ordinary : Atomic source,
      0<source.length ∧ Internal site source ∧
      Extraction (.of ((ParallelHistory.single (singleContraction innerRight)).append (.single (singleContraction outerRight)))
        ((Atomic.single innerRight).append (.single outerRight))) (.of source ordinary) := by
  have right : RightHistory [.fn,.fn] (.single (singleContraction innerRight)) :=
    (Atomic.single innerRight).right_of_paths (by
      intro p hp
      have eq : p=[.fn,.arg] := by simpa [ParallelHistory.single_derivation,ParallelStep.derivation,singleContraction] using hp
      rw [eq]
      exact .child .fn (.branch [] []))
  exact right.extract_right_pointed (.single innerRight) outerRight (.branch [.fn] [])
    (DisjointPositions.head_ne (by intro eq; cases eq))
#print axioms ProtectedBlocks.extract_argument_pointed
#print axioms LeftOf.right_sibling
#print axioms Atomic.extract_local_program
#print axioms RightHistory.extract_right_pointed

abbrev identityTerm : Term := .lam (.var 0)
abbrev functionSource : Term := .app (.lam (.app (.var 0) omegaTerm)) identityTerm
abbrev functionTarget : Term := .app identityTerm omegaTerm
def creatingRoot : BetaAt functionSource [] functionTarget :=
  ⟨.app (.var 0) omegaTerm,identityTerm,rfl,rfl⟩
def functionLoop : BetaAt functionSource [.fn,.body,.arg] functionSource :=
  ⟨.app (.var 0) (.var 0),delta,rfl,rfl⟩
def projectedLoop : BetaAt functionTarget [.arg] functionTarget :=
  ⟨.app (.var 0) (.var 0),delta,rfl,rfl⟩
def createdBeta : BetaAt functionTarget [] omegaTerm := ⟨.var 0,omegaTerm,rfl,rfl⟩
/-- The outer beta creates an actual earlier root redex. The supplied
function projection remains standard and never uses that new root identity. -/
example : ∃ G, ∃ last : ParallelStep G functionSource functionTarget,
    StepProjection (singleContraction creatingRoot) (.single (singleContraction functionLoop))
      (.single (singleContraction projectedLoop)) last ∧
    Standard ((ParallelHistory.single (singleContraction creatingRoot)).append (.single (singleContraction projectedLoop))) ∧
    ¬UsedSource (.single (singleContraction projectedLoop)) ⟨[],createdBeta.redex⟩ := by
  obtain ⟨G,last,row⟩ := singleton_projection_row creatingRoot functionLoop projectedLoop (by decide)
  have inside : Internal [.fn] (.single (singleContraction functionLoop)) := by
    intro p hp
    have eq : p=[.fn,.body,.arg] := by simpa [ParallelHistory.single_derivation,ParallelStep.derivation,singleContraction] using hp
    exact ⟨[.body,.arg],eq⟩
  have sourceStandard : Standard (.single (singleContraction functionLoop)) :=
    Standard.single_step _ ⟨[.fn,.body,.arg],functionLoop.redex⟩ (leftmost_singleton _)
  have projectedStandard := (Atomic.single functionLoop).function_projection_standard creatingRoot inside row (.single projectedLoop) sourceStandard
  have right : RightHistory [] (.single (singleContraction projectedLoop)) :=
    (Atomic.single projectedLoop).right_of_paths (by
      intro p hp
      have eq : p=[.arg] := by simpa [ParallelHistory.single_derivation,ParallelStep.derivation,singleContraction] using hp
      rw [eq]; exact .outer _ _)
  exact ⟨G,last,row,projectedStandard.1,right.not_used_self ⟨[],createdBeta.redex⟩⟩
#print axioms StepProjection.passive_tracking_diamond
#print axioms UsedSource.region_project_reflect
#print axioms BetaAt.region_left_reflect
#print axioms Atomic.region_standard_project
#print axioms Atomic.function_projection_standard
end Lamping.Checks.CopyExtraction

