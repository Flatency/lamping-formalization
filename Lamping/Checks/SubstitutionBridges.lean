import Lamping.Lambda.ValidParallelSubstitution
import Lamping.Lambda.RenameProjectionStandardness
import Lamping.Lambda.ExtractionContextLift
import Lamping.Lambda.ParallelRename
namespace Lamping.Checks.SubstitutionBridges
open Lamping.Lambda

private def I : Term := .lam (.var 0)
private def redex : Term := .app I (.var 0)
private def invalid : ParallelStep [[]] (.var 0) (.var 0) :=
  ⟨[],.var 0,⟨.nil _,rfl⟩,rfl⟩
private theorem nil_target (h : Marked.RelativeHistory [] a b) : a=b := by cases h; rfl
private theorem no_before_empty {p : Path} : ¬LeftOf p [] := by intro h; cases h
-- Invalid source selections can become active after substitution; the old
-- empty schedule then cannot be a complete development.
example : ¬∃ k : ParallelStep [[]] redex redex,k.paths=invalid.paths := by
  rintro ⟨k,paths⟩
  have complete := (Marked.completeOld_iff [[]] redex).mp k.complete
  have history := complete.1
  change k.paths=[] at paths
  rw [paths] at history
  have same := nil_target history
  have normal := complete.2
  rw [←same] at normal
  exact normal

-- Even valid empty selections do not make arbitrary invalid OLD names
-- natural: fresh initialization after substitution names the new root.
example : (ParallelStep.empty redex).paths=(ParallelStep.empty (.var 0)).paths := rfl
example : (ParallelStep.empty redex).residualSet [[]] ≠
    (ParallelStep.empty (.var 0)).residualSet [[]] := by
  intro equal
  change [[]]=[] at equal
  cases equal

private def duplicateSource : Term := .app (.lam (.app (.var 0) (.var 0))) redex
private def duplicateTarget : Term := .app redex redex
private def R : BetaAt duplicateSource [] duplicateTarget :=
  ⟨.app (.var 0) (.var 0),redex,rfl,rfl⟩
private theorem validHead : SelectionValid duplicateSource [[]] := by
  intro p hp; cases List.mem_singleton.mp hp; exact R.redex
private theorem validNames : SelectionValid duplicateSource [[.arg],[.arg]] := by
  intro p hp
  have equal : p=[Step.arg] := by simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,or_self] using hp
  cases equal
  exact ⟨redex,rfl,True.intro⟩
example (σ : Nat → Term) :
    ((singleContraction R).substitute σ validHead).paths=[[]] := by
  rw [ParallelStep.substitute_paths]
  rfl
example (σ : Nat → Term) :
    ((singleContraction R).substitute σ validHead).residualSet [[.arg],[.arg]]=
      [[.fn],[.arg],[.fn],[.arg]] := by
  rw [(singleContraction R).substitution_residualSet_eq
    ((singleContraction R).substitute σ validHead) (ParallelStep.substitute_paths _ _ _) validNames]
  rfl

namespace ForwardStandard
private def start : Term := .app (.lam (.app (.app (.var 0) (.var 1)) (.var 2))) I
private def middle : Term := .app (.app I (.var 0)) (.var 1)
private def finish : Term := .app (.var 0) (.var 1)
private def first : BetaAt start [] middle := ⟨.app (.app (.var 0) (.var 1)) (.var 2),I,rfl,rfl⟩
private def last : BetaAt middle [.fn] finish := ⟨.var 0,.var 0,rfl,rfl⟩
private def program := ParallelHistory.cons (singleContraction first) (.single (singleContraction last))
private theorem ordinary : Atomic program := .cons first (.single last)
private theorem standard : Standard program := by
  refine .cons (singleContraction first) ⟨[],first.redex⟩ (leftmost_singleton _) ?_
    (Standard.single_step (singleContraction last) ⟨_,last.redex⟩ (leftmost_singleton _))
  intro s before
  exact False.elim (no_before_empty before)
private def context : SyntaxContext := .frame (.arg (.var 9)) (.frame .body .hole)
private noncomputable def copy := context.liftHistory (program.rename (fun _ => 7))
-- Both free variables are merged by a noninjective renaming, then the same
-- actual two-beta program is placed beneath a lambda and an argument edge.
example : Standard copy := by
  change Standard (context.liftHistory (program.rename (fun _ => 7)))
  apply Atomic.region_rename_standard_project ordinary
    (context.liftAtomic (ordinary.rename (fun _ => 7)))
    (pre := []) (pre' := context.path) (a := start) (ren := fun _ => 7)
    rfl (context.lookup _) [[],[.fn]]
  · rfl
  · rw [context.liftHistory_paths,ParallelHistory.rename_derivation_paths]
    rfl
  · exact standard
example : rename (fun _ => 7) (.var 0) = rename (fun _ => 7) (.var 1) := rfl
end ForwardStandard

#print axioms ParallelStep.substitute_exists
#print axioms ParallelStep.substitution_residualSet_eq
#print axioms UsedSource.region_rename_reflect
#print axioms Atomic.region_rename_standard_project
end Lamping.Checks.SubstitutionBridges
