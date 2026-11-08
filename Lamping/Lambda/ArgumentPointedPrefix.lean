import Lamping.Lambda.ArgumentParallelization
import Lamping.Lambda.ArgumentLiftSplits
namespace Lamping.Lambda

private theorem list_last (xs : List α) (nonempty : xs≠[]) :
    ∃ (pre : List α) (last : α),xs=pre++[last] := by
  cases eq : xs.reverse with
  | nil =>
    have empty := congrArg List.reverse eq
    simp only [List.reverse_reverse,List.reverse_nil] at empty
    exact False.elim (nonempty empty)
  | cons last rest =>
    refine ⟨rest.reverse,last,?_⟩
    have same := congrArg List.reverse eq
    simpa only [List.reverse_reverse,List.reverse_cons] using same

private theorem append_last_injective (h : xs++[a]=ys++[b]) : xs=ys ∧ a=b := by
  have reversed := congrArg List.reverse h
  simp only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.singleton_append] at reversed
  obtain ⟨last,same⟩ := List.cons.inj reversed
  refine ⟨?_,last⟩
  have same' := congrArg List.reverse same
  simpa only [List.reverse_reverse] using same'

/-- Restrict a specified argument-copy lift to the actual prefixes before
 the last contractions of both ordinary programs. The mirrored local
 program is recovered from the two complete pointed representations. -/
theorem ArgumentLift.pointed_prefix {R : BetaAt t p u}
    (lift : ArgumentLift R copy original) (hc : Atomic copy) (ho : Atomic original)
    (a : RedexWithHistory u) (b : RedexWithHistory t)
    (sourceRep : RunRepresents (.of copy hc) a)
    (targetRep : RunRepresents (.of original ho) b) :
    ∃ prefixLift : ArgumentLift R a.history b.history, prefixLift.occurrence=lift.occurrence := by
  rcases a with ⟨aTarget,aHistory,aRedex⟩
  rcases b with ⟨bTarget,bHistory,bRedex⟩
  obtain ⟨lastA,ha,copyEq⟩ := sourceRep
  obtain ⟨lastB,hb,originalEq⟩ := targetRep
  change copy=aHistory.append (.single (singleContraction lastA)) at copyEq
  change original=bHistory.append (.single (singleContraction lastB)) at originalEq
  have nonempty : lift.localPaths≠[] := by
    intro empty
    have paths := lift.copy_paths
    conv at paths => lhs; rw [copyEq,ParallelHistory.derivation_append,ParallelHistory.single_derivation]
    rw [empty,List.map_nil] at paths
    have length := congrArg List.length paths
    simp only [Derivation.append,List.length_append] at length
    change aHistory.derivation.paths.length+1=0 at length
    omega
  obtain ⟨program,last,localEq⟩ := list_last lift.localPaths nonempty
  have copied := lift.copy_paths
  conv at copied => lhs; rw [copyEq,ParallelHistory.derivation_append,ParallelHistory.single_derivation]
  rw [localEq,List.map_append,List.map_cons,List.map_nil] at copied
  change aHistory.derivation.paths++[aRedex.val]=
    program.map (fun q => (p++lift.occurrence)++q)++[(p++lift.occurrence)++last] at copied
  have aPrefix := (append_last_injective copied).1
  have originalPaths := lift.original_paths
  conv at originalPaths => lhs; rw [originalEq,ParallelHistory.derivation_append,ParallelHistory.single_derivation]
  rw [localEq,List.map_append,List.map_cons,List.map_nil] at originalPaths
  change bHistory.derivation.paths++[bRedex.val]=
    program.map (fun q => (p++[.arg])++q)++[(p++[.arg])++last] at originalPaths
  have bPrefix := (append_last_injective originalPaths).1
  have inside : Internal (p++lift.occurrence) aHistory := by
    intro name hn
    rw [aPrefix] at hn
    obtain ⟨q,_,he⟩ := List.mem_map.mp hn
    exact ⟨q,he.symm⟩
  obtain ⟨newTarget,newOriginal,newAtomic,prefixLift,occEq⟩ :=
    argument_lift_exists R lift.redex lift.isVariable aHistory inside
  have sameProgram : prefixLift.localPaths=program := by
    apply mapped_prefix_paths_injective (p++lift.occurrence)
    have paths := prefixLift.copy_paths
    rw [occEq] at paths
    exact paths.symm.trans aPrefix
  have samePaths : newOriginal.derivation.paths=bHistory.derivation.paths := by
    rw [prefixLift.original_paths,sameProgram,bPrefix]
  have endpoint := newOriginal.derivation.valid.deterministic (by
    have valid := bHistory.derivation.valid
    rw [←samePaths] at valid
    exact valid)
  cases endpoint
  have histories := newAtomic.paths_injective hb samePaths
  cases histories
  exact ⟨prefixLift,occEq⟩

end Lamping.Lambda
