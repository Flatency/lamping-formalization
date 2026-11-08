import Lamping.Lambda.DisjointHistoryPullback
namespace Lamping.Lambda

/-- For an argument-pointed source, first delete the disjoint suffix by
rule (i), then the entire function prefix by actual inverse rows and rule (ii).
The retained argument program includes its final contraction. -/
theorem ProtectedBlocks.extract_argument_pointed {ρ : ParallelHistory t u}
    (blocks : ProtectedBlocks cut ρ) (ordinary : Atomic ρ) (last : BetaAt u p v)
    (atArgument : p=(cut++[.arg])++q) :
    ∃ w, ∃ source : ParallelHistory t w, ∃ sourceAtomic : Atomic source,
      Internal (cut++[.arg]) source ∧
      Extraction (.of (ρ.append (.single (singleContraction last))) (ordinary.append (.single last)))
        (.of source sourceAtomic) := by
  obtain ⟨mid,endArg,function,argument,outside,hf,ha,whole,fi,ai,forest⟩ := blocks
  have apart : ∀ r∈outside.derivation.paths,DisjointPositions r p := by
    intro r hr
    rw [atArgument,List.append_assoc]
    exact forest.paths_apart_descendant ([.arg]++q) r hr
  obtain ⟨w,initial,removed⟩ := Atomic.extract_apart_suffix (function.append argument)
    (hf.append ha) forest.atomic last apart
  have programInside : Internal (cut++[.arg]) (argument.append (.single (singleContraction initial))) := by
    intro r hr
    rw [ParallelHistory.derivation_append] at hr
    change r∈argument.derivation.paths++[p] at hr
    rcases List.mem_append.mp hr with earlier | last
    · exact ai r earlier
    · exact ⟨q,(List.mem_singleton.mp last).trans atArgument⟩
  have functionApart : ∀ r∈function.derivation.paths,DisjointPositions r (cut++[.arg]) := by
    intro r hr
    obtain ⟨s,eq⟩ := fi r hr
    rw [eq]
    have base : DisjointPositions (cut++[.fn]) (cut++[.arg]) :=
      (DisjointPositions.head_ne (by intro eq; cases eq) : DisjointPositions [.fn] [.arg]).prefix cut
    exact base.descend_left s
  obtain ⟨z,source,sourceAtomic,_,sourceInside,removedFunction⟩ := hf.extract_disjoint_prefix
    (argument.append (.single (singleContraction initial))) (ha.append (.single initial)) programInside
    (by simp [ParallelHistory.length_append,ParallelHistory.single,ParallelHistory.length]) functionApart
  refine ⟨z,source,sourceAtomic,sourceInside,?_⟩
  have sourceEq : ExtractionRun.of (ρ.append (.single (singleContraction last))) (ordinary.append (.single last)) =
      .of (((function.append argument).append outside).append (.single (singleContraction last)))
        (((hf.append ha).append forest.atomic).append (.single last)) := by
    apply ExtractionRun.ext_paths
    change (ρ.append (.single (singleContraction last))).derivation.paths =
      (((function.append argument).append outside).append (.single (singleContraction last))).derivation.paths
    simp only [whole,ParallelHistory.append_assoc]
  have middleEq : ExtractionRun.of ((function.append argument).append (.single (singleContraction initial)))
      ((hf.append ha).append (.single initial)) =
      .of (function.append (argument.append (.single (singleContraction initial))))
        (hf.append (ha.append (.single initial))) := by
    apply ExtractionRun.ext_paths
    simp only [ExtractionRun.of,ParallelHistory.derivation_append,Derivation.append,List.append_assoc]
  rw [sourceEq]
  exact removed.trans (by rw [middleEq]; exact removedFunction)

end Lamping.Lambda
