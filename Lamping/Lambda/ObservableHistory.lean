import Lamping.Lambda.PermutationResidual

namespace Lamping.Lambda

/-- Empty selections have no actual contractions, even when the source
contains redexes. This does not identify nonempty self-reductions with silence. -/
theorem ParallelStep.empty_paths (step : ParallelStep [] t u) : step.paths=[] := by
  have no_steps {ps marked} (history : Marked.RelativeOldHistory [] ps (Marked.mark [] t) marked) : ps=[] := by
    cases history with
    | nil => rfl
    | cons turn member rest => simp [Marked.setResidualPositions] at member
  exact no_steps step.complete.1

namespace ParallelHistory

/-- Every retained boundary selects at least one old name. Validity and
whole-family maximality remain separate obligations. -/
inductive Observable : ParallelHistory t u → Prop where
  | nil (t) : Observable (.nil t)
  | cons {F : List Path} {step : ParallelStep F t u} {tail : ParallelHistory u v}
      (positive : F≠[]) (rest : Observable tail) : Observable (.cons step tail)

/-- Delete only empty-selection boundaries. All retained steps and the
literal underlying occurrence-indexed derivation are preserved. This is
not a completion operation on arbitrary derivations. -/
theorem exists_observable (raw : ParallelHistory t u) :
    ∃ observed : ParallelHistory t u,
      Observable observed ∧ raw.derivation=observed.derivation ∧ PermEq raw observed := by
  induction raw with
  | nil t => exact ⟨.nil t,.nil t,rfl,.refl _⟩
  | @cons t middle target F step tail ih =>
    by_cases empty : F=[]
    · subst F
      have endpoint : middle=t := step.endpoint (ParallelStep.empty t)
      subst middle
      obtain ⟨observed,positive,same,permutation⟩ := ih
      refine ⟨observed,positive,?_,?_⟩
      · apply Derivation.ext
        change step.paths++tail.derivation.paths=observed.derivation.paths
        rw [step.empty_paths,List.nil_append,same]
      · exact .trans (.comp (.empty step) (.refl tail)) permutation
    · obtain ⟨observed,positive,same,permutation⟩ := ih
      refine ⟨.cons step observed,.cons empty positive,?_,?_⟩
      · change step.derivation.append tail.derivation=step.derivation.append observed.derivation
        rw [same]
      · exact .comp (.refl (.single step)) permutation

end ParallelHistory
end Lamping.Lambda
