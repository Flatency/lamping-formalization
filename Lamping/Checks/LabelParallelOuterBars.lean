import Lamping.Lambda.LabelParallelOuterBars

namespace Lamping.Checks.LabelParallelOuterBars
open Lambda Lambda.Labelled

private abbrev identity : Term := .lam (.var 0)
private abbrev bare : Term := .app (.lam (.app (.var 0) (.var 0))) (.app identity identity)
private abbrev source := initLabels bare
private abbrev selection : List Path := [[],[.arg]]
private def allowed (degree : Label) : Prop := degree=Label.atom 1 ∨degree=Label.atom 6

/-- A real finite development may duplicate an OLD selected argument.
Every schedule still introduces only the two selected source degrees;
newly created redexes are not silently reselected. -/
theorem duplicated_old_selection_has_only_selected_markers :
    ∃ target : LTerm,∃ step : ParallelStep selection source.erase target.erase,
      History step.paths source target ∧target.OuterBarsSafe allowed := by
  obtain ⟨ps,marked,complete⟩ := Marked.completeOld_exists selection source.erase
  have actual := ((Marked.completeOld_iff _ _).mp complete).1.general.betaHistory
  rw [Marked.erase_mark] at actual
  obtain ⟨target,labels,erased⟩ := lift_history actual source rfl
  let step : ParallelStep selection source.erase target.erase := ⟨ps,marked,complete,erased.symm⟩
  refine ⟨target,step,labels,step.outerBarsSafe labels ((init_is_INIT bare).outerBarsSafe _) ?_⟩
  intro path member degree atDegree
  rcases List.mem_cons.mp member with root | rest
  · subst path
    have same : degree=Label.atom 1 := (Option.some.inj atDegree).symm
    exact .inl same
  · have samePath : path=[.arg] := List.mem_singleton.mp rest
    subst path
    have same : degree=Label.atom 6 := (Option.some.inj atDegree).symm
    exact .inr same

/-- Empty selection remains silent on a source that still contains redexes,
and preserves even the policy that permits no outer markers at all. -/
theorem empty_selection_is_not_normalization :
    source.OuterBarsSafe (fun _=>False) ∧IsRedex source.erase := by
  have labels : History (ParallelStep.empty source.erase).paths source source := .nil _
  exact ⟨(ParallelStep.empty source.erase).outerBarsSafe labels
    ((init_is_INIT bare).outerBarsSafe _) (by intro path member;cases member),True.intro⟩

#print axioms Marked.RelativeOldHistory.outerBarsSafe
#print axioms ParallelStep.outerBarsSafe
#print axioms duplicated_old_selection_has_only_selected_markers
#print axioms empty_selection_is_not_normalization
end Lamping.Checks.LabelParallelOuterBars
