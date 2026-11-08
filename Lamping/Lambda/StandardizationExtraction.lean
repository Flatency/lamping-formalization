import Lamping.Lambda.StandardizationRank
namespace Lamping.Lambda
/-- Every concrete contraction in a right-side parallel history is right of
the cut. The claim is extracted from actual complete-development paths. -/
theorem RightHistory.paths_right {ρ : ParallelHistory t u} (right : RightHistory cut ρ) :
    ∀ p∈ρ.derivation.paths, LeftOf cut p := by
  induction right with
  | nil => simp [ParallelHistory.derivation,Derivation.nil]
  | cons h row allRight tail ih =>
    intro p hp
    change p∈h.paths++row.derivation.paths at hp
    rcases List.mem_append.mp hp with first | rest
    · apply ((Marked.completeOld_iff _ _).mp h.complete).1.right_paths (cut:=cut) _ p first
      intro q hq
      obtain ⟨selected,valid⟩ := (Marked.active_mark _ _ q).mp hq
      exact allRight ⟨q,(mem_redexPositions _ q).mp valid⟩ selected
    · exact ih p rest

theorem Derivation.left_survives (h : Derivation t u) (s : RedexOcc t)
    (right : ∀ p∈h.paths, LeftOf s.val p) :
    ∃ q : RedexOcc u, q.val=s.val ∧ h.Residual s q := by
  obtain ⟨target,tracked,erase⟩ := h.tracked
  have fixed := tracked.trace_fixed_right right (fun p hp => (Marked.initial_residual [] t s p).mp hp)
  have alive : s.val∈Marked.tracePositions s.val target := by
    rw [fixed]
    exact (Marked.initial_residual [] t s s.val).mpr rfl
  have isRedex := Marked.tracePositions_sound (tracked.valid (Marked.valid_mark [] t)) alive
  rw [erase] at isRedex
  exact ⟨⟨s.val,isRedex⟩,rfl,⟨target,tracked,erase,alive⟩⟩
/-- Pull a genuinely selected old redex out of any right prefix and any later
complete step. The resulting same-length remainder strictly decreases the
reverse chronological cost vector, derived from active development weight. -/
theorem RightHistory.pull_selected {ρ : ParallelHistory t u} {cut : Path}
    (right : RightHistory cut ρ) (s : RedexOcc t) (atCut : s.val=cut)
    (step : ParallelStep G u v) (selected : cut∈G) (suffix : ParallelHistory v w) :
    ∃ (z : Term) (source : BetaAt t cut z) (tail : ParallelHistory z w),
      PermEq (ρ.append (.cons step suffix)) ((ParallelHistory.single (singleContraction source)).append tail) ∧
      tail.length=(ρ.append (.cons step suffix)).length ∧
      HistoryCost.ListLt tail.costs (ρ.append (.cons step suffix)).costs := by
  have paths : ∀ p∈ρ.derivation.paths, LeftOf s.val p := by
    intro p hp
    rw [atCut]
    exact right.paths_right p hp
  obtain ⟨q,qAt,_⟩ := ρ.derivation.left_survives s paths
  have validAtCut : ∃ redex, subtermAt u cut=some redex ∧ IsRedex redex := by
    rw [←atCut,←qAt]
    exact q.property
  let chosen : RedexOcc u := ⟨cut,validAtCut⟩
  obtain ⟨z,head,rest,factor⟩ := step.selected_factor chosen selected
  obtain ⟨z',source,row,pull,length⟩ := right.pull_step s atCut head
  refine ⟨z',source,(row.append (.single rest)).append suffix,?_,?_,?_⟩
  · have split := PermEq.prepend ρ (factor.append suffix)
    have move := pull.append ((ParallelHistory.single rest).append suffix)
    exact .trans (by simpa only [ParallelHistory.append_assoc,ParallelHistory.append,ParallelHistory.single] using split)
      (by simpa only [ParallelHistory.append_assoc,ParallelHistory.append,ParallelHistory.single] using move)
  · simp only [ParallelHistory.length_append,ParallelHistory.single,ParallelHistory.length,length]
    omega
  · rw [ParallelHistory.costs_append,ParallelHistory.costs_append,ParallelHistory.costs_append]
    simp only [ParallelHistory.single,ParallelHistory.costs,List.nil_append,List.append_assoc]
    change HistoryCost.ListLt (suffix.costs ++ ([Marked.weight (fun _ => 1) (Marked.mark ((singleContraction head).residualSet G) z)] ++ row.costs))
      (suffix.costs ++ ([Marked.weight (fun _ => 1) (Marked.mark G u)] ++ ρ.costs))
    apply HistoryCost.ListLt.prefix
    exact .head _ _ (head.selected_residual_weight_lt selected (fun _ => 1))
end Lamping.Lambda
