import Lamping.Lambda.AtomicRowExistence
namespace Lamping.Lambda

/-- Identical actual contraction schedules transport identical old-name
lists, regardless of which names were selected as active. -/
theorem ParallelStep.residualSet_eq_of_paths (h : ParallelStep F t u)
    (k : ParallelStep G t u) (paths : h.paths=k.paths) (names : List Path) :
    h.residualSet names=k.residualSet names := by
  have hk : Marked.History h.paths (Marked.mark [] t) k.markedTarget.passive := by
    simpa only [paths] using k.tracked
  have same := h.tracked.deterministic hk
  unfold ParallelStep.residualSet Marked.setResidualPositions
  apply congrArg (fun f : Path → List Path => names.flatMap f)
  funext r
  have eq := congrArg (Marked.tracePositions r) same
  simpa only [Marked.passive_trace] using eq

/-- For a source singleton outside an internal ordinary history, every
vertical selection of its actual row remains literally that singleton. -/
theorem StepProjection.final_selection_singleton
    {vertical : ParallelStep F t u} {σ : ParallelHistory t v} {τ : ParallelHistory u w}
    {last : ParallelStep G v w} (row : StepProjection vertical σ τ last)
    (selected : F=[p]) (root : RedexOcc t) (hp : root.val=p)
    (ha : Atomic σ) (inside : Internal site σ) (outside : ¬∃ q, p=site++q) : G=[p] := by
  induction row generalizing p site with
  | nil => exact selected
  | @cons F H t u v w x σ y τ G last sq tail ih =>
    have halves := Atomic.split_append (ρ:=.single sq.second) (σ:=σ) ha
    obtain ⟨q,S,paths⟩ := halves.1.single_step
    have sourceInside : ∃ s, q=site++s := inside q (by
      change q∈sq.second.derivation.paths++σ.derivation.paths
      change q∈sq.second.paths++σ.derivation.paths
      rw [paths]; simp)
    have rootOutside : ¬∃ s, p=q++s := by
      rintro ⟨s,hs⟩
      obtain ⟨r,hr⟩ := sourceInside
      exact outside ⟨r++s,by simpa only [List.append_assoc] using hs.trans (congrArg (·++s) hr)⟩
    have normalized : (singleContraction S).residualSet [p]=[p] :=
      S.outside_residualSet_singleton ⟨p,by simpa only [←hp] using root.property⟩ rootOutside
    have nextSelection : sq.second.residualSet F=[p] := by
      calc
        sq.second.residualSet F=sq.second.residualSet [p] := congrArg sq.second.residualSet selected
        _=(singleContraction S).residualSet [p] := sq.second.residualSet_eq_of_paths (singleContraction S) paths _
        _=[p] := normalized
    have valid := ((Marked.completeOld_iff H t).mp sq.second.complete).1.general.valid (Marked.valid_mark H t)
    have member : p∈sq.second.residualSet F := by rw [nextSelection]; simp
    have redex := Marked.setResidualPositions_sound valid member
    rw [sq.second.target_eq] at redex
    let nextRoot : RedexOcc v := ⟨p,redex⟩
    have restInside : Internal site σ := by
      intro z hz
      exact inside z (by
        change z∈sq.second.derivation.paths++σ.derivation.paths
        exact List.mem_append_right _ hz)
    exact ih nextSelection nextRoot rfl halves.2 restInside outside

end Lamping.Lambda
