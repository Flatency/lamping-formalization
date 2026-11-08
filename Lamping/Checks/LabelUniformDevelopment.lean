import Lamping.Lambda.LabelUniformDevelopment
namespace Lamping.Checks.LabelUniformDevelopment
open Lambda Lambda.Labelled

private abbrev left : LTerm := .app (.atom 1) (.lam (.atom 2) (.var (.atom 3) 0))
  (.lam (.atom 4) (.var (.atom 5) 0))
private abbrev right : LTerm := .app (.atom 6) (.lam (.atom 2) (.var (.atom 7) 0))
  (.lam (.atom 8) (.var (.atom 9) 0))
private abbrev leftResult := LTerm.contract (.atom 1) (.atom 2) (.var (.atom 3) 0)
  (.lam (.atom 4) (.var (.atom 5) 0))
private abbrev rightResult := LTerm.contract (.atom 6) (.atom 2) (.var (.atom 7) 0)
  (.lam (.atom 8) (.var (.atom 9) 0))
private abbrev source : LTerm := .app (.atom 0) left right
private abbrev middle : LTerm := .app (.atom 0) leftResult right
private abbrev target : LTerm := .app (.atom 0) leftResult rightResult
private abbrev selection : List Path := [[.fn],[.arg]]
private abbrev schedule : List Path := [[.fn],[.arg]]
private def first : StepAt [.fn] source middle := .fn (.root _ _ _ _)
private def second : StepAt [.arg] middle target := .arg (.root _ _ _ _)
private def labels : History schedule source target := .cons first (.cons second (.nil _))
private abbrev markedTarget : Marked := .app [] (.lam (.var 0)) (.lam (.var 0))

private def step : ParallelStep selection source.erase target.erase := by
  refine ⟨schedule,markedTarget,(Marked.completeOld_iff _ _).mpr ⟨?_,?goal⟩,rfl⟩
  · change Marked.RelativeHistory schedule
      (.app [] (.red [[.fn]] (.var 0) (.lam (.var 0))) (.red [[.arg]] (.var 0) (.lam (.var 0)))) markedTarget
    exact .cons (.appL (.root _ _ _)) (.cons (.appR (.root _ _ _)) (.nil _))
  case goal => exact ⟨True.intro,True.intro⟩

private theorem selected (path : Path) (member : path∈selection) : source.degreeAt path=some (.atom 2) := by
  rcases List.mem_cons.mp member with rfl | rest
  · rfl
  · have equal : path=[.arg] := List.mem_singleton.mp rest
    subst path; rfl

private theorem initialSafe : source.OuterBarsSafe (fun payload=>payload≠Label.atom 2) := by
  simp [LTerm.OuterBarsSafe,Label.OuterBarsSafe,Label.atom]

/-- The second actual contraction starts AFTER this degree's marker was
minted. The theorem uses old-name alignment rather than stepwise freshness. -/
theorem two_events_with_unsafe_middle :
    History step.paths source target ∧step.paths.length=2 ∧
    ¬middle.OuterBarsSafe (fun payload=>payload≠Label.atom 2) ∧
    ((Label.atom 5)∈source.labels ↔(Label.atom 5).OuterBarsSafe (fun payload=>payload≠Label.atom 2)) := by
  refine ⟨labels,rfl,?_,?_⟩
  · intro middleSafe
    exact first.created_label_not_safe rfl (edge := [.fn]) (current := leftResult) rfl (Or.inl rfl)
      ((LTerm.outerBarsSafe_iff _ _).mp middleSafe _
        (LTerm.label_mem_of_subterm (show middle.subterm [.fn]=some leftResult from rfl)))
  · exact step.label_mem_iff_marker_free labels selected initialSafe
      (current := .var (.atom 5) 0) (edge := [.fn,.body]) rfl

theorem whole_schedule_old_and_new :
    (Label.atom 9)∈source.labels ∧rightResult.label∉source.labels := by
  refine ⟨step.marker_free_label_origin labels selected (current := .var (.atom 9) 0)
    (edge := [.arg,.body]) rfl True.intro,?_⟩
  intro member
  have safe := (step.label_mem_iff_marker_free labels selected initialSafe (edge := [.arg]) rfl).mp member
  have marked := second.created_label_not_safe rfl (edge := [.arg]) rfl (Or.inl rfl)
  exact marked safe

/-- Empty selection preserves actual marker-free labels on a source that
still contains two redexes; no normalization condition is substituted. -/
theorem empty_selection_old_label : (Label.atom 2)∈source.labels :=
  (ParallelStep.empty source.erase).marker_free_label_origin (.nil _)
    (degree := .atom 99) (by intro path member;cases member)
    (edge := [.fn,.fn]) rfl True.intro

end Lamping.Checks.LabelUniformDevelopment
#print axioms Lamping.Lambda.Marked.RelativeOldHistory.marker_free_label_origin
#print axioms Lamping.Lambda.ParallelStep.marker_free_label_origin
#print axioms Lamping.Lambda.ParallelStep.label_mem_iff_marker_free
#print axioms Lamping.Checks.LabelUniformDevelopment.two_events_with_unsafe_middle
#print axioms Lamping.Checks.LabelUniformDevelopment.whole_schedule_old_and_new
