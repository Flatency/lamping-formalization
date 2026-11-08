import Lamping.Lambda.LabelOuterBarProvenance

namespace Lamping.Checks.LabelOuterBarProvenance
open Lambda Lambda.Labelled

private abbrev degree : Label := (Label.atom 1).over
private abbrev body : LTerm := .var (.atom 2) 0
private abbrev argument : LTerm := .lam (.atom 3) (.var (.atom 4) 0)
private abbrev source : LTerm := .app (.atom 0) (.lam degree body) argument
private abbrev target : LTerm := LTerm.contract (.atom 0) degree body argument

/-- Provenance applies to a non-atomic fired degree and a non-INIT source,
provided the forbidden outer marker is initially absent. -/
theorem non_atomic_degree_is_an_actual_firing : FiresDegree degree [[]] source target := by
  have history : History [[]] source target := .cons (.root _ _ _ _) (.nil _)
  have safe : source.OuterBarsSafe (fun payload=>payload≠degree) := by
    simp [degree,LTerm.OuterBarsSafe,Label.OuterBarsSafe,Label.atom,Label.over]
  have markerPresent : ¬target.OuterBarsSafe (fun payload=>payload≠degree) := by
    simp [target,degree,LTerm.OuterBarsSafe,Label.OuterBarsSafe,
      LTerm.contract,LTerm.prepend,LTerm.subst,LTerm.single,Label.concat,Label.over,Label.under,Label.atom]
  exact (history.outerBarsSafe_or_fires_degree safe).resolve_left markerPresent

private abbrev identity : Term := .lam (.var 0)
private abbrev bare : Term := .app (.app identity identity) identity
private abbrev original := initLabels bare
private abbrev firstResult := LTerm.contract (.atom 1) (.atom 2)
  (.var (.atom 3) 0) (.lam (.atom 4) (.var (.atom 5) 0))
private abbrev middle : LTerm := .app (.atom 0) firstResult (.lam (.atom 6) (.var (.atom 7) 0))
private abbrev secondDegree := firstResult.label
private abbrev finalTerm := LTerm.contract (.atom 0) secondDegree
  (.var (.atom 5) 0) (.lam (.atom 6) (.var (.atom 7) 0))

/-- Two actual beta events from one atomic INIT: the marker's degree is
minted by the SECOND event, not the initial function contraction. The
provenance witness retains the preceding path and existing labels. -/
theorem later_event_mints_the_marker :
    FiresDegree secondDegree [[.fn],[]] original finalTerm ∧
      original.degreeAt [.fn]≠some secondDegree := by
  have history : History [[.fn],[]] original finalTerm :=
    .cons (.fn (.root _ _ _ _)) (.cons (.root _ _ _ _) (.nil _))
  have member : finalTerm.label∈finalTerm.labels := List.mem_cons_self
  have marker : ¬finalTerm.label.OuterBarsSafe (fun payload=>payload≠secondDegree) := by
    simp [finalTerm,LTerm.contract,LTerm.prepend,LTerm.subst,LTerm.single,LTerm.label,
      Label.OuterBarsSafe,Label.concat,Label.over,Label.under,Label.atom]
  exact ⟨history.outer_bar_fired (init_is_INIT bare) member marker,by decide⟩

/-- A marker may already exist with no firing at all when initial safety
is dropped. This is why the provenance theorem exposes that premise. -/
theorem initial_marker_needs_no_firing :
    let existing : LTerm := .lam degree.over (.var (.atom 9) 0)
    ¬existing.OuterBarsSafe (fun payload=>payload≠degree) ∧¬FiresDegree degree [] existing existing := by
  intro existing
  refine ⟨by simp [existing,LTerm.OuterBarsSafe,Label.OuterBarsSafe,Label.over],?_⟩
  rintro ⟨before,path,after,current,next,equal,_first,_step,_atDegree,_last⟩
  have nonempty : before++path::after≠[] := by simp
  exact nonempty equal.symm

#print axioms StepAt.outerBarsSafe
#print axioms History.outerBarsSafe_or_fires_degree
#print axioms History.outer_bar_fired
#print axioms non_atomic_degree_is_an_actual_firing
#print axioms later_event_mints_the_marker
#print axioms initial_marker_needs_no_firing
end Lamping.Checks.LabelOuterBarProvenance
