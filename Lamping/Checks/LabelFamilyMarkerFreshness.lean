import Lamping.Lambda.LabelFamilyMarkerFreshness

namespace Lamping.Checks.LabelFamilyMarkerFreshness
open Lambda Lambda.Labelled

private abbrev identity : Term := .lam (.var 0)
private abbrev bare : Term := .app (.app identity identity) identity
private abbrev original := initLabels bare
private abbrev firstResult := LTerm.contract (.atom 1) (.atom 2)
  (.var (.atom 3) 0) (.lam (.atom 4) (.var (.atom 5) 0))
private abbrev middle : LTerm := .app (.atom 0) firstResult (.lam (.atom 6) (.var (.atom 7) 0))
private def turn : StepAt [.fn] original middle := .fn (.root _ _ _ _)
private abbrev parallel := singleContraction turn.betaAt
private abbrev program := ParallelHistory.single parallel
private abbrev nextDegree := firstResult.label
private def nextRedex : RedexOcc middle.erase :=
  ⟨[],.app identity identity,rfl,True.intro⟩

private theorem whole : CompleteFamilyStep (ParallelHistory.nil original.erase) parallel := by
  let representative : RedexOcc original.erase := ⟨[.fn],turn.betaAt.redex⟩
  refine ⟨?_,representative,List.mem_singleton_self _,?_⟩
  · intro path member
    have same : path=[.fn] := List.mem_singleton.mp member
    subst path
    exact turn.betaAt.redex
  · intro candidate
    rw [initial_families_injective]
    exact ⟨fun selected=>Subtype.ext (List.mem_singleton.mp selected).symm,
      fun same=>by rw [←same];exact List.mem_singleton_self _⟩

/-- After one actual whole-family step, an older marker is present, but
the newly created current redex's non-atomic degree is still fresh. The
global INIT and all labels are transported through the actual prefix. -/
theorem actual_complete_prefix_has_fresh_next_marker :
    middle.OuterBarsSafe (fun payload=>payload≠nextDegree) ∧
      ¬middle.OuterBarsSafe (fun payload=>payload≠Label.atom 2) := by
  have complete : CompleteDerivation program := .step (.nil _) whole
  have labels : History program.derivation.paths original middle := .cons turn (.nil _)
  refine ⟨complete_prefix_outer_bars_fresh (init_is_INIT bare) program complete labels nextRedex rfl,?_⟩
  simp [firstResult,LTerm.contract,LTerm.prepend,LTerm.subst,LTerm.single,
    LTerm.OuterBarsSafe,Label.OuterBarsSafe,Label.concat,Label.over,Label.under,Label.atom]

private abbrev duplicateBare : Term := .app (.lam (.app (.var 0) (.var 0))) (.app identity identity)
private abbrev duplicateOriginal := initLabels duplicateBare
private abbrev oldBody : LTerm := .app (.atom 2) (.var (.atom 3) 0) (.var (.atom 4) 0)
private abbrev oldArgument : LTerm := .app (.atom 5)
  (.lam (.atom 6) (.var (.atom 7) 0)) (.lam (.atom 8) (.var (.atom 9) 0))
private abbrev duplicateMiddle := LTerm.contract (.atom 0) (.atom 1) oldBody oldArgument
private abbrev outerLabel := ((Label.atom 0).concat (Label.atom 1).over).concat (.atom 2)
private abbrev copyLabel := ((Label.atom 3).concat (Label.atom 1).under).concat (.atom 5)
private abbrev rightCopy := oldArgument.prepend (((Label.atom 4).concat (Label.atom 1).under))
private abbrev partialResult : LTerm := .app outerLabel
  (LTerm.contract copyLabel (.atom 6) (.var (.atom 7) 0) (.lam (.atom 8) (.var (.atom 9) 0))) rightCopy
private def outerTurn : StepAt [] duplicateOriginal duplicateMiddle := .root _ _ _ _
private def oneCopyTurn : StepAt [.fn] duplicateMiddle partialResult := .fn (.root _ _ _ _)
private abbrev partialProgram := ParallelHistory.cons (singleContraction outerTurn.betaAt)
  (.single (singleContraction oneCopyTurn.betaAt))
private def remainingCopy : RedexOcc partialResult.erase :=
  ⟨[.arg],.app identity identity,rfl,True.intro⟩

/-- A real INIT-labelled history reduces just one of two copies. The other
copy still has degree 6, while the first contraction has already minted its
marker. Consequently this actual history cannot be a complete derivation.
The freshness theorem must not be applied to arbitrary beta histories. -/
theorem reducing_only_one_copy_is_incomplete : ¬CompleteDerivation partialProgram := by
  have labels : History partialProgram.derivation.paths duplicateOriginal partialResult :=
    .cons outerTurn (.cons oneCopyTurn (.nil _))
  have markerPresent : ¬partialResult.OuterBarsSafe (fun payload=>payload≠Label.atom 6) := by
    simp [copyLabel,LTerm.contract,LTerm.prepend,LTerm.subst,LTerm.single,
      LTerm.OuterBarsSafe,Label.OuterBarsSafe,Label.concat,Label.over,Label.under,Label.atom]
  intro complete
  exact markerPresent (complete_prefix_outer_bars_fresh (init_is_INIT duplicateBare)
    partialProgram complete labels remainingCopy rfl)

#print axioms complete_prefix_outer_bars_fresh
#print axioms actual_complete_prefix_has_fresh_next_marker
#print axioms reducing_only_one_copy_is_incomplete
end Lamping.Checks.LabelFamilyMarkerFreshness
