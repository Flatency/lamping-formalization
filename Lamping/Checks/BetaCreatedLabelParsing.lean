import Lamping.Lambda.BetaCreatedLabelParsing
namespace Lamping.Checks.BetaCreatedLabelParsing
open Lambda Lambda.Labelled
private abbrev degree := (Label.atom 2).concat (.atom 12)
private abbrev body : LTerm := .app (.atom 3) (.var (.atom 4) 0) (.var (.atom 4) 0)
private abbrev argument : LTerm := .lam (.atom 7) (.var (.atom 8) 0)
private abbrev source : LTerm := .app (.atom 1) (.lam degree body) argument
private abbrev target := LTerm.contract (.atom 1) degree body argument
private abbrev copied := argument.prepend ((Label.atom 4).concat degree.under)
private def turn : StepAt [] source target := .root _ _ _ _
private theorem safe : source.OuterBarsSafe (fun payload=>payload≠degree) := by
  simp [degree,LTerm.OuterBarsSafe,Label.OuterBarsSafe,Label.concat,Label.atom]

/-- The actual result is separated from a strict copied lambda, even
though there are two distinct strict copies with equal labels. -/
theorem real_result_and_strict_copies :
    target.label≠copied.label ∧
    ∃ stamp,body.subterm [.fn]=some (.var stamp 0) ∧body.subterm [.arg]=some (.var stamp 0) := by
  constructor
  · exact turn.result_ne_strict_copy_label rfl safe rfl
      (copySite := [.fn]) (by rfl) (by decide) rfl
  · exact turn.strict_copy_equal_labels rfl safe
      (leftSite := [.fn]) (rightSite := [.arg]) (by rfl) (by decide) (by rfl) (by decide)
      (left := copied) (right := copied) rfl rfl rfl

private abbrev unsafeBeta := (Label.atom 4).concat ((Label.atom 2).under.concat (.atom 5))
private abbrev unsafeArgLabel := (Label.atom 5).concat ((Label.atom 2).over.concat (.atom 3))
private abbrev unsafeArgument : LTerm := .lam unsafeArgLabel (.var (.atom 8) 0)
private abbrev unsafeSource : LTerm := .app unsafeBeta (.lam (.atom 2) body) unsafeArgument
private abbrev unsafeTarget := LTerm.contract unsafeBeta (.atom 2) body unsafeArgument
private abbrev unsafeCopy := unsafeArgument.prepend ((Label.atom 4).concat (Label.atom 2).under)

/-- A real beta with old markers can have equal result and strict-copy
labels, so first-marker disjointness requires source safety. -/
theorem unsafe_result_copy_collision :
    StepAt [] unsafeSource unsafeTarget ∧
    unsafeTarget.subterm [.fn]=some unsafeCopy ∧unsafeTarget.label=unsafeCopy.label ∧
    ¬unsafeSource.OuterBarsSafe (fun payload=>payload≠Label.atom 2) := by
  refine ⟨.root _ _ _ _,rfl,?_,?_⟩
  · decide
  · simp [LTerm.OuterBarsSafe,Label.OuterBarsSafe,unsafeBeta,unsafeArgLabel,
      Label.outerBarsSafe_concat,Label.under,Label.over]

/-- The excluded empty copy site really coincides with the result, even
for a source with fresh degree markers. -/
theorem root_result_copy_overlap :
    ArgumentOccurrence (LTerm.var (.atom 3) 0).erase [] ∧
    BetaCreatedIncoming (.var (.atom 3) 0) [] [] ∧
    (LTerm.contract (.atom 1) degree (.var (.atom 3) 0) argument).label=
      ((Label.atom 1).concat degree.over).concat
        ((Label.atom 3).concat (degree.under.concat argument.label)) := by
  exact ⟨rfl,Or.inl rfl,rfl⟩
end Lamping.Checks.BetaCreatedLabelParsing
#print axioms Lamping.Lambda.Labelled.StepAt.result_ne_strict_copy_label
#print axioms Lamping.Lambda.Labelled.StepAt.strict_copy_equal_labels
#print axioms Lamping.Checks.BetaCreatedLabelParsing.real_result_and_strict_copies
#print axioms Lamping.Checks.BetaCreatedLabelParsing.unsafe_result_copy_collision
