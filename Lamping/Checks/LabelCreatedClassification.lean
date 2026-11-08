import Lamping.Lambda.LabelCreatedClassification
namespace Lamping.Checks.LabelCreatedClassification
open Lambda Lambda.Labelled

private abbrev degree := (Label.atom 2).concat (.atom 12)
private abbrev body : LTerm := .app (.atom 3) (.var (.atom 4) 0) (.var (.atom 4) 0)
private abbrev argument : LTerm := .lam (.atom 7) (.var (.atom 8) 0)
private abbrev source : LTerm := .app (.atom 1) (.lam degree body) argument
private abbrev target := LTerm.contract (.atom 1) degree body argument
private def turn : StepAt [] source target := .root _ _ _ _
private theorem safe : source.OuterBarsSafe (fun payload=>payload≠degree) := by
  simp [degree,LTerm.OuterBarsSafe,Label.OuterBarsSafe,Label.concat,Label.atom]
private abbrev copied := argument.prepend ((Label.atom 4).concat degree.under)

/-- A non-INIT degree and repeated labels still give two distinct actual
created occurrences with the same fresh label. No injection is assumed. -/
theorem same_label_two_created :
    BetaCreatedIncoming body [] [.fn] ∧BetaCreatedIncoming body [] [.arg] ∧
    copied.label∉source.labels ∧([Step.fn] : Path)≠[.arg] := by
  have first : BetaCreatedIncoming body [] [.fn] := by decide
  have second := (turn.same_label_created_iff rfl safe
    (left := copied) (right := copied) (leftEdge := [.fn]) (rightEdge := [.arg]) rfl rfl rfl).mp first
  exact ⟨first,second,(turn.created_iff_fresh_label rfl safe (edge := [.fn]) rfl).mp first,by decide⟩

theorem strict_copy_interior_is_old :
    ¬BetaCreatedIncoming body [] [.fn,.body] ∧
    (Label.atom 8)∈source.labels := by
  have uncreated : ¬BetaCreatedIncoming body [] [.fn,.body] := by decide
  exact ⟨uncreated,turn.uncreated_label_mem (current := .var (.atom 8) 0) rfl rfl uncreated⟩

private abbrev identity : Term := .lam (.var 0)
private abbrev initialSource := initLabels (.app identity identity)
private abbrev initialBody : LTerm := .var (.atom 2) 0
private abbrev initialArgument : LTerm := .lam (.atom 3) (.var (.atom 4) 0)
private abbrev initialTarget := LTerm.contract (.atom 0) (.atom 1) initialBody initialArgument
private def initialTurn : StepAt [] initialSource initialTarget := .root _ _ _ _

/-- Both roles coincide on the real I I result. The global INIT/complete
prefix wrapper supplies freshness without any new source safety premise. -/
theorem complete_prefix_overlap :
    initialTarget.label∉initialSource.labels ∧
    (BetaCreatedIncoming initialBody [] [] ↔initialTarget.label∉initialSource.labels) := by
  have classified := complete_prefix_created_iff_fresh_label (init_is_INIT (.app identity identity))
    (.nil _) (.nil _) (.nil _) initialTurn rfl (edge := []) rfl
  exact ⟨classified.mp (Or.inl rfl),classified⟩

private abbrev oldResult := ((Label.atom 1).concat (Label.atom 2).over).concat (.atom 3)
private abbrev unsafeArgument : LTerm := .lam oldResult (.var (.atom 8) 0)
private abbrev unsafeSource : LTerm := .app (.atom 1) (.lam (.atom 2) body) unsafeArgument
private abbrev unsafeTarget := LTerm.contract (.atom 1) (.atom 2) body unsafeArgument

/-- A genuinely created result can already be an old label if the source
contains that degree's marker. The source safety premise is necessary. -/
theorem old_marker_breaks_unconditional_freshness :
    StepAt [] unsafeSource unsafeTarget ∧BetaCreatedIncoming body [] [] ∧
    unsafeTarget.label∈unsafeSource.labels ∧
    ¬unsafeSource.OuterBarsSafe (fun payload=>payload≠Label.atom 2) := by
  refine ⟨.root _ _ _ _,Or.inl rfl,?_,?_⟩
  · decide
  · simp [oldResult,LTerm.OuterBarsSafe,
      Label.outerBarsSafe_concat,Label.OuterBarsSafe,Label.over]

end Lamping.Checks.LabelCreatedClassification
#print axioms Lamping.Lambda.Labelled.StepAt.created_label_not_safe
#print axioms Lamping.Lambda.Labelled.StepAt.created_iff_fresh_label
#print axioms Lamping.Lambda.Labelled.StepAt.created_iff_marker
#print axioms Lamping.Lambda.Labelled.complete_prefix_created_iff_fresh_label
#print axioms Lamping.Lambda.Labelled.StepAt.same_label_created_iff
#print axioms Lamping.Checks.LabelCreatedClassification.same_label_two_created
#print axioms Lamping.Checks.LabelCreatedClassification.complete_prefix_overlap
