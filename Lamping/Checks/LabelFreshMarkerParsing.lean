import Lamping.Lambda.LabelFreshMarkerParsing

namespace Lamping.Checks.LabelFreshMarkerParsing
open Lambda Lambda.Labelled

private abbrev degree := (Label.atom 3).concat (Label.atom 4).over
private abbrev before := (Label.atom 1).concat (Label.atom 2).under
private abbrev after := (Label.atom 5).concat (degree.under.concat (.atom 6))
private abbrev laterPrefix := before.concat (degree.over.concat (.atom 5))
private theorem beforeSafe : before.OuterBarsSafe (fun payload=>payload≠degree) := by
  simp [before,degree,Label.OuterBarsSafe,Label.concat,Label.atom,Label.over,Label.under]

/-- A genuine outer word has pre-existing unrelated bars and a later
under-marker of this same composite degree. Parsing the first over-marker
still uniquely recovers its entire original prefix and suffix. -/
theorem first_marker_keeps_later_markers {otherBefore otherAfter : Label}
    (safe : otherBefore.OuterBarsSafe (fun payload=>payload≠degree))
    (same : before.concat (degree.over.concat after)=otherBefore.concat (degree.over.concat otherAfter)) :
    before=otherBefore ∧after=otherAfter := by
  have parsed := Label.fresh_marker_split_unique beforeSafe safe
    (Or.inl rfl : Letter.MarksDegree degree (.over degree))
    (Or.inl rfl : Letter.MarksDegree degree (.over degree)) same
  exact ⟨parsed.1,parsed.2.2⟩

/-- The same word also has a later under split; that later prefix is not
marker-free. Thus no unqualified result/substitution disjointness is claimed. -/
theorem later_marker_is_not_the_first :
    before.concat (degree.over.concat after)=laterPrefix.concat (degree.under.concat (.atom 6)) ∧
      ¬laterPrefix.OuterBarsSafe (fun payload=>payload≠degree) := by
  constructor
  · simp only [laterPrefix,after,Label.concat_assoc]
  · simp [laterPrefix,Label.outerBarsSafe_concat,Label.OuterBarsSafe,Label.over]

private abbrev identity : Term := .lam (.var 0)
private abbrev source := initLabels (.app identity identity)
private abbrev body : LTerm := .var (.atom 2) 0
private abbrev argument : LTerm := .lam (.atom 3) (.var (.atom 4) 0)
private def rootRedex : RedexOcc source.erase :=
  ⟨[],.app identity identity,rfl,True.intro⟩

/-- A real I I beta contracts a variable body, so its new result label also
contains a substitution marker. Nevertheless it differs from EVERY old
edge label, using the same INIT and the complete empty prefix. -/
theorem actual_result_copy_overlap_is_fresh (old : Label) (member : old∈source.labels) :
    (LTerm.contract (.atom 0) (.atom 1) body argument).label≠old := by
  rw [LTerm.contract,label_prepend,Label.concat_assoc]
  exact complete_prefix_marked_label_fresh (init_is_INIT (.app identity identity))
    (.nil _) (.nil _) (.nil _) rootRedex rfl member (.atom 0) _ (Or.inl rfl)

#print axioms Label.outerBarsSafe_iff_no_marker
#print axioms Label.fresh_marker_split_unique
#print axioms complete_prefix_marked_label_fresh
#print axioms first_marker_keeps_later_markers
#print axioms later_marker_is_not_the_first
#print axioms actual_result_copy_overlap_is_fresh
end Lamping.Checks.LabelFreshMarkerParsing
