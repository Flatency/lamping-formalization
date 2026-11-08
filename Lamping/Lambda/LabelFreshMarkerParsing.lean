import Lamping.Lambda.LabelFamilyMarkerFreshness
import Lamping.Lambda.LabelHeadMarkerParsing

namespace Lamping.Lambda.Labelled

def Letter.MarksDegree (degree : Label) (letter : Letter) : Prop :=
  letter=.over degree ∨letter=.under degree

theorem Label.outerBarsSafe_iff_no_marker (degree : Label) : ∀ label : Label,
    label.OuterBarsSafe (fun payload=>payload≠degree) ↔
      ∀ letter∈label.letters,¬letter.MarksDegree degree
  | .single letter => by cases letter <;> simp [Label.OuterBarsSafe,Label.letters,Letter.MarksDegree]
  | .cons letter rest => by
    cases letter <;> simp [Label.OuterBarsSafe,Label.letters,Letter.MarksDegree,
      outerBarsSafe_iff_no_marker degree rest,or_imp,forall_and,and_assoc,and_left_comm]

theorem first_marker_unique {xs ys leftTail rightTail : List Letter}
    {degree : Label} {left right : Letter}
    (leftSafe : ∀ letter∈xs,¬letter.MarksDegree degree)
    (rightSafe : ∀ letter∈ys,¬letter.MarksDegree degree)
    (leftMarker : left.MarksDegree degree) (rightMarker : right.MarksDegree degree)
    (same : xs++left::leftTail=ys++right::rightTail) :
    xs=ys ∧left=right ∧leftTail=rightTail := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact ⟨rfl,(List.cons.inj same).1,(List.cons.inj same).2⟩
    | cons head tail =>
      have equal : left=head := (List.cons.inj same).1
      subst head
      exact False.elim (rightSafe left List.mem_cons_self leftMarker)
  | cons head tail ih =>
    cases ys with
    | nil =>
      have equal : head=right := (List.cons.inj same).1
      subst head
      exact False.elim (leftSafe right List.mem_cons_self rightMarker)
    | cons other rest =>
      have equal : head=other := (List.cons.inj same).1
      subst other
      have tails := ih
        (fun letter member=>leftSafe letter (List.mem_cons_of_mem _ member))
        (fun letter member=>rightSafe letter (List.mem_cons_of_mem _ member))
        (List.cons.inj same).2
      exact ⟨congrArg (head::·) tails.1,tails.2⟩

/-- Parse the first marker of this degree. Only the prefixes must be free
of that marker; the suffixes may contain further result/substitution marks,
including the real result/copy overlap. -/
theorem Label.fresh_marker_split_unique {degree : Label} {before otherBefore after otherAfter : Label}
    {left right : Letter}
    (beforeSafe : before.OuterBarsSafe (fun payload=>payload≠degree))
    (otherSafe : otherBefore.OuterBarsSafe (fun payload=>payload≠degree))
    (leftMarker : left.MarksDegree degree) (rightMarker : right.MarksDegree degree)
    (same : before.concat ((Label.single left).concat after)=
      otherBefore.concat ((Label.single right).concat otherAfter)) :
    before=otherBefore ∧left=right ∧after=otherAfter := by
  have words : before.letters++left::after.letters=otherBefore.letters++right::otherAfter.letters := by
    simpa only [Label.letters_concat,Label.letters,List.cons_append,List.nil_append] using
      congrArg Label.letters same
  obtain ⟨first,marker,last⟩ := first_marker_unique
    ((Label.outerBarsSafe_iff_no_marker degree before).mp beforeSafe)
    ((Label.outerBarsSafe_iff_no_marker degree otherBefore).mp otherSafe)
    leftMarker rightMarker words
  exact ⟨Label.letters_injective first,marker,Label.letters_injective last⟩

/-- A marked label cannot equal an older edge label before that current
degree's whole-family step. Prefix/suffix contents are otherwise unrestricted. -/
theorem complete_prefix_marked_label_fresh {original current : LTerm}
    (initial : INIT original) (program : ParallelHistory original.erase current.erase)
    (complete : CompleteDerivation program) (labels : History program.derivation.paths original current)
    (redex : RedexOcc current.erase) (atDegree : current.degreeAt redex.val=some degree)
    {old : Label} (member : old∈current.labels) (before after : Label)
    {marker : Letter} (marked : marker.MarksDegree degree) :
    before.concat ((Label.single marker).concat after)≠old := by
  have safe := (LTerm.outerBarsSafe_iff _ _).mp
    (complete_prefix_outer_bars_fresh initial program complete labels redex atDegree) old member
  intro same
  rw [←same] at safe
  have hasMarker : marker∈(before.concat ((Label.single marker).concat after)).letters := by
    simp only [Label.letters_concat,Label.letters]
    exact List.mem_append_right _ (List.mem_append_left _ List.mem_cons_self)
  exact ((Label.outerBarsSafe_iff_no_marker degree _).mp safe marker hasMarker) marked

end Lamping.Lambda.Labelled
