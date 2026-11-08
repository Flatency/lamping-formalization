import Lamping.Lambda.DirectedReadingCreation
namespace Lamping.Lambda.Labelled

/-- Reversing the actual reading direction does not change which outer
degree markers occur. This statement concerns words, not occurrence identity. -/
theorem Label.readLetters_safe {before degree : Label}
    (safe : before.OuterBarsSafe (fun x=>x≠degree))
    (forward : Bool) : ∀ letter∈before.readLetters forward,¬letter.MarksDegree degree := by
  intro letter member
  apply (Label.outerBarsSafe_iff_no_marker degree before).mp safe letter
  cases forward with
  | false => exact List.mem_reverse.mp member
  | true => exact member

theorem Label.readLetters_injective {forward : Bool} {left right : Label}
    (same : left.readLetters forward=right.readLetters forward) : left=right := by
  apply Label.letters_injective
  cases forward with
  | false => exact List.reverse_inj.mp same
  | true => exact same

/-- The first marker determines both source labels and the entire remaining
word. Suffixes are arbitrary lists, including empty or further marked words.
The prefixes are compared in the SAME actual reading direction. -/
theorem Label.readLetters_first_marker_unique
    {forward : Bool} {degree before otherBefore : Label}
    {left right : Letter} {after otherAfter : List Letter}
    (safe : before.OuterBarsSafe (fun x=>x≠degree))
    (otherSafe : otherBefore.OuterBarsSafe (fun x=>x≠degree))
    (leftMarker : left.MarksDegree degree) (rightMarker : right.MarksDegree degree)
    (same : before.readLetters forward++left::after=
      otherBefore.readLetters forward++right::otherAfter) :
    before=otherBefore ∧left=right ∧after=otherAfter := by
  obtain ⟨initialWord,marker,suffix⟩ := first_marker_unique
    (Label.readLetters_safe safe forward) (Label.readLetters_safe otherSafe forward)
    leftMarker rightMarker same
  exact ⟨Label.readLetters_injective initialWord,marker,suffix⟩

/-- Compare two actual first-marker equations without wrapping a possibly
empty suffix as a nonempty Label. Equal labels do not imply equal positions. -/
theorem Label.readLetters_first_marker_of_splits
    {forward : Bool} {degree before otherBefore current otherCurrent : Label}
    {left right : Letter} {after otherAfter : List Letter}
    (safe : before.OuterBarsSafe (fun x=>x≠degree))
    (otherSafe : otherBefore.OuterBarsSafe (fun x=>x≠degree))
    (leftMarker : left.MarksDegree degree) (rightMarker : right.MarksDegree degree)
    (first : current.readLetters forward=before.readLetters forward++left::after)
    (second : otherCurrent.readLetters forward=otherBefore.readLetters forward++right::otherAfter)
    (same : current=otherCurrent) : before=otherBefore ∧left=right ∧after=otherAfter := by
  apply Label.readLetters_first_marker_unique safe otherSafe leftMarker rightMarker
  exact first.symm.trans ((congrArg (Label.readLetters forward) same).trans second)

end Lamping.Lambda.Labelled
