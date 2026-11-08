import Lamping.Lamping.PhysicalReadingRoles
import Lamping.Lamping.TerminalPredecessorDirection

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

/-- Opposite actual reads under equal physical parent images occur only
in the whole singleton case. No parent incidence iso is assumed. -/
theorem actual_physical_parent_opposite_cut_singleton
    {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} {root : B}
    {source current : LTerm} {F ps : List Path} {degree : Label}
    {leftStart rightStart : Path} {es fs : List Path}
    (matching : Matches g root current.erase)
    (sourceClosed : Closed source.erase)
    (labels : History ps source current)
    (selection : OccurrenceFragmentSelection current g root)
    (leftParent : PrerequisiteChain current leftStart es)
    (rightParent : PrerequisiteChain current rightStart fs)
    (physical : SameChainRepresentation selection leftParent rightParent)
    (left : ActualUnsafeMarkerCut F ps source current degree leftStart es)
    (right : ActualUnsafeMarkerCut F ps source current degree rightStart fs)
    (sameBefore : left.before.length=right.before.length)
    (opposite : left.forward≠right.forward) :
    es.length=1 ∧fs.length=1 ∧
      left.before=[] ∧right.before=[] ∧left.after=[] ∧right.after=[] := by
  obtain ⟨_length,_empty,casesAfter⟩ := actual_cut_after_representation_cases
    selection leftParent rightParent physical left right sameBefore
  have terminal : left.after=[] ∧right.after=[] := by
    rcases casesAfter with terminal | more
    · exact terminal
    · have signs := actual_parent_cut_physical_reading_roles matching sourceClosed labels
        selection leftParent rightParent physical left right sameBefore more.1
      exact False.elim (opposite signs.2.1)
  have zero : left.before.length=0 := by
    by_cases zero : left.before.length=0
    · exact zero
    · have positive : 0<left.before.length := by omega
      exact False.elim (opposite (actual_terminal_predecessor_direction_eq matching selection
        leftParent rightParent physical left right sameBefore positive terminal.1 terminal.2))
  have lb : left.before=[] := List.length_eq_zero_iff.mp zero
  have rb : right.before=[] := List.length_eq_zero_iff.mp (sameBefore ▸ zero)
  have ls := left.split
  have rs := right.split
  rw [lb,terminal.1,List.nil_append] at ls
  rw [rb,terminal.2,List.nil_append] at rs
  exact ⟨by rw [ls];rfl,by rw [rs];rfl,lb,rb,terminal⟩

#print axioms actual_physical_parent_opposite_cut_singleton
end Lamping.AG
