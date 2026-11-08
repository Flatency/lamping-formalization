import Lamping.Lamping.ComputedFocusBoundaryTraversals

namespace Lamping.AG.ExposureScheduling
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

/-- The actual selected ordinal determines exactly which sides have a
boundary traversal. In the internal case neither empty-side alternative
of the whole-assignment boundary theorem is possible. -/
theorem selectPhysicalControlFocus_boundary_sides (connection : RedexConnection g)
    (focus : PhysicalControlFocus g)
    (chosen : selectPhysicalControlFocus g connection.edges=some focus) :
    match focus with
    | .initialReader _ => focus.beforeCorridor connection.edges=[] ∧
        focus.afterCorridor connection.edges≠[]
    | .terminalWriter _ => focus.beforeCorridor connection.edges≠[] ∧
        focus.afterCorridor connection.edges=[]
    | .internalPeak _ _ _ => focus.beforeCorridor connection.edges≠[] ∧
        focus.afterCorridor connection.edges≠[] := by
  have spec := selectPhysicalControlFocus_sound g connection.edges focus chosen
  cases focus with
  | initialReader occurrence =>
    exact ⟨rfl, by simp [PhysicalControlFocus.afterCorridor]⟩
  | terminalWriter occurrence =>
    exact ⟨by simp [PhysicalControlFocus.beforeCorridor], rfl⟩
  | internalPeak index writer reader =>
    have writerMember := List.mem_of_getElem? spec.1
    have readerMember := List.mem_of_getElem? spec.2.1
    have atWriter := (controlOccurrences_entry_exit g connection.edges writer writerMember).1
    have atReader := (controlOccurrences_entry_exit g connection.edges reader readerMember).2
    have writerBound := (List.getElem?_eq_some_iff.mp atWriter).1
    have readerBound := (List.getElem?_eq_some_iff.mp atReader).1
    constructor
    · change connection.edges.take (writer.physicalOrdinal+1) ≠ []
      intro empty
      have count := congrArg List.length empty
      rw [List.length_take] at count
      simp only [List.length_nil] at count
      omega
    · change connection.edges.drop (reader.physicalOrdinal+1) ≠ []
      intro empty
      have count := congrArg List.length empty
      rw [List.length_drop] at count
      simp only [List.length_nil] at count
      omega
end
end Lamping.AG.ExposureScheduling
