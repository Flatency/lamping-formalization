import Lamping.Lamping.ExposureControlWords

namespace Lamping.AG.ExposureScheduling

/-- A lexical focus in an actual Bool control word: true is writer,
false is reader. No physical site or rewrite certificate is stored here. -/
inductive ControlWordFocus where
  | initialReader
  | terminalWriter
  | internalPeak (index : Nat)
  deriving DecidableEq, Repr

/-- The returned index is the exact prefix length before a WR peak. -/
def ControlWordFocus.Spec (word : List Bool) : ControlWordFocus → Prop
  | .initialReader => ∃ tail,word=false::tail
  | .terminalWriter => ∃ before,word=before++[true]
  | .internalPeak index => ∃ before after,
      word=before++true::false::after ∧before.length=index

/-- Structural data selection. A reader at the head has priority; otherwise
walk through the initial writer prefix until a reader or the terminal writer. -/
def selectControlWordFocus : List Bool → Option ControlWordFocus
  | [] => none
  | false::_ => some .initialReader
  | true::tail =>
    match selectControlWordFocus tail with
    | none => some .terminalWriter
    | some .initialReader => some (.internalPeak 0)
    | some .terminalWriter => some .terminalWriter
    | some (.internalPeak index) => some (.internalPeak (index+1))

theorem selectControlWordFocus_none_iff (word : List Bool) :
    selectControlWordFocus word=none ↔word=[] := by
  cases word with
  | nil => simp [selectControlWordFocus]
  | cons bit tail =>
    cases bit with
    | false => simp [selectControlWordFocus]
    | true =>
      cases selected : selectControlWordFocus tail with
      | none => simp [selectControlWordFocus,selected]
      | some focus => cases focus <;> simp [selectControlWordFocus,selected]

theorem selectControlWordFocus_sound {word : List Bool} {focus : ControlWordFocus}
    (chosen : selectControlWordFocus word=some focus) :
    ControlWordFocus.Spec word focus := by
  induction word generalizing focus with
  | nil => simp [selectControlWordFocus] at chosen
  | cons bit tail ih =>
    cases bit with
    | false =>
      have same : ControlWordFocus.initialReader=focus := by
        simpa only [selectControlWordFocus,Option.some.injEq] using chosen
      cases same
      exact ⟨tail,rfl⟩
    | true =>
      cases selected : selectControlWordFocus tail with
      | none =>
        have tailEmpty := (selectControlWordFocus_none_iff tail).mp selected
        have same : ControlWordFocus.terminalWriter=focus := by
          simpa only [selectControlWordFocus,selected,Option.some.injEq] using chosen
        cases same
        exact ⟨[],congrArg (List.cons true) tailEmpty⟩
      | some next =>
        have rest := ih selected
        cases next with
        | initialReader =>
          have same : ControlWordFocus.internalPeak 0=focus := by
            simpa only [selectControlWordFocus,selected,Option.some.injEq] using chosen
          cases same
          obtain ⟨after,shape⟩ := rest
          exact ⟨[],after,congrArg (List.cons true) shape,rfl⟩
        | terminalWriter =>
          have same : ControlWordFocus.terminalWriter=focus := by
            simpa only [selectControlWordFocus,selected,Option.some.injEq] using chosen
          cases same
          obtain ⟨before,shape⟩ := rest
          exact ⟨true::before,congrArg (List.cons true) shape⟩
        | internalPeak index =>
          have same : ControlWordFocus.internalPeak (index+1)=focus := by
            simpa only [selectControlWordFocus,selected,Option.some.injEq] using chosen
          cases same
          obtain ⟨before,after,shape,atIndex⟩ := rest
          refine ⟨true::before,after,congrArg (List.cons true) shape,?_⟩
          simpa only [List.length_cons] using congrArg (fun n : Nat => n+1) atIndex

theorem selectControlWordFocus_initial_position {word : List Bool}
    (chosen : selectControlWordFocus word=some .initialReader) :
    word.head?=some false := by
  obtain ⟨tail,rfl⟩ := selectControlWordFocus_sound chosen
  rfl

theorem selectControlWordFocus_terminal_position {word : List Bool}
    (chosen : selectControlWordFocus word=some .terminalWriter) :
    word.getLast?=some true := by
  obtain ⟨before,rfl⟩ := selectControlWordFocus_sound chosen
  simp only [List.getLast?_append,List.getLast?_singleton,Option.some_or]

theorem selectControlWordFocus_peak_positions {word : List Bool} {index : Nat}
    (chosen : selectControlWordFocus word=some (.internalPeak index)) :
    word[index]?=some true ∧word[index+1]?=some false := by
  obtain ⟨before,after,rfl,rfl⟩ := selectControlWordFocus_sound chosen
  clear chosen
  induction before with
  | nil => exact ⟨rfl,rfl⟩
  | cons bit before ih =>
    simpa only [List.cons_append,List.length_cons,List.getElem?_cons_succ] using ih

theorem selectControlWordFocus_total (word : List Bool) (nonempty : word≠[]) :
    ∃ focus,selectControlWordFocus word=some focus ∧ControlWordFocus.Spec word focus := by
  cases selected : selectControlWordFocus word with
  | none => exact False.elim (nonempty ((selectControlWordFocus_none_iff word).mp selected))
  | some focus => exact ⟨focus,rfl,selectControlWordFocus_sound selected⟩

end Lamping.AG.ExposureScheduling
