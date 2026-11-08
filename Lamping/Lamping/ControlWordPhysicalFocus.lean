import Lamping.Lamping.ControlWordOccurrenceOrder
import Lamping.Lamping.ControlWordFocusData

namespace Lamping.AG.ExposureScheduling
open Graph

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]

inductive PhysicalControlFocus (g : Net signature N B W) where
  | initialReader (occurrence : ControlOccurrence g)
  | terminalWriter (occurrence : ControlOccurrence g)
  | internalPeak (index : Nat) (writer reader : ControlOccurrence g)

/-- This is a theorem target, not a certificate stored in the returned data. -/
def PhysicalControlFocus.Spec (g : Net signature N B W) (es : List (Endpoint g)) :
    PhysicalControlFocus g → Prop
  | .initialReader occurrence =>
      (controlOccurrences g es)[0]?=some occurrence ∧ occurrence.bit=false
  | .terminalWriter occurrence =>
      (controlOccurrences g es).getLast?=some occurrence ∧ occurrence.bit=true
  | .internalPeak index writer reader =>
      (controlOccurrences g es)[index]?=some writer ∧
      (controlOccurrences g es)[index+1]?=some reader ∧
      writer.bit=true ∧ reader.bit=false ∧ writer.physicalOrdinal<reader.physicalOrdinal

/-- Lexical indices select records in the actual scan. No semantic witness,
physical cut, rank or desired role is a runtime input. -/
def selectPhysicalControlFocus (g : Net signature N B W) (es : List (Endpoint g)) :
    Option (PhysicalControlFocus g) :=
  let occurrences := controlOccurrences g es
  match selectControlWordFocus (controlWord g es) with
  | none => none
  | some .initialReader => (occurrences[0]?).map PhysicalControlFocus.initialReader
  | some .terminalWriter => occurrences.getLast?.map PhysicalControlFocus.terminalWriter
  | some (.internalPeak index) =>
      match occurrences[index]?,occurrences[index+1]? with
      | some writer,some reader => some (.internalPeak index writer reader)
      | _,_ => none

private theorem map_get {A C : Type} (f : A → C) (items : List A) (index : Nat) :
    (items.map f)[index]?=(items[index]?).map f := by
  induction items generalizing index with
  | nil => cases index <;> rfl
  | cons first items ih => cases index with
    | zero => rfl
    | succ index => exact ih index

private theorem element_of_map {A C : Type} (f : A → C) (items : List A)
    (index : Nat) (value : C) (picked : (items.map f)[index]?=some value) :
    ∃ entry,items[index]?=some entry ∧ f entry=value := by
  have result : (items[index]?).map f=some value := (map_get f items index).symm.trans picked
  cases actual : items[index]? with
  | none => simp only [actual,Option.map_none] at result; cases result
  | some entry =>
    exact ⟨entry,rfl,Option.some.inj (by simpa only [actual,Option.map_some] using result)⟩

private theorem map_last {A C : Type} (f : A → C) (items : List A) :
    (items.map f).getLast?=items.getLast?.map f := by
  induction items with
  | nil => rfl
  | cons first items ih => cases items with
    | nil => rfl
    | cons second rest => exact ih

private theorem get_zero_head {A : Type} (items : List A) :
    items[0]?=items.head? := by
  cases items <;> rfl

theorem selectPhysicalControlFocus_sound (g : Net signature N B W) (es : List (Endpoint g))
    (focus : PhysicalControlFocus g) (chosen : selectPhysicalControlFocus g es=some focus) :
    PhysicalControlFocus.Spec g es focus := by
  cases lexical : selectControlWordFocus (controlWord g es) with
  | none => simp only [selectPhysicalControlFocus,lexical] at chosen; cases chosen
  | some selected =>
    cases selected with
    | initialReader =>
      cases atFirst : (controlOccurrences g es)[0]? with
      | none => simp only [selectPhysicalControlFocus,lexical,atFirst,Option.map_none] at chosen; cases chosen
      | some occurrence =>
        have same : PhysicalControlFocus.initialReader occurrence=focus := Option.some.inj (by
          simpa only [selectPhysicalControlFocus,lexical,atFirst,Option.map_some] using chosen)
        cases same
        refine ⟨atFirst,?_⟩
        have expected := selectControlWordFocus_initial_position lexical
        rw [←get_zero_head (controlWord g es)] at expected
        have actual := (controlOccurrences_lookup g es 0 occurrence atFirst).2.2.2.2
        exact Option.some.inj (actual.symm.trans expected)
    | terminalWriter =>
      cases atLast : (controlOccurrences g es).getLast? with
      | none => simp only [selectPhysicalControlFocus,lexical,atLast,Option.map_none] at chosen; cases chosen
      | some occurrence =>
        have same : PhysicalControlFocus.terminalWriter occurrence=focus := Option.some.inj (by
          simpa only [selectPhysicalControlFocus,lexical,atLast,Option.map_some] using chosen)
        cases same
        refine ⟨atLast,?_⟩
        have expected := selectControlWordFocus_terminal_position lexical
        have actual : (controlWord g es).getLast?=some occurrence.bit := by
          rw [←controlOccurrences_bits,map_last,atLast]; rfl
        exact Option.some.inj (actual.symm.trans expected)
    | internalPeak index =>
      cases atWriter : (controlOccurrences g es)[index]? with
      | none => simp only [selectPhysicalControlFocus,lexical,atWriter] at chosen; cases chosen
      | some writer =>
        cases atReader : (controlOccurrences g es)[index+1]? with
        | none => simp only [selectPhysicalControlFocus,lexical,atWriter,atReader] at chosen; cases chosen
        | some reader =>
          have same : PhysicalControlFocus.internalPeak index writer reader=focus := Option.some.inj (by
            simpa only [selectPhysicalControlFocus,lexical,atWriter,atReader] using chosen)
          cases same
          have expected := selectControlWordFocus_peak_positions lexical
          have writerBit := (controlOccurrences_lookup g es index writer atWriter).2.2.2.2
          have readerBit := (controlOccurrences_lookup g es (index+1) reader atReader).2.2.2.2
          exact ⟨atWriter,atReader,Option.some.inj (writerBit.symm.trans expected.1),
            Option.some.inj (readerBit.symm.trans expected.2),
            controlOccurrences_lookup_strict g es writer reader index (index+1)
              (Nat.lt_succ_self index) atWriter atReader⟩

/-- Nonempty words never fail the physical table lookup. Existential
witnesses are eliminated only in this proposition, never into selector data. -/
theorem selectPhysicalControlFocus_total (g : Net signature N B W) (es : List (Endpoint g))
    (nonempty : controlWord g es≠[]) : ∃ focus,selectPhysicalControlFocus g es=some focus := by
  obtain ⟨selected,lexical,_spec⟩ := selectControlWordFocus_total (controlWord g es) nonempty
  cases selected with
  | initialReader =>
    have expected := selectControlWordFocus_initial_position lexical
    rw [←get_zero_head (controlWord g es)] at expected
    have projected : ((controlOccurrences g es).map ControlOccurrence.bit)[0]?=some false := by
      rw [controlOccurrences_bits]; exact expected
    obtain ⟨occurrence,atFirst,_bit⟩ := element_of_map ControlOccurrence.bit (controlOccurrences g es) 0 false projected
    exact ⟨.initialReader occurrence,by
      simp only [selectPhysicalControlFocus,lexical,atFirst,Option.map_some]⟩
  | terminalWriter =>
    have expected := selectControlWordFocus_terminal_position lexical
    have projected : (controlOccurrences g es).getLast?.map ControlOccurrence.bit=some true := by
      rw [←map_last,controlOccurrences_bits]; exact expected
    cases atLast : (controlOccurrences g es).getLast? with
    | none => simp only [atLast,Option.map_none] at projected; cases projected
    | some occurrence =>
      exact ⟨.terminalWriter occurrence,by
        simp only [selectPhysicalControlFocus,lexical,atLast,Option.map_some]⟩
  | internalPeak index =>
    have expected := selectControlWordFocus_peak_positions lexical
    have writerProjected : ((controlOccurrences g es).map ControlOccurrence.bit)[index]?=some true := by
      rw [controlOccurrences_bits]; exact expected.1
    have readerProjected : ((controlOccurrences g es).map ControlOccurrence.bit)[index+1]?=some false := by
      rw [controlOccurrences_bits]; exact expected.2
    obtain ⟨writer,atWriter,_writerBit⟩ :=
      element_of_map ControlOccurrence.bit (controlOccurrences g es) index true writerProjected
    obtain ⟨reader,atReader,_readerBit⟩ :=
      element_of_map ControlOccurrence.bit (controlOccurrences g es) (index+1) false readerProjected
    exact ⟨.internalPeak index writer reader,by
      simp only [selectPhysicalControlFocus,lexical,atWriter,atReader]⟩

#print axioms Lamping.AG.ExposureScheduling.PhysicalControlFocus
#print axioms Lamping.AG.ExposureScheduling.PhysicalControlFocus.Spec
#print axioms Lamping.AG.ExposureScheduling.selectPhysicalControlFocus
#print axioms Lamping.AG.ExposureScheduling.selectPhysicalControlFocus_sound
#print axioms Lamping.AG.ExposureScheduling.selectPhysicalControlFocus_total

end
end Lamping.AG.ExposureScheduling
