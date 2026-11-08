import Lamping.Lamping.ComputedFocusCorridorData

namespace Lamping.AG.ExposureScheduling
open Graph

private theorem prefix_head {A : Type} (before : List A) (entry exit : A) (after : List A) :
    (before++[entry]).head?=(before++entry::exit::after).head? := by
  cases before <;> rfl

private theorem suffix_last {A : Type} (before : List A) (entry exit : A) (after : List A) :
    (exit::after).getLast?=(before++entry::exit::after).getLast? := by
  induction before with
  | nil => simp only [List.nil_append,List.getLast?_cons_cons]
  | cons first before ih =>
    cases before with
    | nil => simp only [List.cons_append,List.nil_append,List.getLast?_cons_cons]
    | cons second before => simpa only [List.cons_append,List.getLast?_cons_cons] using ih

private theorem drop_lookup {A : Type} (xs : List A) (m n : Nat) :
    (xs.drop m)[n]?=xs[m+n]? := by
  induction m generalizing xs with
  | zero => simp only [List.drop_zero,Nat.zero_add]
  | succ m ih =>
    cases xs with
    | nil => simp
    | cons x xs =>
      simpa only [List.drop_succ_cons,Nat.succ_add,List.getElem?_cons_succ] using ih xs

private theorem take_positive_head {A : Type} (xs : List A) (n : Nat) (positive : 0<n) :
    (xs.take n).head?=xs.head? := by
  cases n with
  | zero => cases (Nat.not_lt_zero 0 positive)
  | succ n => cases xs <;> rfl

private theorem drop_head {A : Type} (xs : List A) (m : Nat) :
    (xs.drop m).head?=xs[m]? := by
  simpa only [List.head?_eq_getElem?,Nat.add_zero] using drop_lookup xs m 0

private theorem take_succ_last {A : Type} (xs : List A) (n : Nat) (last : A)
    (atLast : xs[n]?=some last) : (xs.take (n+1)).getLast?=some last := by
  induction n generalizing xs with
  | zero =>
    cases xs with
    | nil => cases atLast
    | cons first xs =>
      have same : first=last := Option.some.inj atLast
      subst first
      rfl
  | succ n ih =>
    cases xs with
    | nil => cases atLast
    | cons first xs =>
      have next : xs[n]?=some last := atLast
      simp only [Nat.succ_add,List.take_succ_cons,List.getLast?_cons,
        ih xs next,Option.getD_some]

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

/-- The actual computed interval begins and ends at its computed ports.
Repeated visits are distinguished by their physical ordinals throughout. -/
theorem computeFocusCorridorData_endpoints (connection : RedexConnection g)
    (focus : PhysicalControlFocus g)
    (chosen : selectPhysicalControlFocus g connection.edges=some focus)
    (data : FocusCorridorData g) (computed : computeFocusCorridorData connection focus=some data) :
    data.edges.head?=some (Sum.inl data.first) ∧
      data.edges.getLast?=some (g.wire (Sum.inl data.last)) := by
  have spec := selectPhysicalControlFocus_sound g connection.edges focus chosen
  cases focus with
  | initialReader occurrence =>
    have member := List.mem_of_getElem? spec.1
    have split := controlOccurrences_split g connection.edges occurrence member
    cases actual : nodePortOfEndpoint g (g.wire occurrence.entry) with
    | none => simp [computeFocusCorridorData,actual] at computed
    | some last =>
      have arrives := (nodePortOfEndpoint_eq_some_iff g _ last).mp actual
      simp only [computeFocusCorridorData,actual,Option.map_some,Option.some.injEq] at computed
      cases computed
      constructor
      · change (occurrence.before++[occurrence.entry]).head?=_
        rw [prefix_head occurrence.before occurrence.entry occurrence.exit occurrence.after,←split]
        exact connection.start
      · change (occurrence.before++[occurrence.entry]).getLast?=some (g.wire (Sum.inl last))
        rw [←arrives,Pairing.involutive]
        simp only [List.getLast?_append,List.getLast?_singleton,Option.some_or]
  | terminalWriter occurrence =>
    have member : occurrence∈controlOccurrences g connection.edges := by
      obtain ⟨earlier,split⟩ := List.getLast?_eq_some_iff.mp spec.1
      rw [split]
      exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
    have split := controlOccurrences_split g connection.edges occurrence member
    simp only [computeFocusCorridorData,Option.some.injEq] at computed
    cases computed
    constructor
    · rfl
    · change (occurrence.exit::occurrence.after).getLast?=_
      rw [suffix_last occurrence.before occurrence.entry occurrence.exit occurrence.after,←split]
      exact connection.finish
  | internalPeak index writer reader =>
    have writerMember := List.mem_of_getElem? spec.1
    have readerMember := List.mem_of_getElem? spec.2.1
    have ordered := controlOccurrences_lookup_strict g connection.edges writer reader index (index+1)
      (Nat.lt_succ_self index) spec.1 spec.2.1
    have atWriter := (controlOccurrences_entry_exit g connection.edges writer writerMember).2
    have atReader := (controlOccurrences_entry_exit g connection.edges reader readerMember).1
    have positive : 0<reader.physicalOrdinal-writer.physicalOrdinal := by omega
    have countEq : reader.physicalOrdinal-writer.physicalOrdinal=
        (reader.physicalOrdinal-(writer.physicalOrdinal+1))+1 := by omega
    have offsetEq : writer.physicalOrdinal+1+
        (reader.physicalOrdinal-(writer.physicalOrdinal+1))=reader.physicalOrdinal := by omega
    have atLast : (connection.edges.drop (writer.physicalOrdinal+1))[reader.physicalOrdinal-(writer.physicalOrdinal+1)]?=some reader.entry := by
      rw [drop_lookup,offsetEq]
      exact atReader
    cases actual : nodePortOfEndpoint g (g.wire reader.entry) with
    | none => simp [computeFocusCorridorData,actual] at computed
    | some last =>
      have arrives := (nodePortOfEndpoint_eq_some_iff g _ last).mp actual
      simp only [computeFocusCorridorData,actual,Option.map_some,Option.some.injEq] at computed
      cases computed
      constructor
      · change ((connection.edges.drop (writer.physicalOrdinal+1)).take
          (reader.physicalOrdinal-writer.physicalOrdinal)).head?=some writer.exit
        rw [take_positive_head _ _ positive,drop_head]
        exact atWriter
      · change ((connection.edges.drop (writer.physicalOrdinal+1)).take
          (reader.physicalOrdinal-writer.physicalOrdinal)).getLast?=some (g.wire (Sum.inl last))
        rw [←arrives,Pairing.involutive,countEq]
        exact take_succ_last _ _ reader.entry atLast
end
end Lamping.AG.ExposureScheduling
