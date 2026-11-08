import Lamping.Lamping.ControlWordOccurrenceCuts

namespace Lamping.AG.ExposureScheduling
open Graph

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]

/-- Word order strictly orders literal physical occurrences. Equal endpoints
at distinct visits are not identified or deduplicated. -/
theorem scanFrom_lookup_strict (g : Net signature N B W) (before es : List (Endpoint g))
    (first second : ControlOccurrence g) (i j : Nat) (ordered : i<j)
    (atFirst : (scanFrom g before es)[i]?=some first)
    (atSecond : (scanFrom g before es)[j]?=some second) :
    first.physicalOrdinal<second.physicalOrdinal := by
  induction es generalizing before i j with
  | nil => cases i <;> cases atFirst
  | cons entry tail ih =>
    cases tail with
    | nil => cases i <;> cases atFirst
    | cons exit after =>
      cases picked : occurrenceAt g before entry exit after with
      | none =>
        have scan : scanFrom g before (entry::exit::after)=
            scanFrom g (before++[entry]) (exit::after) := by
          rw [scanFrom,picked]; rfl
        rw [scan] at atFirst atSecond
        exact ih (before++[entry]) i j ordered atFirst atSecond
      | some head =>
        have scan : scanFrom g before (entry::exit::after)=
            head::scanFrom g (before++[entry]) (exit::after) := by
          rw [scanFrom,picked]; rfl
        rw [scan] at atFirst atSecond
        cases i with
        | zero =>
          have same : head=first := Option.some.inj atFirst
          cases j with
          | zero => exact False.elim ((Nat.lt_irrefl 0) ordered)
          | succ j =>
            have tailLookup :
                (scanFrom g (before++[entry]) (exit::after))[j]?=some second := atSecond
            have member := List.mem_of_getElem? tailLookup
            have lower := scanFrom_ordinal_lower g (before++[entry]) (exit::after) second member
            have geometry := occurrenceAt_geometry g before entry exit after head picked
            have firstOrdinal : first.physicalOrdinal=before.length := by
              rw [←same]
              exact congrArg List.length geometry.1
            rw [firstOrdinal]
            apply Nat.lt_of_lt_of_le (Nat.lt_succ_self before.length)
            simpa only [List.length_append,List.length_singleton,ControlOccurrence.physicalOrdinal] using lower
        | succ i =>
          cases j with
          | zero => exact False.elim (Nat.not_lt_zero _ ordered)
          | succ j => exact ih (before++[entry]) i j (Nat.lt_of_succ_lt_succ ordered) atFirst atSecond

theorem controlOccurrences_lookup_strict (g : Net signature N B W) (es : List (Endpoint g))
    (first second : ControlOccurrence g) (i j : Nat) (ordered : i<j)
    (atFirst : (controlOccurrences g es)[i]?=some first)
    (atSecond : (controlOccurrences g es)[j]?=some second) :
    first.physicalOrdinal<second.physicalOrdinal :=
  scanFrom_lookup_strict g [] es first second i j ordered atFirst atSecond

#print axioms Lamping.AG.ExposureScheduling.scanFrom_lookup_strict
#print axioms Lamping.AG.ExposureScheduling.controlOccurrences_lookup_strict

end
end Lamping.AG.ExposureScheduling
