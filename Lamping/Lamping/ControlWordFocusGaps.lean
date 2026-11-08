import Lamping.Lamping.ControlWordOccurrenceTurns

namespace Lamping.AG.ExposureScheduling
open Graph

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]

private def gapEndpointProjection (g : Net signature N B W) : Endpoint g → List Bool
  | .inl ⟨node,port⟩ => controlPortWord (g.label node).sort port
  | .inr _ => []

private theorem gap_word_overlap (g : Net signature N B W)
    (before : List (Endpoint g)) (pivot : Endpoint g) (after : List (Endpoint g)) :
    controlWord g (before++pivot::after)=
      controlWord g (before++[pivot])++controlWord g (pivot::after) := by
  cases before with
  | nil => rfl
  | cons first before =>
    change (before++pivot::after).flatMap (gapEndpointProjection g)=
      (before++[pivot]).flatMap (gapEndpointProjection g)++after.flatMap (gapEndpointProjection g)
    rw [List.flatMap_append,List.flatMap_append,List.flatMap_cons,List.flatMap_singleton]
    exact (List.append_assoc _ _ _).symm

private theorem gap_word_snoc (g : Net signature N B W)
    (before : List (Endpoint g)) (entry exit : Endpoint g) :
    controlWord g ((before++[entry])++[exit])=
      controlWord g (before++[entry])++gapEndpointProjection g exit := by
  simpa only [List.append_assoc,List.singleton_append,controlWord,gapEndpointProjection,
    List.tail_cons,List.flatMap_cons,List.flatMap_nil,List.append_nil] using
    gap_word_overlap g before entry [exit]

private theorem emitted_word (g : Net signature N B W) (before : List (Endpoint g))
    (entry exit : Endpoint g) (after : List (Endpoint g)) :
    ((occurrenceAt g before entry exit after).toList).map ControlOccurrence.bit=
      gapEndpointProjection g exit := by
  exact occurrenceAt_bits g before entry exit after

/-- The external scanner prefix is retained literally. Only its projected
word is transported: no locally rescanned record is equated to an OLD record. -/
private theorem scanFrom_prefix_projection (g : Net signature N B W)
    (before : List (Endpoint g)) (entry : Endpoint g) (tail : List (Endpoint g))
    (index : Nat) (occurrence : ControlOccurrence g)
    (picked : (scanFrom g before (entry::tail))[index]?=some occurrence) :
    controlWord g (occurrence.before++[occurrence.entry])=
      controlWord g (before++[entry])++(controlWord g (entry::tail)).take index := by
  induction tail generalizing before entry index with
  | nil => cases index <;> cases picked
  | cons exit after ih =>
    cases found : occurrenceAt g before entry exit after with
    | none =>
      have scan : scanFrom g before (entry::exit::after)=
          scanFrom g (before++[entry]) (exit::after) := by
        rw [scanFrom,found];rfl
      have noLetter : gapEndpointProjection g exit=[] := by
        have actual := emitted_word g before entry exit after
        rw [found] at actual
        exact actual.symm
      have next := ih (before++[entry]) exit index (by simpa only [scan] using picked)
      have word : controlWord g (entry::exit::after)=controlWord g (exit::after) := by
        change gapEndpointProjection g exit++controlWord g (exit::after)=_
        rw [noLetter,List.nil_append]
      rw [gap_word_snoc,noLetter,List.append_nil] at next
      rw [word]
      exact next
    | some head =>
      have scan : scanFrom g before (entry::exit::after)=
          head::scanFrom g (before++[entry]) (exit::after) := by
        rw [scanFrom,found];rfl
      have letter : gapEndpointProjection g exit=[head.bit] := by
        have actual := emitted_word g before entry exit after
        rw [found] at actual
        exact actual.symm
      rw [scan] at picked
      cases index with
      | zero =>
        have same : head=occurrence := Option.some.inj picked
        have geometry := occurrenceAt_geometry g before entry exit after head found
        rw [←same,geometry.1,geometry.2.1,List.take_zero,List.append_nil]
      | succ index =>
        have tailLookup : (scanFrom g (before++[entry]) (exit::after))[index]?=some occurrence := picked
        have next := ih (before++[entry]) exit index tailLookup
        have word : controlWord g (entry::exit::after)=head.bit::controlWord g (exit::after) := by
          change gapEndpointProjection g exit++controlWord g (exit::after)=_
          rw [letter];rfl
        rw [gap_word_snoc,letter] at next
        rw [word,List.take_succ_cons]
        simpa only [List.append_assoc,List.singleton_append] using next

/-- A real table lookup determines the complete word before that physical turn. -/
theorem controlOccurrences_prefix_projection (g : Net signature N B W)
    (es : List (Endpoint g)) (index : Nat) (occurrence : ControlOccurrence g)
    (picked : (controlOccurrences g es)[index]?=some occurrence) :
    controlWord g (occurrence.before++[occurrence.entry])=(controlWord g es).take index := by
  cases es with
  | nil => cases index <;> cases picked
  | cons entry tail =>
    simpa only [List.nil_append,controlWord,List.tail_cons,List.tail_nil,List.flatMap_nil]
      using scanFrom_prefix_projection g [] entry tail index occurrence picked

private theorem gap_take_at_entry (g : Net signature N B W) (es : List (Endpoint g))
    (occurrence : ControlOccurrence g) (member : occurrence∈controlOccurrences g es) :
    es.take (occurrence.physicalOrdinal+1)=occurrence.before++[occurrence.entry] := by
  have split := controlOccurrences_split g es occurrence member
  have atEntry := (controlOccurrences_entry_exit g es occurrence member).1
  rw [List.take_succ,atEntry]
  congr 1
  rw [split]
  exact List.take_left

private theorem gap_take_at_exit (g : Net signature N B W) (es : List (Endpoint g))
    (occurrence : ControlOccurrence g) (member : occurrence∈controlOccurrences g es) :
    es.take (occurrence.physicalOrdinal+2)=(occurrence.before++[occurrence.entry])++[occurrence.exit] := by
  have atExit := (controlOccurrences_entry_exit g es occurrence member).2
  have takeEq := gap_take_at_entry g es occurrence member
  rw [show occurrence.physicalOrdinal+2=(occurrence.physicalOrdinal+1)+1 from rfl,
    List.take_succ,atExit,takeEq]
  rfl

private theorem gap_occurrence_letter (g : Net signature N B W) (es : List (Endpoint g))
    (occurrence : ControlOccurrence g) (member : occurrence∈controlOccurrences g es) :
    gapEndpointProjection g occurrence.exit=[occurrence.bit] :=
  controlOccurrences_letter g es occurrence member

/-- Including the selected departure consumes exactly one emitted table letter. -/
theorem controlOccurrences_prefix_exit_projection (g : Net signature N B W)
    (es : List (Endpoint g)) (index : Nat) (occurrence : ControlOccurrence g)
    (picked : (controlOccurrences g es)[index]?=some occurrence) :
    controlWord g (es.take (occurrence.physicalOrdinal+2))=
      (controlWord g es).take (index+1) := by
  have member := List.mem_of_getElem? picked
  have letter := gap_occurrence_letter g es occurrence member
  have indexed := (controlOccurrences_lookup g es index occurrence picked).2.2.2.2
  rw [gap_take_at_exit g es occurrence member,gap_word_snoc,letter,
    controlOccurrences_prefix_projection g es index occurrence picked,List.take_succ,indexed]
  rfl

private theorem gap_scan_nil_of_word_nil (g : Net signature N B W) (segment : List (Endpoint g))
    (empty : controlWord g segment=[]) : controlOccurrences g segment=[] := by
  have projected := controlOccurrences_bits g segment
  rw [empty] at projected
  apply List.length_eq_zero_iff.mp
  simpa only [List.length_map,List.length_nil] using congrArg List.length projected

/-- The initial skipped interval ends at entry, before the selected emission. -/
theorem controlOccurrences_initial_gap (g : Net signature N B W) (es : List (Endpoint g))
    (occurrence : ControlOccurrence g)
    (picked : (controlOccurrences g es)[0]?=some occurrence) :
    controlOccurrences g (occurrence.before++[occurrence.entry])=[] := by
  apply gap_scan_nil_of_word_nil
  rw [controlOccurrences_prefix_projection g es 0 occurrence picked,List.take_zero]

/-- The terminal skipped interval starts at exit and excludes the selected turn. -/
theorem controlOccurrences_terminal_gap (g : Net signature N B W) (es : List (Endpoint g))
    (occurrence : ControlOccurrence g)
    (picked : (controlOccurrences g es).getLast?=some occurrence) :
    controlOccurrences g (occurrence.exit::occurrence.after)=[] := by
  obtain ⟨earlier,tableEq⟩ := List.getLast?_eq_some_iff.mp picked
  have atIndex : (controlOccurrences g es)[earlier.length]?=some occurrence := by
    rw [tableEq];simp
  have member := List.mem_of_getElem? atIndex
  have bits : controlWord g es=earlier.map ControlOccurrence.bit++[occurrence.bit] := by
    rw [←controlOccurrences_bits,tableEq,List.map_append];rfl
  have prefixWord := controlOccurrences_prefix_projection g es earlier.length occurrence atIndex
  rw [bits,show earlier.length=(earlier.map ControlOccurrence.bit).length from by simp only [List.length_map],
    List.take_left] at prefixWord
  have whole : controlWord g es=
      (controlWord g (occurrence.before++[occurrence.entry])++[occurrence.bit])++
        controlWord g (occurrence.exit::occurrence.after) := by
    rw [controlOccurrences_split g es occurrence member,
      gap_word_overlap g occurrence.before occurrence.entry (occurrence.exit::occurrence.after)]
    change controlWord g (occurrence.before++[occurrence.entry])++
      (gapEndpointProjection g occurrence.exit++controlWord g (occurrence.exit::occurrence.after))=_
    rw [gap_occurrence_letter g es occurrence member]
    exact (List.append_assoc _ _ _).symm
  have lengthEq := congrArg List.length whole
  rw [bits,prefixWord] at lengthEq
  simp only [List.length_append,List.length_singleton] at lengthEq
  have nilLength : (controlWord g (occurrence.exit::occurrence.after)).length=0 := by omega
  exact gap_scan_nil_of_word_nil g _ (List.length_eq_zero_iff.mp nilLength)

private theorem gap_take_add {A : Type} (xs : List A) (a b : Nat) :
    xs.take (a+b)=xs.take a++(xs.drop a).take b := by
  induction a generalizing xs with
  | zero => simp
  | succ a ih =>
    cases xs with
    | nil => simp
    | cons x xs =>
      simpa only [Nat.succ_add,List.take_succ_cons,List.drop_succ_cons,List.cons_append]
        using congrArg (List.cons x) (ih xs)

private theorem gap_drop_head {A : Type} (xs : List A) (n : Nat) :
    (xs.drop n).head?=xs[n]? := by
  induction n generalizing xs with
  | zero => cases xs <;> rfl
  | succ n ih =>
    cases xs with
    | nil => rfl
    | cons x xs => exact ih xs

private theorem gap_take_head {A : Type} (xs : List A) (n : Nat) (positive : 0<n) :
    (xs.take n).head?=xs.head? := by
  cases n with
  | zero => cases (Nat.not_lt_zero 0 positive)
  | succ n => cases xs <;> rfl

private theorem gap_word_append_head (g : Net signature N B W)
    (before segment : List (Endpoint g)) (first : Endpoint g)
    (head : segment.head?=some first) :
    controlWord g (before++segment)=
      controlWord g (before++[first])++controlWord g segment := by
  obtain ⟨tail,split⟩ := List.head?_eq_some_iff.mp head
  rw [split]
  exact gap_word_overlap g before first tail

/-- The literal physical interval excludes both selected departures. Repeated
visits and singleton intervals are retained, not replaced by adjacent letters. -/
theorem controlOccurrences_internal_partition (g : Net signature N B W)
    (es : List (Endpoint g)) (index : Nat) (writer reader : ControlOccurrence g)
    (atWriter : (controlOccurrences g es)[index]?=some writer)
    (atReader : (controlOccurrences g es)[index+1]?=some reader) :
    es=(es.take (writer.physicalOrdinal+1)++
      (es.drop (writer.physicalOrdinal+1)).take (reader.physicalOrdinal-writer.physicalOrdinal))++
        es.drop (reader.physicalOrdinal+1) := by
  have ordered := controlOccurrences_lookup_strict g es writer reader index (index+1)
    (Nat.lt_succ_self index) atWriter atReader
  have sumEq : writer.physicalOrdinal+1+(reader.physicalOrdinal-writer.physicalOrdinal)=
      reader.physicalOrdinal+1 := by omega
  have split := gap_take_add es (writer.physicalOrdinal+1)
    (reader.physicalOrdinal-writer.physicalOrdinal)
  rw [sumEq] at split
  calc
    es=es.take (reader.physicalOrdinal+1)++es.drop (reader.physicalOrdinal+1) :=
      (List.take_append_drop _ _).symm
    _=_ := congrArg (fun xs => xs++es.drop (reader.physicalOrdinal+1)) split

/-- Consecutive table entries force zero control emissions only BETWEEN the
selected physical turns; this says nothing about adjacency of their endpoints. -/
theorem controlOccurrences_internal_gap (g : Net signature N B W)
    (es : List (Endpoint g)) (index : Nat) (writer reader : ControlOccurrence g)
    (atWriter : (controlOccurrences g es)[index]?=some writer)
    (atReader : (controlOccurrences g es)[index+1]?=some reader) :
    controlOccurrences g ((es.drop (writer.physicalOrdinal+1)).take
      (reader.physicalOrdinal-writer.physicalOrdinal))=[] := by
  let middle := (es.drop (writer.physicalOrdinal+1)).take
    (reader.physicalOrdinal-writer.physicalOrdinal)
  have ordered := controlOccurrences_lookup_strict g es writer reader index (index+1)
    (Nat.lt_succ_self index) atWriter atReader
  have writerMember := List.mem_of_getElem? atWriter
  have readerMember := List.mem_of_getElem? atReader
  have exitAt := (controlOccurrences_entry_exit g es writer writerMember).2
  have positive : 0<reader.physicalOrdinal-writer.physicalOrdinal := by omega
  have middleHead : middle.head?=some writer.exit := by
    change ((es.drop (writer.physicalOrdinal+1)).take _).head?=_
    rw [gap_take_head _ _ positive,gap_drop_head,exitAt]
  have sumEq : writer.physicalOrdinal+1+(reader.physicalOrdinal-writer.physicalOrdinal)=
      reader.physicalOrdinal+1 := by omega
  have split : es.take (reader.physicalOrdinal+1)=es.take (writer.physicalOrdinal+1)++middle := by
    simpa only [sumEq] using gap_take_add es (writer.physicalOrdinal+1)
      (reader.physicalOrdinal-writer.physicalOrdinal)
  have writerExitTake : es.take (writer.physicalOrdinal+1)++[writer.exit]=
      es.take (writer.physicalOrdinal+2) := by
    symm
    rw [show writer.physicalOrdinal+2=(writer.physicalOrdinal+1)+1 from rfl,
      List.take_succ]
    rw [exitAt]
    rfl
  have writerWord := controlOccurrences_prefix_exit_projection g es index writer atWriter
  have readerWord : controlWord g (es.take (reader.physicalOrdinal+1))=
      (controlWord g es).take (index+1) := by
    rw [gap_take_at_entry g es reader readerMember]
    exact controlOccurrences_prefix_projection g es (index+1) reader atReader
  have factor := gap_word_append_head g (es.take (writer.physicalOrdinal+1)) middle writer.exit middleHead
  rw [←split,writerExitTake,writerWord,readerWord] at factor
  have lengthEq := congrArg List.length factor
  simp only [List.length_append] at lengthEq
  have nilLength : (controlWord g middle).length=0 := by omega
  exact gap_scan_nil_of_word_nil g middle (List.length_eq_zero_iff.mp nilLength)

/-- A data-only interval of the actual selected focus. It does not contain
labels, contexts, a transparency witness, or a desired rewrite site. -/
def PhysicalControlFocus.skipped {g : Net signature N B W} (es : List (Endpoint g)) :
    PhysicalControlFocus g → List (Endpoint g)
  | .initialReader occurrence => occurrence.before++[occurrence.entry]
  | .terminalWriter occurrence => occurrence.exit::occurrence.after
  | .internalPeak _ writer reader =>
      (es.drop (writer.physicalOrdinal+1)).take (reader.physicalOrdinal-writer.physicalOrdinal)

/-- The selector's computed interval has no emissions, without caller empty data. -/
theorem selectPhysicalControlFocus_skipped_scan_nil (g : Net signature N B W)
    (es : List (Endpoint g)) (focus : PhysicalControlFocus g)
    (chosen : selectPhysicalControlFocus g es=some focus) :
    controlOccurrences g (focus.skipped es)=[] := by
  have spec := selectPhysicalControlFocus_sound g es focus chosen
  cases focus with
  | initialReader occurrence => exact controlOccurrences_initial_gap g es occurrence spec.1
  | terminalWriter occurrence => exact controlOccurrences_terminal_gap g es occurrence spec.1
  | internalPeak index writer reader =>
    exact controlOccurrences_internal_gap g es index writer reader spec.1 spec.2.1

/-- W-transparency is inferred only for an actual RedexConnection, whose
control_only property excludes invisible proper-node turns. -/
theorem selectPhysicalControlFocus_skipped_transparent {g : Net signature N B W}
    (connection : RedexConnection g) (focus : PhysicalControlFocus g)
    (chosen : selectPhysicalControlFocus g connection.edges=some focus) :
    TransparentTurns (g:=g) (focus.skipped connection.edges) := by
  have spec := selectPhysicalControlFocus_sound g connection.edges focus chosen
  cases focus with
  | initialReader occurrence =>
    exact occurrence_prefix_zero_scan_transparent connection occurrence
      (List.mem_of_getElem? spec.1) (controlOccurrences_initial_gap g connection.edges occurrence spec.1)
  | terminalWriter occurrence =>
    have member : occurrence∈controlOccurrences g connection.edges := by
      obtain ⟨earlier,split⟩ := List.getLast?_eq_some_iff.mp spec.1
      rw [split];exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
    exact occurrence_suffix_zero_scan_transparent connection occurrence member
      (controlOccurrences_terminal_gap g connection.edges occurrence spec.1)
  | internalPeak index writer reader =>
    exact connection_zero_scan_interval connection
      (connection.edges.take (writer.physicalOrdinal+1))
      ((connection.edges.drop (writer.physicalOrdinal+1)).take
        (reader.physicalOrdinal-writer.physicalOrdinal))
      (connection.edges.drop (reader.physicalOrdinal+1))
      (by simpa only [List.append_assoc] using
        controlOccurrences_internal_partition g connection.edges index writer reader spec.1 spec.2.1)
      (controlOccurrences_internal_gap g connection.edges index writer reader spec.1 spec.2.1)

#print axioms Lamping.AG.ExposureScheduling.controlOccurrences_prefix_projection
#print axioms Lamping.AG.ExposureScheduling.controlOccurrences_prefix_exit_projection
#print axioms Lamping.AG.ExposureScheduling.controlOccurrences_initial_gap
#print axioms Lamping.AG.ExposureScheduling.controlOccurrences_terminal_gap
#print axioms Lamping.AG.ExposureScheduling.controlOccurrences_internal_partition
#print axioms Lamping.AG.ExposureScheduling.controlOccurrences_internal_gap
#print axioms Lamping.AG.ExposureScheduling.PhysicalControlFocus.skipped
#print axioms Lamping.AG.ExposureScheduling.selectPhysicalControlFocus_skipped_scan_nil
#print axioms Lamping.AG.ExposureScheduling.selectPhysicalControlFocus_skipped_transparent

end
end Lamping.AG.ExposureScheduling
