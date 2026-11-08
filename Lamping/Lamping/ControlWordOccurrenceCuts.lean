import Lamping.Lamping.ControlWordOccurrences

namespace Lamping.AG.ExposureScheduling
open Graph

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]

private theorem option_member_some {A : Type} {value : A} {optional : Option A}
    (member : value∈optional.toList) : optional=some value := by
  cases optional with
  | none => cases member
  | some other =>
    have same : value=other := List.mem_singleton.mp member
    cases same
    rfl

theorem occurrenceAt_geometry (g : Net signature N B W) (before : List (Endpoint g))
    (entry exit : Endpoint g) (after : List (Endpoint g)) (occurrence : ControlOccurrence g)
    (picked : occurrenceAt g before entry exit after=some occurrence) :
    occurrence.before=before ∧ occurrence.entry=entry ∧ occurrence.exit=exit ∧ occurrence.after=after := by
  cases exit with
  | inr boundary => simp [occurrenceAt] at picked
  | inl nodeport =>
    rcases nodeport with ⟨node,outgoing⟩
    simp only [occurrenceAt] at picked
    cases selected : (controlPortWord (g.label node).sort outgoing).head? with
    | none => simp only [selected,Option.map_none] at picked; cases picked
    | some bit =>
      have same : (⟨before,entry,node,outgoing,after,bit⟩ : ControlOccurrence g)=occurrence :=
        Option.some.inj (by simpa only [selected,Option.map_some] using picked)
      cases same
      exact ⟨rfl,rfl,rfl,rfl⟩

theorem scanFrom_split (g : Net signature N B W) (before es : List (Endpoint g))
    (occurrence : ControlOccurrence g) (member : occurrence∈scanFrom g before es) :
    before++es=occurrence.before++occurrence.entry::occurrence.exit::occurrence.after := by
  revert member
  induction es generalizing before with
  | nil => intro member; cases member
  | cons entry tail ih =>
    intro member
    cases tail with
    | nil => cases member
    | cons exit after =>
      change occurrence∈(occurrenceAt g before entry exit after).toList++
        scanFrom g (before++[entry]) (exit::after) at member
      rcases List.mem_append.mp member with current | later
      · have picked := option_member_some current
        obtain ⟨beforeEq,entryEq,exitEq,afterEq⟩ :=
          occurrenceAt_geometry g before entry exit after occurrence picked
        rw [beforeEq,entryEq,exitEq,afterEq]
      · have result := ih (before++[entry]) later
        simpa only [List.append_assoc,List.singleton_append] using result

theorem scanFrom_ordinal_lower (g : Net signature N B W) (before es : List (Endpoint g))
    (occurrence : ControlOccurrence g) (member : occurrence∈scanFrom g before es) :
    before.length≤occurrence.physicalOrdinal := by
  revert member
  induction es generalizing before with
  | nil => intro member; cases member
  | cons entry tail ih =>
    intro member
    cases tail with
    | nil => cases member
    | cons exit after =>
      change occurrence∈(occurrenceAt g before entry exit after).toList++
        scanFrom g (before++[entry]) (exit::after) at member
      rcases List.mem_append.mp member with current | later
      · have picked := option_member_some current
        have geometry := occurrenceAt_geometry g before entry exit after occurrence picked
        change before.length≤occurrence.before.length
        simpa only [geometry.1] using Nat.le_refl before.length
      · have result := ih (before++[entry]) later
        have shorter : before.length≤(before++[entry]).length := by
          simpa only [List.length_append,List.length_singleton] using Nat.le_succ before.length
        exact Nat.le_trans shorter result

theorem controlOccurrences_split (g : Net signature N B W) (es : List (Endpoint g))
    (occurrence : ControlOccurrence g) (member : occurrence∈controlOccurrences g es) :
    es=occurrence.before++occurrence.entry::occurrence.exit::occurrence.after := by
  simpa only [controlOccurrences,List.nil_append] using scanFrom_split g [] es occurrence member

private theorem pair_at_cut {A : Type} (before : List A) (entry exit : A) (after : List A) :
    (entry,exit)∈(before++entry::exit::after).zip (before++entry::exit::after).tail := by
  induction before with
  | nil => exact List.mem_cons.mpr (Or.inl rfl)
  | cons first before ih =>
    cases before with
    | nil => exact List.mem_cons_of_mem _ ih
    | cons second before => exact List.mem_cons_of_mem _ ih

theorem controlOccurrences_zip (g : Net signature N B W) (es : List (Endpoint g))
    (occurrence : ControlOccurrence g) (member : occurrence∈controlOccurrences g es) :
    (occurrence.entry,occurrence.exit)∈es.zip es.tail := by
  rw [controlOccurrences_split g es occurrence member]
  exact pair_at_cut _ _ _ _

private theorem entries_at_cut {A : Type} (before : List A) (entry exit : A) (after : List A) :
    (before++entry::exit::after)[before.length]?=some entry ∧
      (before++entry::exit::after)[before.length+1]?=some exit := by
  induction before with
  | nil => exact ⟨rfl,rfl⟩
  | cons first before ih =>
    simpa only [List.cons_append,List.length_cons,List.getElem?_cons_succ] using ih

theorem controlOccurrences_entry_exit (g : Net signature N B W) (es : List (Endpoint g))
    (occurrence : ControlOccurrence g) (member : occurrence∈controlOccurrences g es) :
    es[occurrence.physicalOrdinal]?=some occurrence.entry ∧
      es[occurrence.physicalOrdinal+1]?=some occurrence.exit := by
  rw [controlOccurrences_split g es occurrence member]
  exact entries_at_cut _ _ _ _

private theorem map_lookup {A C : Type} (f : A → C) (items : List A) {index : Nat} {value : A}
    (picked : items[index]?=some value) : (items.map f)[index]?=some (f value) := by
  induction items generalizing index with
  | nil => cases index <;> cases picked
  | cons first items ih =>
    cases index with
    | zero =>
      have same : first=value := Option.some.inj picked
      cases same
      rfl
    | succ index => exact ih picked

/-- Table lookup identifies THIS physical occurrence, not merely some visit
with the same bit or endpoint. No path or semantic premise is needed. -/
theorem controlOccurrences_lookup (g : Net signature N B W) (es : List (Endpoint g))
    (index : Nat) (occurrence : ControlOccurrence g)
    (picked : (controlOccurrences g es)[index]?=some occurrence) :
    es=occurrence.before++occurrence.entry::occurrence.exit::occurrence.after ∧
    (occurrence.entry,occurrence.exit)∈es.zip es.tail ∧
    es[occurrence.physicalOrdinal]?=some occurrence.entry ∧
    es[occurrence.physicalOrdinal+1]?=some occurrence.exit ∧
    (controlWord g es)[index]?=some occurrence.bit := by
  have member := List.mem_of_getElem? picked
  have positions := controlOccurrences_entry_exit g es occurrence member
  refine ⟨controlOccurrences_split g es occurrence member,
    controlOccurrences_zip g es occurrence member,positions.1,positions.2,?_⟩
  have bits := map_lookup ControlOccurrence.bit (controlOccurrences g es) picked
  rw [controlOccurrences_bits] at bits
  exact bits

#print axioms Lamping.AG.ExposureScheduling.occurrenceAt_geometry
#print axioms Lamping.AG.ExposureScheduling.scanFrom_split
#print axioms Lamping.AG.ExposureScheduling.scanFrom_ordinal_lower
#print axioms Lamping.AG.ExposureScheduling.controlOccurrences_split
#print axioms Lamping.AG.ExposureScheduling.controlOccurrences_zip
#print axioms Lamping.AG.ExposureScheduling.controlOccurrences_entry_exit
#print axioms Lamping.AG.ExposureScheduling.controlOccurrences_lookup

end
end Lamping.AG.ExposureScheduling
