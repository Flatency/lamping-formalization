import Lamping.Lamping.InitialOriginalWordMarkers
import Lamping.Lamping.InitialMatching

namespace Lamping.Checks.InitialOriginalWordMarkersChecks
open AG Graph Lambda Lambda.Labelled

private def original : LTerm := .lam (.atom 7) (.var (.atom 11) 0)
private abbrev net := (encode 0 original.erase).net
private theorem closed : Closed original.erase := by change 0<1;decide

theorem actual_closed_root_marker :
    ∃ (fragment : OccurrenceFragment original net (.inl ()) [])
      (addr : Addressing net (boundaryAddressAt [])) (a b middle : Context),
      fragment.term=original ∧ Labelling net fragment.fragment.access.val a b ∧
      (fragment.fragment.before=[] ∧ middle=a ∨ Labelling net fragment.fragment.before a middle) ∧
      InitialLabelling (g:=net) fragment.fragment.segments middle b ∧
      OriginalWordReversal (initialOriginalWeights original 0 addr) ∧
      ∃ i : Fin fragment.fragment.segments.length,
        InitialMarkerAt addr.nodes fragment.fragment.segments[i] [] ∧
        initialOriginalEntry original 0 addr fragment.fragment.segments[i]=[⟨7,false⟩] ∧
        ∀ j : Fin fragment.fragment.segments.length,∀ p,
          InitialMarkerAt addr.nodes fragment.fragment.segments[j] p → j=i ∧ p=[] := by
  have matching := encode_closed_matches original.erase closed 0
  have occurrence : SourceSubterm [] .external original [] [] .external original := .nil
  obtain ⟨physical⟩ := matching.base_source_edge_fragment closed occurrence
  let fragment : OccurrenceFragment original net (.inl ()) [] :=
    ⟨original,[],.external,occurrence,physical⟩
  obtain ⟨addr⟩ := encode_addressing original.erase 0
  obtain ⟨a,b,whole⟩ := physical.access.property.1.1
  obtain ⟨middle,prefixEvidence,initialSuffix,i,marked,unique⟩ :=
    fragment.initial_unique_marker_given_assignment addr whole
  have positive : initialOriginalEntry original 0 addr fragment.fragment.segments[i]=[⟨7,false⟩] := by
    unfold initialOriginalEntry
    change initialAtomAddress addr.nodes (net.wire fragment.fragment.segments[i])=some [] at marked
    rw [marked]
    rfl
  have reversal : OriginalWordReversal (initialOriginalWeights original 0 addr) :=
    symmetrizedOriginalWord_reversal net (initialOriginalEntry original 0 addr)
  exact ⟨fragment,addr,a,b,middle,rfl,whole,prefixEvidence,initialSuffix,reversal,i,marked,positive,unique⟩

theorem actual_closed_body_variable_marker :
    ∃ (fragment : OccurrenceFragment original net (.inl ()) [.body])
      (addr : Addressing net (boundaryAddressAt [])) (a b middle : Context),
      fragment.term=.var (.atom 11) 0 ∧ sourceBinder fragment.environment 0=.lamBind (.atom 7) ∧
      Labelling net fragment.fragment.access.val a b ∧
      (fragment.fragment.before=[] ∧ middle=a ∨ Labelling net fragment.fragment.before a middle) ∧
      InitialLabelling (g:=net) fragment.fragment.segments middle b ∧
      OriginalWordReversal (initialOriginalWeights original 0 addr) ∧
      ∃ i : Fin fragment.fragment.segments.length,
        InitialMarkerAt addr.nodes fragment.fragment.segments[i] [.body] ∧
        initialOriginalEntry original 0 addr fragment.fragment.segments[i]=[⟨11,false⟩] ∧
        ∀ j : Fin fragment.fragment.segments.length,∀ p,
          InitialMarkerAt addr.nodes fragment.fragment.segments[j] p → j=i ∧ p=[.body] := by
  have matching := encode_closed_matches original.erase closed 0
  have occurrence : SourceSubterm [] .external original [.body] [.atom 7] (.lamBody (.atom 7))
      (.var (.atom 11) 0) := .body .nil
  obtain ⟨physical⟩ := matching.base_source_edge_fragment closed occurrence
  let fragment : OccurrenceFragment original net (.inl ()) [.body] :=
    ⟨.var (.atom 11) 0,[.atom 7],.lamBody (.atom 7),occurrence,physical⟩
  obtain ⟨addr⟩ := encode_addressing original.erase 0
  obtain ⟨a,b,whole⟩ := physical.access.property.1.1
  obtain ⟨middle,prefixEvidence,initialSuffix,i,marked,unique⟩ :=
    fragment.initial_unique_marker_given_assignment addr whole
  have positive : initialOriginalEntry original 0 addr fragment.fragment.segments[i]=[⟨11,false⟩] := by
    unfold initialOriginalEntry
    change initialAtomAddress addr.nodes (net.wire fragment.fragment.segments[i])=some [.body] at marked
    rw [marked]
    rfl
  have reversal : OriginalWordReversal (initialOriginalWeights original 0 addr) :=
    symmetrizedOriginalWord_reversal net (initialOriginalEntry original 0 addr)
  exact ⟨fragment,addr,a,b,middle,rfl,rfl,whole,prefixEvidence,initialSuffix,reversal,i,marked,positive,unique⟩

#print axioms actual_closed_root_marker
#print axioms actual_closed_body_variable_marker
end Lamping.Checks.InitialOriginalWordMarkersChecks
