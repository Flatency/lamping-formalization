import Lamping.Lamping.InitialOriginalWordSeed
import Lamping.Checks.InitialOriginalWordMarkers
import Lamping.Lamping.InitialMatching

namespace Lamping.Checks.InitialOriginalWordSeedChecks
open AG Graph Lambda Lambda.Labelled

private def original : LTerm := .lam (.atom 7) (.var (.atom 11) 0)
private abbrev net := (encode 0 original.erase).net

theorem actual_closed_root_whole_fold :
    ∃ (fragment : OccurrenceFragment original net (.inl ()) [])
      (addr : Addressing net (boundaryAddressAt [])) (a b : Context),
      fragment.term=original ∧ Labelling net fragment.fragment.access.val a b ∧
      physicalOriginalWord (initialOriginalWeights original 0 addr) fragment.fragment.segments=[⟨7,false⟩] ∧
      ∀ i : Fin fragment.fragment.segments.length,
        initialAtomAddress addr.nodes fragment.fragment.segments[i]=none ∧
        initialOriginalEntry original 0 addr (net.wire fragment.fragment.segments[i])=[] := by
  obtain ⟨fragment,addr,a,b,_middle,termEq,whole,_prefixEvidence,_initial,_reversal,
    _i,_marked,_entry,_unique⟩ := InitialOriginalWordMarkersChecks.actual_closed_root_marker
  have folded := fragment.initial_original_word_given_assignment addr whole
  have literal := folded.trans (congrArg (fun t : LTerm => t.label.edgeWord) termEq)
  exact ⟨fragment,addr,a,b,termEq,whole,literal,fragment.initial_negative_factors_given_assignment addr whole⟩

theorem actual_closed_body_whole_fold :
    ∃ (fragment : OccurrenceFragment original net (.inl ()) [.body])
      (addr : Addressing net (boundaryAddressAt [])) (a b : Context),
      fragment.term=.var (.atom 11) 0 ∧ sourceBinder fragment.environment 0=.lamBind (.atom 7) ∧
      Labelling net fragment.fragment.access.val a b ∧
      physicalOriginalWord (initialOriginalWeights original 0 addr) fragment.fragment.segments=[⟨11,false⟩] ∧
      ∀ i : Fin fragment.fragment.segments.length,
        initialAtomAddress addr.nodes fragment.fragment.segments[i]=none ∧
        initialOriginalEntry original 0 addr (net.wire fragment.fragment.segments[i])=[] := by
  obtain ⟨fragment,addr,a,b,_middle,termEq,binder,whole,_prefixEvidence,_initial,_reversal,
    _i,_marked,_entry,_unique⟩ := InitialOriginalWordMarkersChecks.actual_closed_body_variable_marker
  have folded := fragment.initial_original_word_given_assignment addr whole
  have literal := folded.trans (congrArg (fun t : LTerm => t.label.edgeWord) termEq)
  exact ⟨fragment,addr,a,b,termEq,binder,whole,literal,fragment.initial_negative_factors_given_assignment addr whole⟩

private def support (b : Bool) : List Nat := if b then [42] else []

theorem pure_empty_selected_and_repeated_values :
    [true,false,false].flatMap support=[42] ∧
    [true,true,false].flatMap (fun _ => ([] : List Nat))=[] := by
  constructor
  · apply flatMap_unique_ordinal [true,false,false] support ⟨0,by decide⟩
    intro j different
    rcases j with ⟨j,bound⟩
    change j<3 at bound
    have casesJ : j=0 ∨ j=1 ∨ j=2 := by omega
    rcases casesJ with rfl|rfl|rfl
    · exact False.elim (different (Fin.ext rfl))
    · rfl
    · rfl
  · exact flatMap_unique_ordinal [true,true,false] (fun _ => ([] : List Nat))
      ⟨0,by decide⟩ (fun _ _ => rfl)

private def duplicated : LTerm :=
  .lam (.atom 7) (.app (.atom 11) (.var (.atom 13) 0) (.var (.atom 17) 0))
private abbrev dupNet := (encode 0 duplicated.erase).net

/-- Two actual variable occurrences of a genuinely duplicated INITIAL
encoding; each consumes its own supplied whole assignment in the same graph. -/
theorem actual_closed_duplicate_occurrence_folds :
    ∃ (addr : Addressing dupNet (boundaryAddressAt []))
      (left : OccurrenceFragment duplicated dupNet (.inl ()) [.body,.fn])
      (right : OccurrenceFragment duplicated dupNet (.inl ()) [.body,.arg])
      (al bl ar br : Context),
      sourceBinder left.environment 0=.lamBind (.atom 7) ∧
      sourceBinder right.environment 0=.lamBind (.atom 7) ∧
      Labelling dupNet left.fragment.access.val al bl ∧
      Labelling dupNet right.fragment.access.val ar br ∧
      physicalOriginalWord (initialOriginalWeights duplicated 0 addr) left.fragment.segments=[⟨13,false⟩] ∧
      physicalOriginalWord (initialOriginalWeights duplicated 0 addr) right.fragment.segments=[⟨17,false⟩] := by
  have closed : Closed duplicated.erase := by change 0<1 ∧ 0<1;exact ⟨by decide,by decide⟩
  have matching := encode_closed_matches duplicated.erase closed 0
  have leftOccurrence : SourceSubterm [] .external duplicated [.body,.fn]
      [.atom 7] (.appFn (.atom 11)) (.var (.atom 13) 0) := .body (.fn .nil)
  have rightOccurrence : SourceSubterm [] .external duplicated [.body,.arg]
      [.atom 7] (.appArg (.atom 11)) (.var (.atom 17) 0) := .body (.arg .nil)
  obtain ⟨leftPhysical⟩ := matching.base_source_edge_fragment closed leftOccurrence
  obtain ⟨rightPhysical⟩ := matching.base_source_edge_fragment closed rightOccurrence
  let left : OccurrenceFragment duplicated dupNet (.inl ()) [.body,.fn] :=
    ⟨.var (.atom 13) 0,[.atom 7],.appFn (.atom 11),leftOccurrence,leftPhysical⟩
  let right : OccurrenceFragment duplicated dupNet (.inl ()) [.body,.arg] :=
    ⟨.var (.atom 17) 0,[.atom 7],.appArg (.atom 11),rightOccurrence,rightPhysical⟩
  obtain ⟨addr⟩ := encode_addressing duplicated.erase 0
  obtain ⟨al,bl,leftWhole⟩ := leftPhysical.access.property.1.1
  obtain ⟨ar,br,rightWhole⟩ := rightPhysical.access.property.1.1
  have leftFold := left.initial_original_word_given_assignment addr leftWhole
  have rightFold := right.initial_original_word_given_assignment addr rightWhole
  exact ⟨addr,left,right,al,bl,ar,br,rfl,rfl,leftWhole,rightWhole,leftFold,rightFold⟩

#print axioms actual_closed_root_whole_fold
#print axioms actual_closed_body_whole_fold
#print axioms pure_empty_selected_and_repeated_values
#print axioms actual_closed_duplicate_occurrence_folds
end Lamping.Checks.InitialOriginalWordSeedChecks
