import Lamping.Lambda.BetaPreimageLabels
import Lamping.Lambda.DirectedFreshMarkerParsing
namespace Lamping.Lambda.Labelled
private theorem retained_root_label
    (retained : ∀stamp,body≠LTerm.var stamp 0) :
    (LTerm.contract beta alpha body argument).label=(beta.concat alpha.over).concat body.label := by
  cases body with
  | var stamp index =>
    cases index with
    | zero => exact False.elim (retained stamp rfl)
    | succ index => rfl
  | lam => rfl
  | app => rfl

/-- Incoming labels only gain a prefix at their actual retained/copied
node origin. In the overlap case the rightmost new separator is under. -/
theorem StepAt.beta_node_label_suffix
    {site p oldPosition : Path} {source target body argument current : LTerm} {beta alpha : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (origin : BetaNodePreimage body argument site p oldPosition)
    (lookup : target.subterm p=some current) :
    ∃old,source.subterm oldPosition=some old ∧
      (current.label=old.label ∨∃pre marker,
        marker.MarksDegree alpha ∧current.label.letters=pre++marker::old.label.letters) := by
  cases origin with
  | context outside =>
    have uncreated : ¬BetaCreatedIncoming body site p := by
      intro created
      rcases betaCreatedIncoming_iff.mp created with result |⟨q,occurs,copy⟩
      · exact outside ⟨[],by simpa only [List.append_nil] using result⟩
      · exact outside ⟨q,copy⟩
    obtain ⟨old,atOld,same⟩ := step.beta_preimage_label redex (.context outside) lookup uncreated
    exact ⟨old,atOld,Or.inl same.symm⟩
  | @retained relative old oldLookup nonselected =>
    have globalOld : source.subterm ((site++[.fn,.body])++relative)=some old := by
      simp only [List.append_assoc,LTerm.subterm_append,redex,Option.bind_some,LTerm.subterm,oldLookup]
    have localLookup : (LTerm.contract beta alpha body argument).subterm relative=some current := by
      rw [LTerm.subterm_append,step.contract_lookup redex,Option.bind_some] at lookup
      exact lookup
    by_cases root : relative=[]
    · subst relative
      have oldEq : body=old := by simpa only [LTerm.subterm,Option.some.injEq] using oldLookup
      subst old
      have currentEq : LTerm.contract beta alpha body argument=current := by simpa only [LTerm.subterm,Option.some.injEq] using localLookup
      have labelEq : current.label=(beta.concat alpha.over).concat body.label := by
        rw [←currentEq]
        exact retained_root_label nonselected
      refine ⟨body,globalOld,Or.inr ⟨beta.letters,.over alpha,Or.inl rfl,?_⟩⟩
      rw [labelEq]
      simp only [Label.letters_concat,Label.over,Label.letters,List.cons_append,List.nil_append,List.append_assoc]
    · exact ⟨old,globalOld,Or.inl (contract_retained_node_label oldLookup nonselected localLookup root)⟩
  | @copied q relative old occurs oldLookup =>
    have globalOld : source.subterm ((site++[.arg])++relative)=some old := by
      simp only [List.append_assoc,LTerm.subterm_append,redex,Option.bind_some,LTerm.subterm,oldLookup]
    have localLookup : (LTerm.contract beta alpha body argument).subterm (q++relative)=some current := by
      rw [List.append_assoc,LTerm.subterm_append,step.contract_lookup redex,Option.bind_some] at lookup
      exact lookup
    by_cases root : relative=[]
    · subst relative
      have oldEq : argument=old := by simpa only [LTerm.subterm,Option.some.injEq] using oldLookup
      subst old
      simp only [List.append_nil] at localLookup
      obtain ⟨stamp,atVariable,labelEq⟩ := LTerm.contract_argument_incoming_label occurs localLookup
      by_cases overlap : q=[]
      · rw [if_pos overlap] at labelEq
        refine ⟨argument,globalOld,Or.inr
          ⟨beta.letters++(.over alpha)::stamp.letters,.under alpha,Or.inr rfl,?_⟩⟩
        rw [labelEq]
        simp only [LTerm.label,Label.letters_concat,Label.over,Label.under,Label.letters,
          List.cons_append,List.nil_append,List.append_assoc]
      · rw [if_neg overlap] at labelEq
        refine ⟨argument,globalOld,Or.inr ⟨stamp.letters,.under alpha,Or.inr rfl,?_⟩⟩
        rw [labelEq]
        simp only [Label.letters_concat,Label.under,Label.letters,List.cons_append,List.nil_append]
    · rw [LTerm.subterm_append] at localLookup
      cases atCopy : (LTerm.contract beta alpha body argument).subterm q with
      | none => rw [atCopy] at localLookup;cases localLookup
      | some copy =>
        rw [atCopy,Option.bind_some] at localLookup
        obtain ⟨original,atOriginal,labelEq⟩ :=
          (LTerm.contract_argument_copy_interior occurs atCopy).nonroot_node localLookup root
        have same := Option.some.inj (atOriginal.symm.trans oldLookup)
        subst original
        exact ⟨old,globalOld,Or.inl labelEq.symm⟩

/-- Reverse-word form keeps the complete old label, including empty-prefix
cases. This is word direction, not a prerequisite-reading assumption. -/
theorem StepAt.beta_node_label_suffix_reverse
    {site p oldPosition : Path} {source target body argument current : LTerm} {beta alpha : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (origin : BetaNodePreimage body argument site p oldPosition)
    (lookup : target.subterm p=some current) :
    ∃old,source.subterm oldPosition=some old ∧
      (current.label=old.label ∨∃marker post,marker.MarksDegree alpha ∧
        current.label.readLetters false=old.label.readLetters false++marker::post) := by
  obtain ⟨old,atOld,same |⟨pre,marker,marks,equation⟩⟩ := step.beta_node_label_suffix redex origin lookup
  · exact ⟨old,atOld,Or.inl same⟩
  · refine ⟨old,atOld,Or.inr ⟨marker,pre.reverse,marks,?_⟩⟩
    change current.label.letters.reverse=old.label.letters.reverse++marker::pre.reverse
    rw [equation]
    simp only [List.reverse_append,List.reverse_cons,List.singleton_append,List.append_assoc]
#print axioms StepAt.beta_node_label_suffix
#print axioms StepAt.beta_node_label_suffix_reverse

/-- Source safety makes the complete THIS-origin label the safe suffix
following the last marker. No current incoming-label equality is assumed. -/
theorem StepAt.beta_node_last_marker
    {site p oldPosition : Path} {source target body argument current : LTerm} {beta alpha : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (origin : BetaNodePreimage body argument site p oldPosition)
    (lookup : target.subterm p=some current)
    (sourceSafe : source.OuterBarsSafe (fun payload=>payload≠alpha))
    (marked : ¬current.label.OuterBarsSafe (fun payload=>payload≠alpha)) :
    ∃old pre marker,source.subterm oldPosition=some old ∧
      old.label.OuterBarsSafe (fun payload=>payload≠alpha) ∧marker.MarksDegree alpha ∧
      current.label.letters=pre++marker::old.label.letters ∧
      current.label.readLetters false=old.label.readLetters false++marker::pre.reverse := by
  obtain ⟨old,atOld,unchanged |⟨pre,marker,marks,equation⟩⟩ := step.beta_node_label_suffix redex origin lookup
  · have safe := (LTerm.outerBarsSafe_iff _ _).mp sourceSafe old.label (LTerm.label_mem_of_subterm atOld)
    exact False.elim (marked (unchanged ▸ safe))
  · have safe := (LTerm.outerBarsSafe_iff _ _).mp sourceSafe old.label (LTerm.label_mem_of_subterm atOld)
    refine ⟨old,pre,marker,atOld,safe,marks,equation,?_⟩
    change current.label.letters.reverse=old.label.letters.reverse++marker::pre.reverse
    rw [equation]
    simp only [List.reverse_append,List.reverse_cons,List.singleton_append,List.append_assoc]
#print axioms StepAt.beta_node_last_marker
end Lamping.Lambda.Labelled
