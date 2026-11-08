import Lamping.Lambda.DirectedReadingCreation
namespace Lamping.Lambda.Labelled

/-- Complete local words, including the extra separator at a root overlap.
The additional endpoint is an actual source lookup, never an unconstrained rest. -/
def ExactDirectedReadingFormula (source : LTerm) (site : Path) (alpha : Label)
    (forward : Bool) (firstNode lastNode : LTerm) (marker : Letter) (current : LTerm) : Prop :=
  current.label.readLetters forward=firstNode.label.readLetters forward++marker::lastNode.label.readLetters forward ∨
  (forward=true ∧marker=.over alpha ∧∃argument,source.subterm (site++[.arg])=some argument ∧
    current.label.readLetters forward=firstNode.label.readLetters forward++marker::
      (lastNode.label.readLetters forward++(.under alpha)::argument.label.letters)) ∨
  (forward=false ∧marker=.under alpha ∧∃app,source.subterm site=some app ∧
    current.label.readLetters forward=firstNode.label.readLetters forward++marker::
      (lastNode.label.readLetters forward++(.over alpha)::app.label.letters.reverse))

private theorem no_self_function (p : Path) : p≠p++[.fn] := by
  intro same
  have lengths := congrArg List.length same
  simp only [List.length_append,List.length_cons,List.length_nil] at lengths
  omega

private theorem contract_root_word (beta alpha : Label) (body argument : LTerm) :
    (LTerm.contract beta alpha body argument).label.letters=
      beta.letters++(.over alpha)::body.label.letters ∨
    ∃stamp,body=.var stamp 0 ∧
      (LTerm.contract beta alpha body argument).label.letters=
        beta.letters++(.over alpha)::(body.label.letters++(.under alpha)::argument.label.letters) := by
  cases body with
  | var stamp index =>
    cases index with
    | zero =>
      refine Or.inr ⟨stamp,rfl,?_⟩
      cases argument <;>
        simp only [LTerm.contract,LTerm.subst,LTerm.single,LTerm.prepend,LTerm.label,
          Label.letters_concat,Label.over,Label.under,Label.letters,
          List.cons_append,List.nil_append,List.append_assoc]
    | succ index =>
      apply Or.inl
      change ((beta.concat alpha.over).concat stamp).letters=_
      simp only [LTerm.label,Label.letters_concat,Label.over,Label.letters,
        List.cons_append,List.nil_append,List.append_assoc]
  | lam stamp inner =>
    apply Or.inl
    change ((beta.concat alpha.over).concat stamp).letters=_
    simp only [LTerm.label,Label.letters_concat,Label.over,Label.letters,
      List.cons_append,List.nil_append,List.append_assoc]
  | app stamp fn arg =>
    apply Or.inl
    change ((beta.concat alpha.over).concat stamp).letters=_
    simp only [LTerm.label,Label.letters_concat,Label.over,Label.letters,
      List.cons_append,List.nil_append,List.append_assoc]

theorem BetaIncomingReadingOrigin.directed_label_decomposition
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (origin : BetaIncomingReadingOrigin body argument site edge middle oldMiddle first last)
    (reading : PrerequisiteReadsDirected target middle edge forward)
    (lookup : target.subterm edge=some current) :
    ∃ firstNode lastNode marker,
      source.subterm first=some firstNode ∧source.subterm last=some lastNode ∧
      marker.MarksDegree alpha ∧
      ExactDirectedReadingFormula source site alpha forward firstNode lastNode marker current := by
  cases origin with
  | resultFunction result function =>
    have direction : forward=true := by
      cases forward with
      | true => rfl
      | false => exact False.elim (no_self_function middle ((by simpa only [PrerequisiteReadsDirected,Bool.false_eq_true,if_false] using reading.2 : edge=middle).symm.trans (result.trans function)))
    subst forward
    have same : current=LTerm.contract beta alpha body argument :=
      Option.some.inj (lookup.symm.trans (result ▸ step.contract_lookup redex))
    have bodyLookup : source.subterm (site++[.fn,.body])=some body := by
      rw [LTerm.subterm_append,redex];cases body <;> rfl
    refine ⟨.app beta (.lam alpha body) argument,body,.over alpha,redex,bodyLookup,Or.inl rfl,?_⟩
    change ExactDirectedReadingFormula source site alpha true
      (.app beta (.lam alpha body) argument) body (.over alpha) current
    obtain normal | ⟨stamp,equal,overlap⟩ := contract_root_word beta alpha body argument
    · exact Or.inl (by simpa only [same,Label.readLetters,if_true,LTerm.label] using normal)
    · refine Or.inr (Or.inl ⟨rfl,rfl,argument,?_,?_⟩)
      · rw [LTerm.subterm_append,redex];cases argument <;> rfl
      · simpa only [same,Label.readLetters,if_true,LTerm.label] using overlap
  | @resultLambda stamp inner result atMiddle oldLambda =>
    subst body
    have direction : forward=false := by
      cases forward with
      | false => rfl
      | true => exact False.elim (no_self_function middle ((result.trans atMiddle.symm).symm.trans reading.2))
    subst forward
    have same : current=LTerm.contract beta alpha (.lam stamp inner) argument :=
      Option.some.inj (lookup.symm.trans (result ▸ step.contract_lookup redex))
    have labelEq : current.label=(beta.concat alpha.over).concat stamp := by rw [same];rfl
    refine ⟨.lam stamp inner,.app beta (.lam alpha (.lam stamp inner)) argument,
      .over alpha,?_,redex,Or.inl rfl,Or.inl ?_⟩
    · rw [LTerm.subterm_append,redex];rfl
    · change current.label.letters.reverse=stamp.letters.reverse++(.over alpha)::beta.letters.reverse
      rw [labelEq]
      simp only [Label.letters_concat,Label.over,Label.letters,List.reverse_append,List.reverse_cons,List.nil_append,List.cons_append,List.append_assoc]
  | @copyFunction parent occurs copy atMiddle =>
    have function : edge=middle++[.fn] := by simpa only [atMiddle,List.append_assoc] using copy
    have direction : forward=true := by
      cases forward with
      | true => rfl
      | false => exact False.elim (no_self_function middle (reading.2.symm.trans function))
    subst forward
    have localLookup : (LTerm.contract beta alpha body argument).subterm (parent++[.fn])=some current := by
      rw [copy,LTerm.subterm_append,step.contract_lookup redex,Option.bind_some] at lookup;exact lookup
    obtain ⟨stamp,oldLookup,labelEq⟩ := LTerm.contract_argument_incoming_label occurs localLookup
    have nonroot : parent++[.fn]≠[] := by simp
    rw [if_neg nonroot] at labelEq
    refine ⟨.var stamp (binderDepth (parent++[.fn])),argument,.under alpha,?_,?_,Or.inr rfl,Or.inl ?_⟩
    · rw [List.append_assoc,LTerm.subterm_append,redex]
      simpa only [LTerm.subterm,Option.bind_some] using oldLookup
    · rw [LTerm.subterm_append,redex];cases argument <;> rfl
    · change current.label.letters=stamp.letters++(.under alpha)::argument.label.letters
      rw [labelEq]
      simp only [Label.letters_concat,Label.under,Label.letters,List.cons_append,List.nil_append]
  | @copyLambda q stamp inner occurs copy atMiddle oldLambda =>
    subst argument
    have direction : forward=false := by
      cases forward with
      | false => rfl
      | true => exact False.elim (no_self_function middle (atMiddle.trans reading.2))
    subst forward
    have localLookup : (LTerm.contract beta alpha body (.lam stamp inner)).subterm q=some current := by
      rw [copy,LTerm.subterm_append,step.contract_lookup redex,Option.bind_some] at lookup;exact lookup
    obtain ⟨variableStamp,oldLookup,labelEq⟩ := LTerm.contract_argument_incoming_label occurs localLookup
    have firstLookup : source.subterm (site++[.arg])=some (.lam stamp inner) := by rw [LTerm.subterm_append,redex];rfl
    have lastLookup : source.subterm ((site++[.fn,.body])++q)=some (.var variableStamp (binderDepth q)) := by
      rw [List.append_assoc,LTerm.subterm_append,redex]
      simpa only [LTerm.subterm,Option.bind_some] using oldLookup
    by_cases root : q=[]
    · rw [if_pos root] at labelEq
      refine ⟨.lam stamp inner,.var variableStamp (binderDepth q),.under alpha,
        firstLookup,lastLookup,Or.inr rfl,Or.inr (Or.inr ⟨rfl,rfl,
          .app beta (.lam alpha body) (.lam stamp inner),redex,?_⟩)⟩
      change current.label.letters.reverse=stamp.letters.reverse++(.under alpha)::(variableStamp.letters.reverse++(.over alpha)::beta.letters.reverse)
      rw [labelEq]
      simp only [LTerm.label,Label.letters_concat,Label.over,Label.under,
        Label.letters,List.reverse_append,List.reverse_cons,
        List.append_assoc,List.nil_append,List.cons_append]
    · rw [if_neg root] at labelEq
      refine ⟨.lam stamp inner,.var variableStamp (binderDepth q),.under alpha,
        firstLookup,lastLookup,Or.inr rfl,Or.inl ?_⟩
      change current.label.letters.reverse=stamp.letters.reverse++(.under alpha)::variableStamp.letters.reverse
      rw [labelEq]
      simp only [LTerm.label,Label.letters_concat,Label.under,Label.letters,
        List.reverse_append,List.reverse_cons,List.nil_append,List.cons_append,List.append_assoc]
end Lamping.Lambda.Labelled
