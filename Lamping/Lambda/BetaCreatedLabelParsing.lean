import Lamping.Lambda.LabelCreatedClassification
namespace Lamping.Lambda.Labelled

private theorem StepAt.strict_copy_incoming_data
    {source target body argument current : LTerm} {site edge copySite : Path} {beta alpha : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (occurs : ArgumentOccurrence body.erase copySite) (nonroot : copySite≠[])
    (edgeEq : edge=site++copySite) (lookup : target.subterm edge=some current) :
    ∃ stamp,body.subterm copySite=some (.var stamp (binderDepth copySite)) ∧
      current.label=stamp.concat (alpha.under.concat argument.label) := by
  have localLookup : (LTerm.contract beta alpha body argument).subterm copySite=some current := by
    rw [edgeEq,LTerm.subterm_append,step.contract_lookup redex,Option.bind_some] at lookup
    exact lookup
  obtain ⟨stamp,oldLookup,labels⟩ := LTerm.contract_argument_incoming_label occurs localLookup
  exact ⟨stamp,oldLookup,by simpa only [if_neg nonroot] using labels⟩

private theorem copy_stamp_safe
    {source body argument : LTerm} {site copySite : Path} {beta alpha stamp : Label}
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (sourceSafe : source.OuterBarsSafe (fun payload=>payload≠alpha))
    (lookup : body.subterm copySite=some (.var stamp (binderDepth copySite))) :
    stamp.OuterBarsSafe (fun payload=>payload≠alpha) := by
  have atOld : source.subterm ((site++[.fn,.body])++copySite)=some (.var stamp (binderDepth copySite)) := by
    simp only [LTerm.subterm_append,redex,Option.bind_some,LTerm.subterm,lookup]
  exact (LTerm.outerBarsSafe_iff _ _).mp sourceSafe _ (LTerm.label_mem_of_subterm atOld)

/-- The first fresh marker separates the result edge from strict copy
roots. The actual copy at [] is deliberately excluded: it may coincide with
the result and contain both over and under markers. -/
theorem StepAt.result_ne_strict_copy_label
    {source target body argument result copy : LTerm} {site copySite : Path} {beta alpha : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (sourceSafe : source.OuterBarsSafe (fun payload=>payload≠alpha))
    (resultLookup : target.subterm site=some result)
    (occurs : ArgumentOccurrence body.erase copySite) (nonroot : copySite≠[])
    (copyLookup : target.subterm (site++copySite)=some copy) : result.label≠copy.label := by
  obtain ⟨stamp,oldLookup,copyLabel⟩ := step.strict_copy_incoming_data redex occurs nonroot rfl copyLookup
  have resultEq : result=LTerm.contract beta alpha body argument :=
    Option.some.inj (resultLookup.symm.trans (step.contract_lookup redex))
  have betaSafe := (LTerm.outerBarsSafe_iff _ _).mp sourceSafe _ (LTerm.label_mem_of_subterm redex)
  have stampSafe := copy_stamp_safe redex sourceSafe oldLookup
  intro same
  rw [resultEq,LTerm.contract,label_prepend,Label.concat_assoc,copyLabel] at same
  have marker := (Label.fresh_marker_split_unique betaSafe stampSafe
    (Or.inl rfl : Letter.MarksDegree alpha (.over alpha))
    (Or.inr rfl : Letter.MarksDegree alpha (.under alpha)) same).2.1
  cases marker

/-- Equal strict-copy incoming labels recover equal actual old variable
stamps. They need not determine the syntax positions, which can be distinct
copies with repeated labels in a non-INIT current source. -/
theorem StepAt.strict_copy_equal_labels
    {source target body argument left right : LTerm} {site leftSite rightSite : Path} {beta alpha : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (sourceSafe : source.OuterBarsSafe (fun payload=>payload≠alpha))
    (leftOccurs : ArgumentOccurrence body.erase leftSite) (leftNonroot : leftSite≠[])
    (rightOccurs : ArgumentOccurrence body.erase rightSite) (rightNonroot : rightSite≠[])
    (leftAt : target.subterm (site++leftSite)=some left)
    (rightAt : target.subterm (site++rightSite)=some right)
    (same : left.label=right.label) :
    ∃ stamp,body.subterm leftSite=some (.var stamp (binderDepth leftSite)) ∧
      body.subterm rightSite=some (.var stamp (binderDepth rightSite)) := by
  obtain ⟨leftStamp,oldLeft,leftLabel⟩ := step.strict_copy_incoming_data redex leftOccurs leftNonroot rfl leftAt
  obtain ⟨rightStamp,oldRight,rightLabel⟩ := step.strict_copy_incoming_data redex rightOccurs rightNonroot rfl rightAt
  rw [leftLabel,rightLabel] at same
  have stamps := (Label.fresh_marker_split_unique
    (copy_stamp_safe redex sourceSafe oldLeft) (copy_stamp_safe redex sourceSafe oldRight)
    (Or.inr rfl : Letter.MarksDegree alpha (.under alpha))
    (Or.inr rfl : Letter.MarksDegree alpha (.under alpha)) same).1
  exact ⟨leftStamp,oldLeft,stamps ▸ oldRight⟩

end Lamping.Lambda.Labelled
