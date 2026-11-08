import Lamping.Lambda.DirectedReadingDecomposition
namespace Lamping.Lambda.Labelled

/-- Result versus substitution is determined by THIS origin's literal FIRST
coordinate. It never identifies coordinates from equal labels. -/
def originMarker (site first : Path) (alpha : Label) : Letter :=
  if first=site ∨first=site++[.fn,.body] then .over alpha else .under alpha

private theorem origin_no_self_function (p : Path) : p≠p++[.fn] := by
  intro equal
  have sizes := congrArg List.length equal
  simp only [List.length_append,List.length_cons,List.length_nil] at sizes
  omega

private theorem copy_function_marker (site parent : Path) (alpha : Label) :
    originMarker site ((site++[.fn,.body])++(parent++[.fn])) alpha=.under alpha := by
  have notSite : (site++[.fn,.body])++(parent++[.fn])≠site := by
    intro equal
    have sizes := congrArg List.length equal
    simp only [List.length_append,List.length_cons,List.length_nil] at sizes
    omega
  have notBody : (site++[.fn,.body])++(parent++[.fn])≠site++[.fn,.body] := by
    intro equal
    have sizes := congrArg List.length equal
    simp only [List.length_append,List.length_cons,List.length_nil] at sizes
    omega
  exact if_neg (by rintro (a|a);exact notSite a;exact notBody a)

private theorem copy_lambda_marker (site : Path) (alpha : Label) :
    originMarker site (site++[.arg]) alpha=.under alpha := by
  have notSite : site++[.arg]≠site := by
    intro equal
    have sizes := congrArg List.length equal
    simp only [List.length_append,List.length_cons,List.length_nil] at sizes
    omega
  have notBody : site++[.arg]≠site++[.fn,.body] := by
    intro equal
    have sizes := congrArg List.length equal
    simp only [List.length_append,List.length_cons,List.length_nil] at sizes
    omega
  exact if_neg (by rintro (a|a);exact notSite a;exact notBody a)

/-- Strengthen the actual operational prefix derivation with its exact
origin-selected marker. In particular the copied q=[] overlap is retained. -/
theorem BetaIncomingReadingOrigin.directed_label_prefix_kind
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (origin : BetaIncomingReadingOrigin body argument site edge middle oldMiddle first last)
    (reading : PrerequisiteReadsDirected target middle edge forward)
    (lookup : target.subterm edge=some current) :
    ∃ firstNode lastNode marker rest,
      source.subterm first=some firstNode ∧source.subterm last=some lastNode ∧
      marker.MarksDegree alpha ∧marker=originMarker site first alpha ∧
      current.label.readLetters forward=firstNode.label.readLetters forward++marker::rest := by
  cases origin with
  | resultFunction result function =>
    have direction : forward=true := by
      cases forward with
      | true => rfl
      | false => exact False.elim (origin_no_self_function middle ((by simpa only [PrerequisiteReadsDirected,Bool.false_eq_true,if_false] using reading.2 : edge=middle).symm.trans (result.trans function)))
    subst forward
    have same : current=LTerm.contract beta alpha body argument :=
      Option.some.inj (lookup.symm.trans (result ▸ step.contract_lookup redex))
    refine ⟨.app beta (.lam alpha body) argument,body,.over alpha,
      (body.subst (LTerm.single (argument.prepend alpha.under))).label.letters,redex,?_,Or.inl rfl,(by simp [originMarker]),?_⟩
    · rw [LTerm.subterm_append,redex];cases body <;> rfl
    · change current.label.letters=beta.letters++(.over alpha)::(body.subst (LTerm.single (argument.prepend alpha.under))).label.letters
      rw [same,LTerm.contract,label_prepend]
      simp only [Label.letters_concat,Label.over,Label.letters,List.cons_append,List.nil_append,List.append_assoc]
  | @resultLambda stamp inner result atMiddle oldLambda =>
    subst body
    have direction : forward=false := by
      cases forward with
      | false => rfl
      | true => exact False.elim (origin_no_self_function middle ((result.trans atMiddle.symm).symm.trans reading.2))
    subst forward
    have same : current=LTerm.contract beta alpha (.lam stamp inner) argument :=
      Option.some.inj (lookup.symm.trans (result ▸ step.contract_lookup redex))
    have labelEq : current.label=(beta.concat alpha.over).concat stamp := by rw [same];rfl
    refine ⟨.lam stamp inner,.app beta (.lam alpha (.lam stamp inner)) argument,
      .over alpha,beta.letters.reverse,?_,redex,Or.inl rfl,(by simp [originMarker]),?_⟩
    · rw [LTerm.subterm_append,redex];rfl
    · change current.label.letters.reverse=stamp.letters.reverse++(.over alpha)::beta.letters.reverse
      rw [labelEq]
      simp only [Label.letters_concat,Label.over,Label.letters,List.reverse_append,List.reverse_cons,List.nil_append,List.cons_append,List.append_assoc]
  | @copyFunction parent occurs copy atMiddle =>
    have function : edge=middle++[.fn] := by simpa only [atMiddle,List.append_assoc] using copy
    have direction : forward=true := by
      cases forward with
      | true => rfl
      | false => exact False.elim (origin_no_self_function middle (reading.2.symm.trans function))
    subst forward
    have localLookup : (LTerm.contract beta alpha body argument).subterm (parent++[.fn])=some current := by
      rw [copy,LTerm.subterm_append,step.contract_lookup redex,Option.bind_some] at lookup;exact lookup
    obtain ⟨stamp,oldLookup,labelEq⟩ := LTerm.contract_argument_incoming_label occurs localLookup
    have nonroot : parent++[.fn]≠[] := by simp
    rw [if_neg nonroot] at labelEq
    refine ⟨.var stamp (binderDepth (parent++[.fn])),argument,.under alpha,argument.label.letters,?_,?_,Or.inr rfl,(copy_function_marker site parent alpha).symm,?_⟩
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
      | true => exact False.elim (origin_no_self_function middle (atMiddle.trans reading.2))
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
        variableStamp.letters.reverse++(.over alpha)::beta.letters.reverse,firstLookup,lastLookup,Or.inr rfl,(copy_lambda_marker site alpha).symm,?_⟩
      change current.label.letters.reverse=stamp.letters.reverse++(.under alpha)::(variableStamp.letters.reverse++(.over alpha)::beta.letters.reverse)
      rw [labelEq]
      simp only [LTerm.label,Label.letters_concat,Label.over,Label.under,
        Label.letters,List.reverse_append,List.reverse_cons,
        List.append_assoc,List.nil_append,List.cons_append]
    · rw [if_neg root] at labelEq
      refine ⟨.lam stamp inner,.var variableStamp (binderDepth q),.under alpha,
        variableStamp.letters.reverse,firstLookup,lastLookup,Or.inr rfl,(copy_lambda_marker site alpha).symm,?_⟩
      change current.label.letters.reverse=stamp.letters.reverse++(.under alpha)::variableStamp.letters.reverse
      rw [labelEq]
      simp only [LTerm.label,Label.letters_concat,Label.under,Label.letters,
        List.reverse_append,List.reverse_cons,List.nil_append,List.cons_append,List.append_assoc]
/-- On the SAME actual event, the complete formula's marker is forced by
its actual FIRST lookup and origin. Only an IDENTICAL literal FIRST prefix
is canceled; no LAST label or unknown continuation is canceled. -/
theorem BetaIncomingReadingOrigin.formula_marker
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (origin : BetaIncomingReadingOrigin body argument site edge reader oldReader first last)
    (reading : PrerequisiteReadsDirected target reader edge forward)
    (lookup : target.subterm edge=some current)
    (firstLookup : source.subterm first=some firstNode)
    (formula : ExactDirectedReadingFormula source site alpha forward firstNode lastNode marker current) :
    marker=originMarker site first alpha := by
  obtain ⟨actualFirst,_actualLast,known,rest,atFirst,_atLast,_marks,kind,equation⟩ :=
    origin.directed_label_prefix_kind step redex reading lookup
  have sameFirst : actualFirst=firstNode := Option.some.inj (atFirst.symm.trans firstLookup)
  subst actualFirst
  have arbitrary : ∃ tail,current.label.readLetters forward=firstNode.label.readLetters forward++marker::tail := by
    rcases formula with ordinary | resultOverlap | copyOverlap
    · exact ⟨_,ordinary⟩
    · obtain ⟨_direction,_kind,_argument,_lookup,eq⟩ := resultOverlap
      exact ⟨_,eq⟩
    · obtain ⟨_direction,_kind,_app,_lookup,eq⟩ := copyOverlap
      exact ⟨_,eq⟩
  obtain ⟨_tail,other⟩ := arbitrary
  have heads := List.cons.inj (List.append_cancel_left (equation.symm.trans other))
  exact heads.1.symm.trans kind

#print axioms BetaIncomingReadingOrigin.directed_label_prefix_kind
#print axioms BetaIncomingReadingOrigin.formula_marker
end Lamping.Lambda.Labelled
