import Lamping.Lambda.ResidualFunctionPreimages
import Lamping.Lambda.UniformReadingCreationTrace
namespace Lamping.Lambda.Labelled
/-- Read a label in the actual FUNCTION or lambda CONTEXT direction. -/
def Label.readLetters (forward : Bool) (label : Label) : List Letter :=
  if forward then label.letters else label.letters.reverse
/-- The orientation comes from the actual syntax reading, not its label. -/
def PrerequisiteReadsDirected (t : LTerm) (middle edge : Path) (forward : Bool) : Prop :=
  PrerequisiteReads t middle edge ∧if forward then edge=middle++[.fn] else edge=middle
private theorem no_self_function (p : Path) : p≠p++[.fn] := by
  intro same
  have lengths := congrArg List.length same
  simp only [List.length_append,List.length_cons,List.length_nil] at lengths
  omega
/-- A created reading peels from the old first endpoint on the ACTUAL
reading side. The remainder may still contain markers. -/
theorem BetaIncomingReadingOrigin.directed_label_prefix
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (origin : BetaIncomingReadingOrigin body argument site edge middle oldMiddle first last)
    (reading : PrerequisiteReadsDirected target middle edge forward)
    (lookup : target.subterm edge=some current) :
    ∃ firstNode lastNode marker rest,
      source.subterm first=some firstNode ∧source.subterm last=some lastNode ∧
      marker.MarksDegree alpha ∧
      current.label.readLetters forward=firstNode.label.readLetters forward++marker::rest := by
  cases origin with
  | resultFunction result function =>
    have direction : forward=true := by
      cases forward with
      | true => rfl
      | false => exact False.elim (no_self_function middle ((by simpa only [PrerequisiteReadsDirected,Bool.false_eq_true,if_false] using reading.2 : edge=middle).symm.trans (result.trans function)))
    subst forward
    have same : current=LTerm.contract beta alpha body argument :=
      Option.some.inj (lookup.symm.trans (result ▸ step.contract_lookup redex))
    refine ⟨.app beta (.lam alpha body) argument,body,.over alpha,
      (body.subst (LTerm.single (argument.prepend alpha.under))).label.letters,redex,?_,Or.inl rfl,?_⟩
    · rw [LTerm.subterm_append,redex];cases body <;> rfl
    · change current.label.letters=beta.letters++(.over alpha)::(body.subst (LTerm.single (argument.prepend alpha.under))).label.letters
      rw [same,LTerm.contract,label_prepend]
      simp only [Label.letters_concat,Label.over,Label.letters,List.cons_append,List.nil_append,List.append_assoc]
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
      .over alpha,beta.letters.reverse,?_,redex,Or.inl rfl,?_⟩
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
    refine ⟨.var stamp (binderDepth (parent++[.fn])),argument,.under alpha,argument.label.letters,?_,?_,Or.inr rfl,?_⟩
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
        variableStamp.letters.reverse++(.over alpha)::beta.letters.reverse,firstLookup,lastLookup,Or.inr rfl,?_⟩
      change current.label.letters.reverse=stamp.letters.reverse++(.under alpha)::(variableStamp.letters.reverse++(.over alpha)::beta.letters.reverse)
      rw [labelEq]
      simp only [LTerm.label,Label.letters_concat,Label.over,Label.under,
        Label.letters,List.reverse_append,List.reverse_cons,
        List.append_assoc,List.nil_append,List.cons_append]
    · rw [if_neg root] at labelEq
      refine ⟨.lam stamp inner,.var variableStamp (binderDepth q),.under alpha,
        variableStamp.letters.reverse,firstLookup,lastLookup,Or.inr rfl,?_⟩
      change current.label.letters.reverse=stamp.letters.reverse++(.under alpha)::variableStamp.letters.reverse
      rw [labelEq]
      simp only [LTerm.label,Label.letters_concat,Label.under,Label.letters,
        List.reverse_append,List.reverse_cons,List.nil_append,List.cons_append,List.append_assoc]
end Lamping.Lambda.Labelled
namespace Lamping.Lambda.Labelled
/-- Cutting the real old two-edge chain allows zero-edge binder jumps;
no successful chain at its other endpoint is assumed. -/
theorem BetaIncomingReadingOrigin.old_directed_reading {source target : LTerm}
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (origin : BetaIncomingReadingOrigin body argument site edge middle oldMiddle first last)
    (reading : PrerequisiteReadsDirected target middle edge forward) :
    ∃ reader,PrerequisitePrefix source oldMiddle [] reader ∧
      PrerequisiteReadsDirected source reader first forward := by
  obtain ⟨chain,_⟩ := origin.old_prerequisite redex
  obtain ⟨before,after,reader,split,segment,_,oldReads⟩ := chain.split_at_member (List.mem_cons_self)
  have firstSplit : [first,site++[.fn]]=[]++(first::[site++[.fn]]) := rfl
  obtain ⟨empty,_⟩ := chain.first_created_split_unique firstSplit split
  subst before
  refine ⟨reader,segment,oldReads,?_⟩
  cases forward with
  | true =>
    cases origin with
    | resultFunction result function =>
      rcases oldReads with ⟨appStamp,fn,arg,atApp,equal⟩ | ⟨stamp,inner,atLambda,equal⟩
      · exact equal
      · have impossible : source.subterm site=some (.lam stamp inner) := equal ▸ atLambda
        rw [redex] at impossible;cases impossible
    | @copyFunction parent occurs copy atMiddle =>
      rcases oldReads with ⟨appStamp,fn,arg,atApp,equal⟩ | ⟨stamp,inner,atLambda,equal⟩
      · exact equal
      · rw [←equal,List.append_assoc,LTerm.subterm_append,redex] at atLambda
        have localLookup : body.subterm (parent++[.fn])=some (.lam stamp inner) := by simpa only [LTerm.subterm,Option.bind_some] using atLambda
        change subtermAt body.erase _=some (.var _) at occurs
        rw [←LTerm.erase_subterm,localLookup] at occurs;cases occurs
    | resultLambda result atMiddle _ =>
      exact False.elim (no_self_function middle ((result.trans atMiddle.symm).symm.trans reading.2))
    | copyLambda _ _ atMiddle _ =>
      exact False.elim (no_self_function middle (atMiddle.trans reading.2))
  | false =>
    cases origin with
    | resultFunction result function =>
      exact False.elim (no_self_function middle (reading.2.symm.trans (result.trans function)))
    | @copyFunction parent occurs copy atMiddle =>
      have function : edge=middle++[.fn] := by simpa only [atMiddle,List.append_assoc] using copy
      exact False.elim (no_self_function middle (reading.2.symm.trans function))
    | resultLambda result atMiddle _ =>
      rcases oldReads with ⟨stamp,fn,arg,atApp,equal⟩ | ⟨stamp,inner,atLambda,equal⟩
      · have reversed := congrArg List.reverse equal
        simp only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append] at reversed
        cases (List.cons.inj reversed).1
      · exact equal
    | copyLambda _ _ atMiddle _ =>
      rcases oldReads with ⟨stamp,fn,arg,atApp,equal⟩ | ⟨stamp,inner,atLambda,equal⟩
      · have reversed := congrArg List.reverse equal
        simp only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append] at reversed
        cases (List.cons.inj reversed).1
      · exact equal
end Lamping.Lambda.Labelled
