import Lamping.Lambda.PrerequisiteChainOrigins
import Lamping.Lambda.LabelCopyInteriors
import Lamping.Lambda.LabelContextualRegions
namespace Lamping.Lambda.Labelled.LTerm
private theorem lift_value_label
    (labels : ∀ i value,sigma i=.put value → value.label=word) :
    ∀ i value,lift sigma i=.put value → value.label=word := by
  intro i value put
  cases i with
  | zero => cases put
  | succ i =>
    cases hs : sigma i with
    | keep j => simp only [lift,hs] at put; cases put
    | put old =>
      have equal : old.rename Nat.succ=value := by simpa only [lift,hs,SubValue.put.injEq] using put
      rw [←equal,rename_label]
      exact labels i old hs

theorem InsertedCopy.incoming_label (inserted : InsertedCopy sigma t site copy)
    (labels : ∀ i value,sigma i=.put value → value.label=word) :
    ∃ stamp index,t.subterm site=some (.var stamp index) ∧ copy.label=stamp.concat word := by
  induction inserted with
  | @here sigma stamp index value put =>
    refine ⟨stamp,index,rfl,?_⟩
    have prefixed : (value.prepend stamp).label=stamp.concat value.label := by cases value <;> rfl
    rw [prefixed,labels index value put]
  | fn inserted ih =>
    obtain ⟨stamp,index,atOld,equal⟩ := ih labels
    exact ⟨stamp,index,atOld,equal⟩
  | arg inserted ih =>
    obtain ⟨stamp,index,atOld,equal⟩ := ih labels
    exact ⟨stamp,index,atOld,equal⟩
  | body inserted ih =>
    obtain ⟨stamp,index,atOld,equal⟩ := ih (lift_value_label labels)
    exact ⟨stamp,index,atOld,equal⟩
end Lamping.Lambda.Labelled.LTerm


namespace Lamping.Lambda.Labelled.LTerm
/-- Exact incoming label of an actual beta argument-copy root. The extra
result prefix is present precisely when the insertion is itself the root. -/
theorem contract_argument_incoming_label {body argument copy : LTerm}
    (occurs : ArgumentOccurrence body.erase site)
    (lookup : (contract beta alpha body argument).subterm site=some copy) :
    ∃ stamp,body.subterm site=some (.var stamp (binderDepth site)) ∧
      copy.label=if site=[] then
        (beta.concat alpha.over).concat (stamp.concat (alpha.under.concat argument.label))
      else stamp.concat (alpha.under.concat argument.label) := by
  obtain ⟨inserted,atInserted⟩ := insertedCopy_of_variable_site body (depth := 0)
    (sigma := single (argument.prepend alpha.under))
    (by simpa only [Nat.zero_add] using occurs) rfl
  have labels : ∀ i value,single (argument.prepend alpha.under) i=.put value →
      value.label=alpha.under.concat argument.label := by
    intro i value put
    cases i with
    | zero =>
      have same : argument.prepend alpha.under=value := SubValue.put.inj put
      rw [←same]
      cases argument <;> rfl
    | succ i => cases put
  obtain ⟨stamp,index,atOld,sameLabel⟩ := atInserted.incoming_label labels
  have atBare := occurs
  change subtermAt body.erase site=some (.var (binderDepth site)) at atBare
  rw [←erase_subterm,atOld] at atBare
  have depthEq : index=binderDepth site := by
    simpa only [Option.map_some,erase,Option.some.injEq,Term.var.injEq] using atBare
  subst index
  refine ⟨stamp,atOld,?_⟩
  by_cases root : site=[]
  · subst site
    have sourceEq : body.subst (single (argument.prepend alpha.under))=inserted := by
      simpa only [subterm,Option.some.injEq] using atInserted.lookup
    have copyEq : inserted.prepend (beta.concat alpha.over)=copy := by
      simpa only [contract,subterm,sourceEq,Option.some.injEq] using lookup
    rw [if_pos rfl,←copyEq]
    have prefixed : (inserted.prepend (beta.concat alpha.over)).label=
        (beta.concat alpha.over).concat inserted.label := by cases inserted <;> rfl
    rw [prefixed,sameLabel]
  · have copyEq : inserted=copy := by
      rw [contract,prepend_subterm_nonempty _ _ root] at lookup
      exact Option.some.inj (atInserted.lookup.symm.trans lookup)
    rw [if_neg root,←copyEq,sameLabel]
end Lamping.Lambda.Labelled.LTerm
namespace Lamping.Lambda.Labelled.LTerm
/-- A lambda on the result edge is either a retained body-root lambda, or
one actual root argument insertion (the result/substitution overlap). -/
theorem contract_root_lambda_origin
    (shape : contract beta alpha body argument=.lam currentStamp currentBody) :
    (∃ oldStamp oldBody,body=.lam oldStamp oldBody ∧
      currentStamp=(beta.concat alpha.over).concat oldStamp) ∨
    (∃ variableStamp argumentStamp argumentBody,
      body=.var variableStamp 0 ∧ argument=.lam argumentStamp argumentBody ∧
      currentStamp=(beta.concat alpha.over).concat
        (variableStamp.concat (alpha.under.concat argumentStamp))) := by
  cases body with
  | app stamp fn arg => cases shape
  | lam stamp oldBody =>
    exact .inl ⟨stamp,oldBody,rfl,(LTerm.lam.inj shape).1.symm⟩
  | var stamp index =>
    cases index with
    | succ index => cases shape
    | zero =>
      cases argument with
      | var => cases shape
      | app => cases shape
      | lam argumentStamp argumentBody =>
        right
        refine ⟨stamp,argumentStamp,argumentBody,rfl,rfl,?_⟩
        have same := (LTerm.lam.inj shape).1.symm
        simpa only [contract,subst,single,prepend,Label.concat_assoc] using same
end Lamping.Lambda.Labelled.LTerm
namespace Lamping.Lambda.Labelled
/-- The actual result lambda supplies its old eligible first edge and the
old two-edge prerequisite chain, including root-copy overlap. -/
theorem StepAt.result_lambda_old_chain {source target body argument currentBody : LTerm}
    {site : Path} {beta alpha currentStamp : Label} (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (atResult : target.subterm site=some (.lam currentStamp currentBody)) :
    ∃ first,(first=site++[.fn,.body] ∨ first=site++[.arg]) ∧
      PrerequisiteChain source first [first,site++[.fn]] := by
  have shape : LTerm.contract beta alpha body argument=.lam currentStamp currentBody :=
    Option.some.inj ((step.contract_lookup redex).symm.trans atResult)
  rcases LTerm.contract_root_lambda_origin shape with ⟨oldStamp,oldBody,bodyEq,_⟩ |
      ⟨variableStamp,argumentStamp,argumentBody,bodyEq,argumentEq,_⟩
  · subst body
    exact ⟨site++[.fn,.body],Or.inl rfl,result_lambda_prerequisite redex⟩
  · subst argument
    exact ⟨site++[.arg],Or.inr rfl,copied_lambda_prerequisite redex⟩
end Lamping.Lambda.Labelled

