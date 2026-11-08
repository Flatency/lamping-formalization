import Lamping.Lambda.UncreatedPrerequisiteTransitions
import Lamping.Lambda.FunctionResultPrefixTransport

namespace Lamping.Lambda.Labelled
/-- Only the syntax constructor, independent of labels, children and indices. -/
def LTerm.constructorTag : LTerm →Nat
  | .var _ _ => 0
  | .lam _ _ => 1
  | .app _ _ _ => 2
private theorem constructorTag_rename (t : LTerm) (rho) : (t.rename rho).constructorTag=t.constructorTag := by
  cases t <;> rfl
private theorem constructorTag_prepend (t : LTerm) (word) : (t.prepend word).constructorTag=t.constructorTag := by
  cases t <;> rfl
private theorem LTerm.CopyInterior.constructor_lookup
    (copied : LTerm.CopyInterior original copy)
    (oldLookup : original.subterm p=some old) (currentLookup : copy.subterm p=some current) :
    old.constructorTag=current.constructorTag := by
  obtain ⟨rho,word,equal⟩ := copied
  cases p with
  | nil =>
    have atOld : original=old := by simpa only [LTerm.subterm,Option.some.injEq] using oldLookup
    subst original
    rw [equal] at currentLookup
    have currentEq : (old.rename rho).prepend word=current := by simpa only [LTerm.subterm,Option.some.injEq] using currentLookup
    rw [←currentEq,constructorTag_prepend,constructorTag_rename]
  | cons child rest =>
    rw [equal,LTerm.prepend_subterm_nonempty _ _ (by simp)] at currentLookup
    obtain ⟨tau,renamed⟩ := LTerm.subterm_rename original rho (child::rest)
    rw [renamed,oldLookup,Option.map_some] at currentLookup
    have currentEq : old.rename tau=current := Option.some.inj currentLookup
    rw [←currentEq,constructorTag_rename]

private theorem retained_constructor_lookup
    {body argument old current : LTerm} {relative : Path} {beta alpha : Label}
    (oldLookup : body.subterm relative=some old)
    (nonselected : ∀ stamp,old≠.var stamp (binderDepth relative))
    (currentLookup : (LTerm.contract beta alpha body argument).subterm relative=some current) :
    old.constructorTag=current.constructorTag := by
  have oldBare : subtermAt body.erase relative=some old.erase := by rw [←LTerm.erase_subterm,oldLookup]; rfl
  have currentBare : subtermAt (Lambda.contract body.erase argument.erase) relative=some current.erase := by
    rw [←LTerm.erase_contract,←LTerm.erase_subterm,currentLookup]; rfl
  have forward := subtermAt_subst oldBare (singleSub argument.erase)
  have shape := Option.some.inj (forward.symm.trans currentBare)
  cases old with
  | app stamp fn arg =>
    cases current with
    | app => rfl
    | var => cases shape
    | lam => cases shape
  | lam stamp body =>
    cases current with
    | lam => rfl
    | var => cases shape
    | app => cases shape
  | var stamp index =>
    have other : index≠binderDepth relative := by intro equal; exact nonselected stamp (by rw [equal])
    obtain ⟨j,keep⟩ := liftSingle_other (binderDepth relative) index argument.erase other
    simp only [LTerm.erase,Lambda.subst,keep] at shape
    cases current <;> cases shape
    rfl
end Lamping.Lambda.Labelled
namespace Lamping.Lambda.Labelled
/-- The actual occurrence preimage has a real old lookup of the same syntax
constructor, even when its incoming label acquired beta prefixes. -/
theorem StepAt.preimage_node_constructor
    {source target body argument current : LTerm} {site p oldPosition : Path} {beta alpha : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (origin : BetaNodePreimage body argument site p oldPosition)
    (lookup : target.subterm p=some current) :
    ∃ old,source.subterm oldPosition=some old ∧old.constructorTag=current.constructorTag := by
  rcases origin.coordinates with ⟨equal,outside⟩ |
      ⟨relative,old,atCurrent,atOld,oldLookup,nonselected⟩ |
      ⟨q,relative,old,occurs,atCurrent,atOld,oldLookup⟩
  · rw [←equal]
    cases current with
    | var stamp index => exact ⟨_,step.context_variable_origin lookup outside,rfl⟩
    | lam stamp body =>
      obtain ⟨oldBody,oldLookup⟩ := step.context_lambda_origin lookup outside
      exact ⟨_,oldLookup,rfl⟩
    | app stamp fn arg =>
      obtain ⟨oldFn,oldArg,oldLookup⟩ := step.context_app_origin lookup outside
      exact ⟨_,oldLookup,rfl⟩
  · have localLookup : (LTerm.contract beta alpha body argument).subterm relative=some current := by
      rw [atCurrent,LTerm.subterm_append,step.contract_lookup redex,Option.bind_some] at lookup
      exact lookup
    refine ⟨old,?_,retained_constructor_lookup oldLookup nonselected localLookup⟩
    rw [atOld,List.append_assoc,LTerm.subterm_append,redex]
    simpa only [LTerm.subterm,Option.bind_some] using oldLookup
  · have localLookup : (LTerm.contract beta alpha body argument).subterm (q++relative)=some current := by
      rw [atCurrent,List.append_assoc,LTerm.subterm_append,step.contract_lookup redex,Option.bind_some] at lookup
      exact lookup
    have originalLookup : source.subterm oldPosition=some old := by
      rw [atOld,List.append_assoc,LTerm.subterm_append,redex]
      simpa only [LTerm.subterm,Option.bind_some] using oldLookup
    rw [LTerm.subterm_append] at localLookup
    cases copyLookup : (LTerm.contract beta alpha body argument).subterm q with
    | none => rw [copyLookup] at localLookup; cases localLookup
    | some copy =>
      rw [copyLookup,Option.bind_some] at localLookup
      exact ⟨old,originalLookup,(LTerm.contract_argument_copy_interior occurs copyLookup).constructor_lookup oldLookup localLookup⟩
end Lamping.Lambda.Labelled
namespace Lamping.Lambda.Labelled
private theorem outside_uncreated_child
    {body : LTerm} {site p : Path} {child : Step}
    (outside : ¬∃ relative,p=site++relative)
    (uncreated : ¬BetaCreatedIncoming body site (p++[child])) :
    ¬∃ relative,p++[child]=site++relative := by
  rintro ⟨relative,equal⟩
  rcases List.append_eq_append_iff.mp equal with ⟨extra,siteEq,tailEq⟩ | ⟨extra,pEq,_⟩
  · cases extra with
    | nil => exact outside ⟨[],by simpa only [List.append_nil] using siteEq.symm⟩
    | cons head rest =>
      have tailEmpty : rest++relative=[] := (List.cons.inj tailEq).2.symm
      obtain ⟨restEmpty,relativeEmpty⟩ := List.append_eq_nil_iff.mp tailEmpty
      subst relative
      exact uncreated (Or.inl (by simpa only [List.append_nil] using equal))
  · exact outside ⟨extra,pEq⟩

private theorem preimage_app_child
    {source body argument oldFn oldArg : LTerm} {site p oldPosition : Path}
    {beta alpha stamp : Label}
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (origin : BetaNodePreimage body argument site p oldPosition)
    (oldApp : source.subterm oldPosition=some (.app stamp oldFn oldArg))
    (uncreated : ¬BetaCreatedIncoming body site (p++[.fn])) :
    BetaNodePreimage body argument site (p++[.fn]) (oldPosition++[.fn]) := by
  rcases origin.coordinates with ⟨equal,outside⟩ |
      ⟨relative,old,atCurrent,atOld,oldLookup,nonselected⟩ |
      ⟨q,relative,old,occurs,atCurrent,atOld,oldLookup⟩
  · rw [←equal]
    exact .context (outside_uncreated_child outside uncreated)
  · have atBody : source.subterm ((site++[.fn,.body])++relative)=some old := by
      rw [List.append_assoc,LTerm.subterm_append,redex]
      simpa only [LTerm.subterm,Option.bind_some] using oldLookup
    have same : old=.app stamp oldFn oldArg := Option.some.inj (atBody.symm.trans (atOld ▸ oldApp))
    subst old
    have childLookup : body.subterm (relative++[.fn])=some oldFn := by
      rw [LTerm.subterm_append,oldLookup]; cases oldFn <;> rfl
    have retained : ∀ childStamp,oldFn≠.var childStamp (binderDepth (relative++[.fn])) := by
      intro childStamp equal
      have selected : ArgumentOccurrence body.erase (relative++[.fn]) := by
        change subtermAt body.erase (relative++[.fn])=some (.var (binderDepth (relative++[.fn])))
        rw [←LTerm.erase_subterm,childLookup,equal]; rfl
      apply uncreated
      exact betaCreatedIncoming_iff.mpr (Or.inr ⟨relative++[.fn],selected,by rw [atCurrent,List.append_assoc]⟩)
    simpa only [atCurrent,atOld,List.append_assoc] using
      (BetaNodePreimage.retained (argument := argument) (site := site) childLookup retained)
  · have atArgument : source.subterm ((site++[.arg])++relative)=some old := by
      rw [List.append_assoc,LTerm.subterm_append,redex]
      simpa only [LTerm.subterm,Option.bind_some] using oldLookup
    have same : old=.app stamp oldFn oldArg := Option.some.inj (atArgument.symm.trans (atOld ▸ oldApp))
    subst old
    have childLookup : argument.subterm (relative++[.fn])=some oldFn := by
      rw [LTerm.subterm_append,oldLookup]; cases oldFn <;> rfl
    simpa only [atCurrent,atOld,List.append_assoc] using
      (BetaNodePreimage.copied (site := site) occurs childLookup)

/-- An actual uncreated FUNCTION reading inherits BOTH an old app and its
old function occurrence, with the actual function constructor preserved. -/
theorem StepAt.beta_app_preimages
    {source target body argument fn arg : LTerm} {site p oldPosition : Path}
    {beta alpha stamp : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (origin : BetaNodePreimage body argument site p oldPosition)
    (lookup : target.subterm p=some (.app stamp fn arg))
    (uncreated : ¬BetaCreatedIncoming body site (p++[.fn])) :
    ∃ oldStamp oldFn oldArg,source.subterm oldPosition=some (.app oldStamp oldFn oldArg) ∧
      BetaNodePreimage body argument site (p++[.fn]) (oldPosition++[.fn]) ∧
      oldFn.constructorTag=fn.constructorTag := by
  obtain ⟨old,oldLookup,same⟩ := step.preimage_node_constructor redex origin lookup
  cases old with
  | var => cases same
  | lam => cases same
  | app oldStamp oldFn oldArg =>
    have childOrigin := preimage_app_child redex origin oldLookup uncreated
    have childLookup : target.subterm (p++[.fn])=some fn := by
      rw [LTerm.subterm_append,lookup]; cases fn <;> rfl
    obtain ⟨child,atChild,childTag⟩ := step.preimage_node_constructor redex childOrigin childLookup
    have sourceChild : source.subterm (oldPosition++[.fn])=some oldFn := by
      rw [LTerm.subterm_append,oldLookup]; cases oldFn <;> rfl
    have childEq : child=oldFn := Option.some.inj (atChild.symm.trans sourceChild)
    exact ⟨oldStamp,oldFn,oldArg,oldLookup,childOrigin,childEq ▸ childTag⟩
end Lamping.Lambda.Labelled
namespace Lamping.Lambda.Labelled
private theorem child_relative_parent {root relative parent : Path} {child : Step}
    (equal : root++relative=parent++[child]) (nonempty : relative≠[]) :
    ∃ inside,relative=inside++[child] ∧parent=root++inside := by
  rcases List.append_eq_append_iff.mp equal with ⟨inside,parentEq,relativeEq⟩ | ⟨extra,rootEq,childEq⟩
  · exact ⟨inside,relativeEq,parentEq⟩
  · cases extra with
    | nil => exact ⟨[],by simpa only [List.nil_append] using childEq.symm,
        by simpa only [List.append_nil] using rootEq.symm⟩
    | cons head rest =>
      have lengths := congrArg List.length childEq
      have positive : 0<relative.length := List.length_pos_iff.mpr nonempty
      simp only [List.length_cons,List.length_nil,List.length_append] at lengths
      omega

/-- The lambda CONTEXT reading moves to its actual old parent, preserving
its literal nonfunction last-step and returning the next occurrence preimage. -/
theorem StepAt.beta_lambda_parent_preimage
    {source target body argument currentBody : LTerm}
    {site p oldPosition parent : Path} {child : Step} {beta alpha stamp : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (origin : BetaNodePreimage body argument site p oldPosition)
    (lookup : target.subterm p=some (.lam stamp currentBody))
    (split : p=parent++[child]) (uncreated : ¬BetaCreatedIncoming body site p) :
    ∃ oldParent oldStamp oldBody,oldPosition=oldParent++[child] ∧
      source.subterm oldPosition=some (.lam oldStamp oldBody) ∧
      BetaNodePreimage body argument site parent oldParent := by
  obtain ⟨old,oldLambda,same⟩ := step.preimage_node_constructor redex origin lookup
  cases old with
  | var => cases same
  | app => cases same
  | lam oldStamp oldBody =>
    rcases origin.coordinates with ⟨equal,outside⟩ |
        ⟨relative,old,atCurrent,atOld,oldLookup,nonselected⟩ |
        ⟨q,relative,old,occurs,atCurrent,atOld,oldLookup⟩
    · refine ⟨parent,oldStamp,oldBody,equal.symm.trans split,oldLambda,.context ?_⟩
      rintro ⟨r,equal⟩
      exact outside ⟨r++[child],by rw [split,equal,List.append_assoc]⟩
    · have nonempty : relative≠[] := by
        intro empty
        exact uncreated (Or.inl (by simpa only [empty,List.append_nil] using atCurrent))
      obtain ⟨inside,relativeEq,parentEq⟩ := child_relative_parent (atCurrent.symm.trans split) nonempty
      have localLambda : body.subterm relative=some (.lam oldStamp oldBody) := by
        rw [atOld,List.append_assoc,LTerm.subterm_append,redex] at oldLambda
        simpa only [LTerm.subterm,Option.bind_some] using oldLambda
      rw [relativeEq,LTerm.subterm_append] at localLambda
      cases atParent : body.subterm inside with
      | none => rw [atParent] at localLambda; cases localLambda
      | some oldParentNode =>
        rw [atParent,Option.bind_some] at localLambda
        have parentRetained : ∀ parentStamp,oldParentNode≠.var parentStamp (binderDepth inside) := by
          intro parentStamp impossible
          rw [impossible] at localLambda
          cases child <;> cases localLambda
        refine ⟨(site++[.fn,.body])++inside,oldStamp,oldBody,?_,?_,?_⟩
        · simp only [atOld,relativeEq,List.append_assoc]
        · rw [atOld,List.append_assoc,LTerm.subterm_append,redex]
          simpa only [LTerm.subterm,Option.bind_some,LTerm.subterm_append,relativeEq,atParent] using localLambda
        · rw [parentEq]
          exact .retained atParent parentRetained
    · have nonempty : relative≠[] := by
        intro empty
        exact uncreated (betaCreatedIncoming_iff.mpr (Or.inr ⟨q,occurs,by simpa only [empty,List.append_nil] using atCurrent⟩))
      obtain ⟨inside,relativeEq,parentEq⟩ := child_relative_parent (atCurrent.symm.trans split) nonempty
      have localLambda : argument.subterm relative=some (.lam oldStamp oldBody) := by
        rw [atOld,List.append_assoc,LTerm.subterm_append,redex] at oldLambda
        simpa only [LTerm.subterm,Option.bind_some] using oldLambda
      rw [relativeEq,LTerm.subterm_append] at localLambda
      cases atParent : argument.subterm inside with
      | none => rw [atParent] at localLambda; cases localLambda
      | some oldParentNode =>
        rw [atParent,Option.bind_some] at localLambda
        refine ⟨(site++[.arg])++inside,oldStamp,oldBody,?_,?_,?_⟩
        · simp only [atOld,relativeEq,List.append_assoc]
        · rw [atOld,List.append_assoc,LTerm.subterm_append,redex]
          simpa only [LTerm.subterm,Option.bind_some,LTerm.subterm_append,relativeEq,atParent] using localLambda
        · rw [parentEq]
          exact .copied occurs atParent
end Lamping.Lambda.Labelled