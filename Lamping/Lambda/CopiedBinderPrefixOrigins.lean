import Lamping.Lambda.LabelArgumentBinderScope
import Lamping.Lambda.LabelContextualRegions
import Lamping.Lambda.PrerequisitePrefixes
import Lamping.Lambda.CopiedLambdaBodies
import Lamping.Lambda.BetaBoundVariableOrigins
namespace Lamping.Lambda.Labelled
/-- The same actual copied lambda and its internal bound leaf reflect to
one OLD argument lambda/leaf pair and the real zero-edge binder jump. -/
theorem StepAt.copied_internal_binder_prefix
    {source target body argument currentBody : LTerm}
    {site copySite relative descendant : Path} {beta alpha currentStamp leafStamp : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (occurs : ArgumentOccurrence body.erase copySite)
    (atLambda : target.subterm (site++(copySite++relative))=some (.lam currentStamp currentBody))
    (atLeaf : target.subterm ((site++(copySite++relative))++(.body::descendant))=
      some (.var leafStamp (binderDepth descendant))) :
    ∃ oldStamp oldBody variableStamp,
      source.subterm ((site++[.arg])++relative)=some (.lam oldStamp oldBody) ∧
      source.subterm (((site++[.arg])++relative)++(.body::descendant))=
        some (.var variableStamp (binderDepth descendant)) ∧
      PrerequisitePrefix source (((site++[.arg])++relative)++(.body::descendant))
        [] ((site++[.arg])++relative) := by
  have localLambda : (LTerm.contract beta alpha body argument).subterm (copySite++relative)=
      some (.lam currentStamp currentBody) := by
    rw [LTerm.subterm_append,step.contract_lookup redex,Option.bind_some] at atLambda
    exact atLambda
  obtain ⟨oldStamp,oldBody,oldArgument,_⟩ :=
    LTerm.contract_copied_lambda_origin occurs localLambda
  have bareRedex : subtermAt source.erase site=some (.app (.lam body.erase) argument.erase) := by
    rw [←LTerm.erase_subterm,redex]; rfl
  have bareLambda : subtermAt argument.erase relative=some (.lam oldBody.erase) := by
    rw [←LTerm.erase_subterm,oldArgument]; rfl
  have bareLeaf : subtermAt target.erase ((site++(copySite++relative))++(.body::descendant))=
      some (.var (binderDepth descendant)) := by
    rw [←LTerm.erase_subterm,atLeaf]; rfl
  have oldBare := (step.betaAt.copied_lambda_bound_variable_iff bareRedex occurs bareLambda descendant).mp bareLeaf
  have oldBinder : source.subterm ((site++[.arg])++relative)=some (.lam oldStamp oldBody) := by
    rw [List.append_assoc,LTerm.subterm_append,redex]
    simpa only [LTerm.subterm,Option.bind_some] using oldArgument
  have oldMapped : (source.subterm (((site++[.arg])++relative)++(.body::descendant))).map LTerm.erase=
      some (.var (binderDepth descendant)) := by
    rw [LTerm.erase_subterm]
    exact oldBare
  obtain ⟨oldLeaf,oldLookup,oldShape⟩ := Option.map_eq_some_iff.mp oldMapped
  cases oldLeaf with
  | app => cases oldShape
  | lam => cases oldShape
  | var variableStamp index =>
    have same : index=binderDepth descendant := Term.var.inj oldShape
    subst index
    exact ⟨oldStamp,oldBody,variableStamp,oldBinder,oldLookup,
      .var oldLookup oldBinder rfl rfl .refl⟩
end Lamping.Lambda.Labelled


namespace Lamping.Lambda
private theorem path_binder_at_depth (p : Path) (k : Nat) (bound : k<binderDepth p) :
    ∃ parent rest,p=parent++(.body::rest) ∧ k=binderDepth rest := by
  induction p generalizing k with
  | nil => simp only [binderDepth] at bound; omega
  | cons step tail ih =>
    cases step with
    | fn | arg =>
      obtain ⟨parent,rest,split,depth⟩ := ih k bound
      exact ⟨_::parent,rest,congrArg (_::·) split,depth⟩
    | body =>
      by_cases inner : k<binderDepth tail
      · obtain ⟨parent,rest,split,depth⟩ := ih k inner
        exact ⟨.body::parent,rest,congrArg (.body::·) split,depth⟩
      · exact ⟨[],tail,rfl,by simp only [binderDepth] at bound; omega⟩

/-- The protected interval between original internal variables and shifted
free variables contains no image of a capture-avoiding argument renaming. -/
theorem shifted_variable_index_gap {argument : Term} {p : Path} {shift index : Nat}
    (lookup : subtermAt (rename (fun i => i+shift) argument) p=some (.var index)) :
    index<binderDepth p ∨ shift+binderDepth p≤index := by
  rw [subtermAt_rename] at lookup
  obtain ⟨old,_,shape⟩ := Option.map_eq_some_iff.mp lookup
  cases old with
  | app => cases shape
  | lam => cases shape
  | var oldIndex =>
    have equal := Term.var.inj shape
    by_cases inside : oldIndex<binderDepth p
    · left
      rw [occurrenceRenaming_bound _ _ _ inside] at equal
      exact equal ▸ inside
    · right
      have split : oldIndex=(oldIndex-binderDepth p)+binderDepth p := by omega
      rw [split,occurrenceRenaming_free_index] at equal
      omega

/-- A binder of one actual shifted-copy variable is either inside that same
copy, or strictly above the beta head. No retained body binder captures it. -/
theorem copied_variable_binder_scope {argument : Term} {site copySite relative parent rest : Path}
    (lookup : subtermAt (rename (fun i => i+binderDepth copySite) argument) relative=
      some (.var (binderDepth rest)))
    (split : site++(copySite++relative)=parent++(.body::rest)) :
    (∃ localParent,parent=(site++copySite)++localParent) ∨
    (∃ outside,site=parent++(.body::outside)) := by
  rcases shifted_variable_index_gap lookup with internal | external
  · obtain ⟨localParent,localRest,relativeEq,sameDepth⟩ :=
      path_binder_at_depth relative (binderDepth rest) internal
    have samePath : ((site++copySite)++localParent)++(.body::localRest)=parent++(.body::rest) := by
      rw [List.append_assoc,List.append_assoc,←relativeEq,←List.append_assoc]
      simpa only [List.append_assoc] using split
    have same := binding_prefix_depth_unique samePath sameDepth.symm
    exact .inl ⟨localParent,same.1.symm⟩
  · have depthEq := congrArg binderDepth split
    simp only [binderDepth_append,binderDepth] at depthEq
    have above : binderDepth parent<binderDepth site := by omega
    have comparable : site <+: parent ∨parent <+: site :=
      List.prefix_or_prefix_of_prefix (l₃ := site++(copySite++relative))
        ⟨copySite++relative,rfl⟩ ⟨.body::rest,split.symm⟩
    rcases comparable with ⟨suffix,eq⟩ | ⟨suffix,eq⟩
    · have depths := congrArg binderDepth eq
      rw [binderDepth_append] at depths
      omega
    · cases suffix with
      | nil => simp only [List.append_nil] at eq; have depths := congrArg binderDepth eq; omega
      | cons step tail =>
        have same : (step::tail)++(copySite++relative)=.body::rest := by
          apply List.append_cancel_left (as := parent)
          rw [←List.append_assoc,eq]
          exact split
        have headEq := (List.cons.inj same).1
        subst step
        exact .inr ⟨tail,eq.symm⟩
end Lamping.Lambda

namespace Lamping.Lambda.Labelled
private theorem StepAt.actual_copy_variable_lookup
    {source target body argument : LTerm} {site copySite relative : Path} {beta alpha stamp : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (occurs : ArgumentOccurrence body.erase copySite)
    (atLeaf : target.subterm ((site++copySite)++relative)=some (.var stamp index)) :
    subtermAt (Lambda.rename (fun i => i+binderDepth copySite) argument.erase) relative=some (.var index) := by
  have bareRedex : subtermAt source.erase site=some (.app (.lam body.erase) argument.erase) := by
    rw [←LTerm.erase_subterm,redex]; rfl
  have bareLeaf : subtermAt target.erase (site++(copySite++relative))=some (.var index) := by
    rw [←List.append_assoc,←LTerm.erase_subterm,atLeaf]; rfl
  rw [subtermAt_append,step.betaAt.contract_lookup bareRedex,Option.bind_some] at bareLeaf
  rw [subtermAt_append,argument_copy occurs argument.erase,Option.bind_some] at bareLeaf
  exact bareLeaf

/-- Every actual copied bound-variable jump reflects to a real old ARG
variable jump. The binder is recovered inside that copy or above the head. -/
theorem StepAt.copied_binder_old_prefix
    {source target body argument binderBody : LTerm}
    {site copySite relative parent rest : Path} {beta alpha binderStamp leafStamp : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (occurs : ArgumentOccurrence body.erase copySite)
    (atBinder : target.subterm parent=some (.lam binderStamp binderBody))
    (atLeaf : target.subterm ((site++copySite)++relative)=some (.var leafStamp (binderDepth rest)))
    (split : ((site++copySite)++relative)=parent++(.body::rest)) :
    ∃ oldParent oldStamp oldBody,
      source.subterm oldParent=some (.lam oldStamp oldBody) ∧
      PrerequisitePrefix source ((site++[.arg])++relative) [] oldParent ∧
      ((∃ inside,parent=(site++copySite)++inside ∧ oldParent=((site++[.arg])++inside)) ∨ (∃ outside,site=parent++(.body::outside) ∧oldParent=parent)) := by
  have bareCopy := step.actual_copy_variable_lookup redex occurs atLeaf
  have localSplit : site++(copySite++relative)=parent++(.body::rest) := by
    simpa only [List.append_assoc] using split
  rcases Lambda.copied_variable_binder_scope bareCopy localSplit with ⟨inside,parentEq⟩ | ⟨outside,siteEq⟩
  · have relativeEq : relative=inside++(.body::rest) := by
      apply List.append_cancel_left (as := site++copySite)
      simpa only [parentEq,List.append_assoc] using split
    have localBinder : target.subterm (site++(copySite++inside))=some (.lam binderStamp binderBody) := by
      simpa only [parentEq,List.append_assoc] using atBinder
    have localLeaf : target.subterm ((site++(copySite++inside))++(.body::rest))=
        some (.var leafStamp (binderDepth rest)) := by
      simpa only [relativeEq,List.append_assoc] using atLeaf
    obtain ⟨oldStamp,oldBody,varStamp,oldBinder,oldLeaf,segment⟩ :=
      step.copied_internal_binder_prefix redex occurs localBinder localLeaf
    refine ⟨(site++[.arg])++inside,oldStamp,oldBody,oldBinder,?_,Or.inl ⟨inside,parentEq,rfl⟩⟩
    simpa only [relativeEq,List.append_assoc] using segment
  · obtain ⟨suffix,oldBody,restEq,oldBinder⟩ := step.strict_lambda_ancestor atBinder siteEq (by simp)
    have suffixEq : suffix=outside := (List.cons.inj restEq).2.symm
    subst suffix
    have restEq : rest=outside++(copySite++relative) := by
      have equal : (.body::rest)=.body::(outside++(copySite++relative)) := by
        apply List.append_cancel_left (as := parent)
        simpa only [siteEq,List.append_assoc] using split.symm
      exact (List.cons.inj equal).2
    have shifted : subtermAt (Lambda.rename (fun i => i+binderDepth copySite) argument.erase) relative=
        some (.var ((binderDepth outside+binderDepth copySite)+binderDepth relative)) := by
      simpa only [restEq,binderDepth_append,Nat.add_assoc] using bareCopy
    have oldBare := (Lambda.shifted_outer_variable_iff argument.erase relative
      (binderDepth outside) (binderDepth copySite)).mp shifted
    have mapped : (argument.subterm relative).map LTerm.erase=
        some (.var (binderDepth outside+binderDepth relative)) := by
      rw [LTerm.erase_subterm]; exact oldBare
    obtain ⟨oldLeaf,argumentLeaf,shape⟩ := Option.map_eq_some_iff.mp mapped
    cases oldLeaf with
    | app => cases shape
    | lam => cases shape
    | var varStamp index =>
      have indexEq : index=binderDepth outside+binderDepth relative := Term.var.inj shape
      subst index
      have globalLeaf : source.subterm ((site++[.arg])++relative)=
          some (.var varStamp (binderDepth outside+binderDepth relative)) := by
        rw [List.append_assoc,LTerm.subterm_append,redex]
        simpa only [LTerm.subterm,Option.bind_some] using argumentLeaf
      refine ⟨parent,binderStamp,oldBody,oldBinder,?_,Or.inr ⟨outside,siteEq,rfl⟩⟩
      apply PrerequisitePrefix.var (rest := outside++(.arg::relative)) globalLeaf oldBinder
      · simp only [siteEq,List.append_assoc,List.cons_append,List.nil_append]
      · simp only [binderDepth_append,binderDepth]
      · exact .refl
end Lamping.Lambda.Labelled




