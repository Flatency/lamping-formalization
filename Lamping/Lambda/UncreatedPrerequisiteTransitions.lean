import Lamping.Lambda.FirstCreatedIncoming
import Lamping.Lambda.ContractumPositionOrigins
import Lamping.Lambda.CopiedBinderPrefixOrigins
import Lamping.Lambda.RetainedBinderPrefixOrigins
namespace Lamping.Lambda.Labelled
/-- An actual beta occurrence preimage. Different copied occurrences may
have the same old ARG preimage; no label injectivity is asserted. -/
inductive BetaNodePreimage (body argument : LTerm) (site : Path) : Path →Path →Prop where
  | context (outside : ¬∃ relative,p=site++relative) : BetaNodePreimage body argument site p p
  | retained (lookup : body.subterm relative=some old)
      (nonselected : ∀ stamp,old≠.var stamp (binderDepth relative)) :
      BetaNodePreimage body argument site (site++relative) ((site++[.fn,.body])++relative)
  | copied (occurs : ArgumentOccurrence body.erase q)
      (lookup : argument.subterm relative=some old) :
      BetaNodePreimage body argument site ((site++q)++relative) ((site++[.arg])++relative)

private theorem LTerm.CopyInterior.lookup_preimage
    (interior : LTerm.CopyInterior original copy) (lookup : copy.subterm p=some node) :
    ∃ old,original.subterm p=some old := by
  cases p with
  | nil => exact ⟨original,by cases original <;> rfl⟩
  | cons child rest =>
    obtain ⟨old,atOld,_⟩ := interior.nonroot_node lookup (by simp)
    exact ⟨old,atOld⟩

/-- The actual contractum lookup constructs its old occurrence coordinate.
It allows the incoming result/copy root and requires no INIT at the reduct. -/
theorem StepAt.beta_node_preimage
    {source target body argument current : LTerm} {site p : Path} {beta alpha : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (lookup : target.subterm p=some current) :
    ∃ oldPosition,BetaNodePreimage body argument site p oldPosition := by
  classical
  by_cases inside : ∃ relative,p=site++relative
  · obtain ⟨relative,equal⟩ := inside
    subst p
    have localLookup : (LTerm.contract beta alpha body argument).subterm relative=some current := by
      rw [LTerm.subterm_append,step.contract_lookup redex,Option.bind_some] at lookup
      exact lookup
    have bareLookup : subtermAt (Lambda.contract body.erase argument.erase) relative=some current.erase := by
      rw [←LTerm.erase_contract,←LTerm.erase_subterm,localLookup]; rfl
    rcases subtermAt_contract_origins bareLookup with ⟨oldBare,atOld,nonvar,_⟩ |
        ⟨k,j,atOld,other,_,_⟩ | ⟨q,r,split,occurs,_⟩
    · rw [←LTerm.erase_subterm] at atOld
      obtain ⟨old,oldLookup,erased⟩ := Option.map_eq_some_iff.mp atOld
      refine ⟨_,.retained oldLookup ?_⟩
      intro stamp equal
      exact nonvar _ (erased.symm.trans (congrArg LTerm.erase equal))
    · rw [←LTerm.erase_subterm] at atOld
      obtain ⟨old,oldLookup,erased⟩ := Option.map_eq_some_iff.mp atOld
      refine ⟨_,.retained oldLookup ?_⟩
      intro stamp equal
      exact other (Term.var.inj (erased.symm.trans (congrArg LTerm.erase equal)))
    · rw [split,LTerm.subterm_append] at localLookup
      cases copyLookup : (LTerm.contract beta alpha body argument).subterm q with
      | none => rw [copyLookup] at localLookup; cases localLookup
      | some copy =>
        rw [copyLookup,Option.bind_some] at localLookup
        obtain ⟨old,oldLookup⟩ := (LTerm.contract_argument_copy_interior occurs copyLookup).lookup_preimage localLookup
        refine ⟨(site++[.arg])++r,?_⟩
        simpa only [split,List.append_assoc] using (BetaNodePreimage.copied (body := body) (argument := argument) (site := site) occurs oldLookup)
  · exact ⟨p,.context inside⟩
end Lamping.Lambda.Labelled
namespace Lamping.Lambda.Labelled
private theorem retained_not_copy
    {body old : LTerm} {relative q r : Path}
    (lookup : body.subterm relative=some old)
    (nonselected : ∀ stamp,old≠.var stamp (binderDepth relative))
    (occurs : ArgumentOccurrence body.erase q) (split : relative=q++r) : False := by
  have bare : subtermAt body.erase relative=some old.erase := by rw [←LTerm.erase_subterm,lookup]; rfl
  cases old with
  | var stamp index =>
    exact retained_variable_not_argument_origin bare
      (by intro eq; exact nonselected stamp (by rw [eq])) occurs split
  | lam stamp inner => exact nonvariable_origin_not_variable_prefix bare (by intro i impossible; cases impossible) occurs split
  | app stamp fn arg => exact nonvariable_origin_not_variable_prefix bare (by intro i impossible; cases impossible) occurs split

theorem BetaNodePreimage.coordinates (origin : BetaNodePreimage body argument site current oldPosition) :
    (current=oldPosition ∧¬∃ relative,current=site++relative) ∨
    (∃ relative old,current=site++relative ∧oldPosition=(site++[.fn,.body])++relative ∧
      body.subterm relative=some old ∧∀ stamp,old≠.var stamp (binderDepth relative)) ∨
    (∃ q relative old,ArgumentOccurrence body.erase q ∧current=(site++q)++relative ∧
      oldPosition=(site++[.arg])++relative ∧argument.subterm relative=some old) := by
  cases origin with
  | context outside => exact Or.inl ⟨rfl,outside⟩
  | retained lookup nonselected => exact Or.inr (Or.inl ⟨_,_,rfl,rfl,lookup,nonselected⟩)
  | copied occurs lookup => exact Or.inr (Or.inr ⟨_,_,_,occurs,rfl,rfl,lookup⟩)

/-- The preimage coordinate is fixed by actual variable-occurrence prefixes,
not by equality of labels. Several new copies may still share this old point. -/
theorem BetaNodePreimage.unique
    (left : BetaNodePreimage body argument site current first)
    (right : BetaNodePreimage body argument site current second) : first=second := by
  rcases left.coordinates with ⟨equal,outside⟩ | ⟨relative,old,atCurrent,atFirst,lookup,nonselected⟩ |
      ⟨q,relative,old,occurs,atCurrent,atFirst,lookup⟩
  · rcases right.coordinates with ⟨same,_⟩ | ⟨r,_,eq,_,_⟩ | ⟨q,r,_,_,eq,_,_⟩
    · exact equal.symm.trans same
    · exact False.elim (outside ⟨r,eq⟩)
    · exact False.elim (outside ⟨q++r,by simpa only [List.append_assoc] using eq⟩)
  · rcases right.coordinates with ⟨_,outside⟩ | ⟨r,_,eq,atSecond,_⟩ |
        ⟨q,r,_,occurs,eq,atSecond,_⟩
    · exact False.elim (outside ⟨relative,atCurrent⟩)
    · have same : relative=r := List.append_cancel_left (atCurrent.symm.trans eq)
      rw [atFirst,atSecond,same]
    · have split : relative=q++r := List.append_cancel_left (by
        simpa only [List.append_assoc] using atCurrent.symm.trans eq)
      exact False.elim (retained_not_copy lookup nonselected occurs split)
  · rcases right.coordinates with ⟨_,outside⟩ | ⟨r,old,eq,atSecond,oldLookup,nonselected⟩ |
        ⟨other,r,_,otherOccurs,eq,atSecond,_⟩
    · exact False.elim (outside ⟨q++relative,by simpa only [List.append_assoc] using atCurrent⟩)
    · have split : r=q++relative := List.append_cancel_left (by
        simpa only [List.append_assoc] using eq.symm.trans atCurrent)
      exact False.elim (retained_not_copy oldLookup nonselected occurs split)
    · have split : q++relative=other++r := List.append_cancel_left (by
        simpa only [List.append_assoc] using atCurrent.symm.trans eq)
      obtain ⟨sameCopy,sameRelative⟩ := contract_argument_origin_unique occurs otherOccurs split
      rw [atFirst,atSecond,sameRelative]
end Lamping.Lambda.Labelled
namespace Lamping.Lambda.Labelled
/-- An outside actual variable and its lexical lambda inherit a real old
zero-edge jump at the SAME literal coordinates. No labels are used as names. -/
private theorem StepAt.outside_variable_old_prefix
    {source target body argument binderBody : LTerm} {site leaf parent rest : Path}
    {beta alpha binderStamp leafStamp : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (outside : ¬∃ relative,leaf=site++relative)
    (atBinder : target.subterm parent=some (.lam binderStamp binderBody))
    (atLeaf : target.subterm leaf=some (.var leafStamp (binderDepth rest)))
    (split : leaf=parent++(.body::rest)) :
    ∃ oldStamp oldBody,source.subterm parent=some (.lam oldStamp oldBody) ∧
      PrerequisitePrefix source leaf [] parent ∧
      (¬∃ relative,parent=site++relative) := by
  have bareRedex : subtermAt source.erase site=some (.app (.lam body.erase) argument.erase) := by
    rw [←LTerm.erase_subterm,redex]; rfl
  have bareLeaf : subtermAt target.erase leaf=some (.var (binderDepth rest)) := by
    rw [←LTerm.erase_subterm,atLeaf]; rfl
  have oldLeaf : subtermAt source.erase leaf=some (.var (binderDepth rest)) := by
    rcases step.betaAt.bound_variable_outside_or_below bareRedex bareLeaf with ⟨_,old⟩ | ⟨r,equal⟩
    · exact old
    · exact False.elim (outside ⟨r,equal⟩)
  rw [←LTerm.erase_subterm] at oldLeaf
  obtain ⟨oldLeaf,oldLookup,oldShape⟩ := Option.map_eq_some_iff.mp oldLeaf
  cases oldLeaf with
  | app => cases oldShape
  | lam => cases oldShape
  | var oldLeafStamp index =>
    have indexEq : index=binderDepth rest := Term.var.inj oldShape
    subst index
    have parentOutside : ¬∃ relative,parent=site++relative := by
      rintro ⟨r,equal⟩
      exact outside ⟨r++(.body::rest),by rw [split,equal,List.append_assoc]⟩
    have oldBinder : ∃ oldStamp oldBody,source.subterm parent=some (.lam oldStamp oldBody) := by
      classical
      by_cases above : ∃ suffix,site=parent++suffix
      · obtain ⟨suffix,equal⟩ := above
        have nonempty : suffix≠[] := by
          intro empty
          apply parentOutside
          exact ⟨[],by simpa only [empty,List.append_nil] using equal.symm⟩
        obtain ⟨suffix',oldBody,_,old⟩ := step.strict_lambda_ancestor atBinder equal nonempty
        exact ⟨binderStamp,oldBody,old⟩
      · have apart : DisjointPositions site parent := ⟨parentOutside,above⟩
        have bareBinder : subtermAt target.erase parent=some (.lam binderBody.erase) := by
          rw [←LTerm.erase_subterm,atBinder]; rfl
        have oldBare := (step.betaAt.disjoint_subterm apart).symm.trans bareBinder
        rw [←LTerm.erase_subterm] at oldBare
        obtain ⟨old,oldLookup,shape⟩ := Option.map_eq_some_iff.mp oldBare
        cases old with
        | var => cases shape
        | app => cases shape
        | lam oldStamp oldBody => exact ⟨oldStamp,oldBody,oldLookup⟩
    obtain ⟨oldStamp,oldBody,oldBinder⟩ := oldBinder
    exact ⟨oldStamp,oldBody,oldBinder,.var oldLookup oldBinder split rfl .refl,parentOutside⟩
end Lamping.Lambda.Labelled
namespace Lamping.Lambda.Labelled
/-- Every actual lexical zero-edge jump has an old zero-edge jump and a
preimage for its next occurrence. Copied and retained variables may genuinely
switch to outside context at their external binder. -/
theorem StepAt.beta_variable_preimage_prefix
    {source target body argument binderBody : LTerm} {site leaf oldLeaf parent rest : Path}
    {beta alpha binderStamp leafStamp : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (preimage : BetaNodePreimage body argument site leaf oldLeaf)
    (atBinder : target.subterm parent=some (.lam binderStamp binderBody))
    (atLeaf : target.subterm leaf=some (.var leafStamp (binderDepth rest)))
    (split : leaf=parent++(.body::rest)) :
    ∃ oldParent oldStamp oldBody,source.subterm oldParent=some (.lam oldStamp oldBody) ∧
      PrerequisitePrefix source oldLeaf [] oldParent ∧
      BetaNodePreimage body argument site parent oldParent := by
  rcases preimage.coordinates with ⟨equal,outside⟩ |
      ⟨relative,old,atCurrent,atOld,oldLookup,nonselected⟩ |
      ⟨q,relative,old,occurs,atCurrent,atOld,oldLookup⟩
  · obtain ⟨oldStamp,oldBody,oldBinder,oldJump,parentOutside⟩ :=
      step.outside_variable_old_prefix redex outside atBinder atLeaf split
    exact ⟨parent,oldStamp,oldBody,oldBinder,by simpa only [←equal] using oldJump,.context parentOutside⟩
  · have bareOld : subtermAt body.erase relative=some old.erase := by
      rw [←LTerm.erase_subterm,oldLookup]; rfl
    have currentBare : subtermAt (Lambda.contract body.erase argument.erase) relative=
        some (.var (binderDepth rest)) := by
      have localLookup : (LTerm.contract beta alpha body argument).subterm relative=
          some (.var leafStamp (binderDepth rest)) := by
        rw [atCurrent,LTerm.subterm_append,step.contract_lookup redex,Option.bind_some] at atLeaf
        exact atLeaf
      rw [←LTerm.erase_contract,←LTerm.erase_subterm,localLookup]; rfl
    have actualSubst := subtermAt_subst bareOld (singleSub argument.erase)
    have shape := Option.some.inj (actualSubst.symm.trans currentBare)
    cases old with
    | app => cases shape
    | lam => cases shape
    | var oldLeafStamp index =>
      have other : index≠binderDepth relative := by intro equal; exact nonselected oldLeafStamp (by rw [equal])
      have leafLookup : target.subterm (site++relative)=some (.var leafStamp (binderDepth rest)) := atCurrent ▸ atLeaf
      have leafSplit : site++relative=parent++(.body::rest) := atCurrent ▸ split
      obtain ⟨oldParent,oldStamp,oldBody,oldBinder,oldJump,location⟩ :=
        step.retained_binder_old_prefix redex oldLookup other atBinder leafLookup leafSplit
      refine ⟨oldParent,oldStamp,oldBody,oldBinder,by simpa only [atOld] using oldJump,?_⟩
      rcases location with ⟨inside,parentEq,oldParentEq⟩ | ⟨outside,siteEq,oldParentEq⟩
      · have oldLocal : body.subterm inside=some (.lam oldStamp oldBody) := by
          rw [oldParentEq,List.append_assoc,LTerm.subterm_append,redex] at oldBinder
          simpa only [LTerm.subterm,Option.bind_some] using oldBinder
        rw [parentEq,oldParentEq]
        exact .retained oldLocal (by intro stamp impossible; cases impossible)
      · rw [oldParentEq]
        apply BetaNodePreimage.context
        rintro ⟨relative,equal⟩
        have sizes := congrArg List.length (equal.trans (congrArg (·++relative) siteEq))
        simp only [List.length_append,List.length_cons] at sizes
        omega
  · have leafLookup : target.subterm ((site++q)++relative)=some (.var leafStamp (binderDepth rest)) := atCurrent ▸ atLeaf
    have leafSplit : (site++q)++relative=parent++(.body::rest) := atCurrent ▸ split
    obtain ⟨oldParent,oldStamp,oldBody,oldBinder,oldJump,location⟩ :=
      step.copied_binder_old_prefix redex occurs atBinder leafLookup leafSplit
    refine ⟨oldParent,oldStamp,oldBody,oldBinder,by simpa only [atOld] using oldJump,?_⟩
    rcases location with ⟨inside,parentEq,oldParentEq⟩ | ⟨outside,siteEq,oldParentEq⟩
    · have oldLocal : argument.subterm inside=some (.lam oldStamp oldBody) := by
        rw [oldParentEq,List.append_assoc,LTerm.subterm_append,redex] at oldBinder
        simpa only [LTerm.subterm,Option.bind_some] using oldBinder
      rw [parentEq,oldParentEq]
      exact .copied occurs oldLocal
    · rw [oldParentEq]
      apply BetaNodePreimage.context
      rintro ⟨relative,equal⟩
      have sizes := congrArg List.length (equal.trans (congrArg (·++relative) siteEq))
      simp only [List.length_append,List.length_cons] at sizes
      omega
end Lamping.Lambda.Labelled