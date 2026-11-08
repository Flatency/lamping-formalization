import Lamping.Lambda.RetainedBodyPrefixTransport
import Lamping.Lambda.PrerequisiteSubtreeEntry
import Lamping.Lambda.ContractumPositionOrigins
namespace Lamping.Lambda.Labelled
private theorem same_last_step {left right : Path} {s u : Step}
    (equal : left++[s]=right++[u]) : left=right ∧s=u := by
  have reversed := congrArg List.reverse equal
  simp only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append] at reversed
  have parts := List.cons.inj reversed
  exact ⟨by simpa only [List.reverse_reverse] using congrArg List.reverse parts.2,parts.1⟩
private theorem unsnoc_path (p : Path) (nonempty : p≠[]) : ∃ before last,p=before++[last] := by
  induction p with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail ih =>
    cases tail with
    | nil => exact ⟨[],head,rfl⟩
    | cons next rest =>
      obtain ⟨before,last,equal⟩ := ih (by simp)
      exact ⟨head::before,last,congrArg (head::·) equal⟩

private theorem StepAt.copy_prefix_cannot_exit_unread
    {source target body argument : LTerm} {site copySite start relative finish ending : Path} {beta alpha : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (occurs : ArgumentOccurrence body.erase copySite)
    (segment : PrerequisitePrefix target start before finish)
    (startEq : start=(site++copySite)++relative) (finishEq : finish=site++ending)
    (finishOutside : ¬∃ inside,finish=(site++copySite)++inside)
    (resultUnread : site∉before) (copyUnread : site++copySite∉before) : False := by
  induction segment generalizing relative with
  | refl => exact finishOutside ⟨relative,startEq⟩
  | @app p a fn arg es endpoint lookup notLambda tail ih =>
    have nextEq : p++[Step.fn]=(site++copySite)++(relative++[Step.fn]) := by rw [startEq,List.append_assoc]
    exact ih nextEq finishEq finishOutside
      (fun member=>resultUnread (List.mem_cons_of_mem _ member))
      (fun member=>copyUnread (List.mem_cons_of_mem _ member))
  | @lam parent child a inner es endpoint lookup notFunction tail ih =>
    by_cases empty : relative=[]
    · apply copyUnread
      apply List.mem_cons.mpr
      exact Or.inl (by simpa only [empty,List.append_nil] using startEq.symm)
    · obtain ⟨initial,last,relativeEq⟩ := unsnoc_path relative empty
      have lastEq : ((site++copySite)++initial)++[last]=parent++[child] := by
        simpa only [relativeEq,List.append_assoc] using startEq.symm
      obtain ⟨parentEq,childEq⟩ := same_last_step lastEq
      exact ih parentEq.symm finishEq finishOutside
        (fun member=>resultUnread (List.mem_cons_of_mem _ member))
        (fun member=>copyUnread (List.mem_cons_of_mem _ member))
  | @var leaf a index parent origin inner rest es endpoint lookup binder split depth tail ih =>
    have currentLeaf : target.subterm ((site++copySite)++relative)=some (.var a (binderDepth rest)) := by
      rw [←startEq,←depth]; exact lookup
    have bindingSplit : ((site++copySite)++relative)=parent++(.body::rest) := startEq.symm.trans split
    obtain ⟨oldParent,oldStamp,oldBody,oldBinder,oldJump,location⟩ :=
      step.copied_binder_old_prefix redex occurs binder currentLeaf bindingSplit
    rcases location with ⟨inside,parentEq,oldParentEq⟩ | ⟨outside,siteEq,oldParentEq⟩
    · exact ih parentEq finishEq finishOutside resultUnread copyUnread
    · obtain ⟨inside,parentInside⟩ := tail.start_inside_of_unread finishEq resultUnread
      have lengths := congrArg List.length parentInside
      have siteLengths := congrArg List.length siteEq
      simp only [List.length_append,List.length_cons] at lengths siteLengths
      omega
end Lamping.Lambda.Labelled
namespace Lamping.Lambda.Labelled
private theorem PrerequisitePrefix.start_lookup
    (segment : PrerequisitePrefix t start before finish) (atFinish : t.subterm finish=some current) :
    ∃ node,t.subterm start=some node := by
  cases segment with
  | refl => exact ⟨current,atFinish⟩
  | app lookup => exact ⟨_,lookup⟩
  | lam lookup => exact ⟨_,lookup⟩
  | var lookup => exact ⟨_,lookup⟩
private theorem old_function_parent {body : LTerm} {parent : Path}
    (occurs : ArgumentOccurrence body.erase (parent++[.fn])) :
    ∃ stamp fn arg,body.subterm parent=some (.app stamp fn arg) := by
  change subtermAt body.erase (parent++[.fn])=some (.var (binderDepth (parent++[.fn]))) at occurs
  rw [subtermAt_append,←LTerm.erase_subterm] at occurs
  cases atParent : body.subterm parent with
  | none => rw [atParent] at occurs; cases occurs
  | some old =>
    rw [atParent,Option.map_some,Option.bind_some] at occurs
    cases old with
    | var => cases occurs
    | lam => cases occurs
    | app stamp fn arg => exact ⟨stamp,fn,arg,rfl⟩

private theorem StepAt.unread_body_prefix_retained_start
    {source target body argument endFn endArg currentEnd : LTerm} {site start finish ending : Path}
    {beta alpha endStamp : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (segment : PrerequisitePrefix target start before finish) (finishEq : finish=site++ending)
    (atFinish : target.subterm finish=some currentEnd)
    (oldEndpoint : body.subterm ending=some (.app endStamp endFn endArg))
    (resultUnread : site∉before)
    (copiesUnread : ∀ q,ArgumentOccurrence body.erase q →site++q∉before) :
    ∃ relative old,start=site++relative ∧body.subterm relative=some old ∧
      ∀ stamp,old≠.var stamp (binderDepth relative) := by
  obtain ⟨relative,startEq⟩ := segment.start_inside_of_unread finishEq resultUnread
  obtain ⟨current,currentLookup⟩ := segment.start_lookup atFinish
  have localLookup : (LTerm.contract beta alpha body argument).subterm relative=some current := by
    rw [startEq,LTerm.subterm_append,step.contract_lookup redex,Option.bind_some] at currentLookup
    exact currentLookup
  have bareLookup : subtermAt (Lambda.contract body.erase argument.erase) relative=some current.erase := by
    rw [←LTerm.erase_contract,←LTerm.erase_subterm,localLookup]; rfl
  rcases subtermAt_contract_origins bareLookup with ⟨oldBare,atOld,nonvar,_⟩ |
      ⟨k,j,atOld,other,_,_⟩ | ⟨q,r,split,occurs,_⟩
  · rw [←LTerm.erase_subterm] at atOld
    obtain ⟨old,oldLookup,erased⟩ := Option.map_eq_some_iff.mp atOld
    refine ⟨relative,old,startEq,oldLookup,?_⟩
    intro stamp equal
    exact nonvar _ (erased.symm.trans (congrArg LTerm.erase equal))
  · rw [←LTerm.erase_subterm] at atOld
    obtain ⟨old,oldLookup,erased⟩ := Option.map_eq_some_iff.mp atOld
    refine ⟨relative,old,startEq,oldLookup,?_⟩
    intro stamp equal
    exact other (Term.var.inj (erased.symm.trans (congrArg LTerm.erase equal)))
  · have startCopy : start=(site++q)++r := by rw [startEq,split,List.append_assoc]
    have outsideCopy : ¬∃ inside,finish=(site++q)++inside := by
      rintro ⟨inside,equal⟩
      have relativeEq : ending=q++inside := List.append_cancel_left (by
        simpa only [List.append_assoc] using finishEq.symm.trans equal)
      have oldBare : subtermAt body.erase ending=some (.app endFn.erase endArg.erase) := by
        rw [←LTerm.erase_subterm,oldEndpoint]; rfl
      exact nonvariable_origin_not_variable_prefix oldBare (by intro i impossible; cases impossible) occurs relativeEq
    exact False.elim (step.copy_prefix_cannot_exit_unread redex occurs segment startCopy finishEq outsideCopy
      resultUnread (copiesUnread q occurs))

/-- First-new COPY-FUNCTION prefixes reflect to the retained body coordinates.
All old start data are derived from the actual finite reading and unread heads. -/
theorem StepAt.copy_function_prefix_reflect_labelled
    {source target body argument currentFn currentArg : LTerm} {site parent start : Path}
    {beta alpha currentStamp : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (occurs : ArgumentOccurrence body.erase (parent++[.fn]))
    (atParent : target.subterm (site++parent)=some (.app currentStamp currentFn currentArg))
    (reading : PrerequisitePrefix target start before (site++parent))
    (resultUnread : site∉before)
    (copiesUnread : ∀ q,ArgumentOccurrence body.erase q →site++q∉before) :
    ∃ relative,start=site++relative ∧
      PrerequisiteChain source ((site++[Step.fn,Step.body])++relative)
        ((before.map (fun edge=>(site++[Step.fn,Step.body])++edge.drop site.length))++
          [(site++[Step.fn,Step.body])++(parent++[Step.fn]),site++[Step.fn]]) ∧
      before.map target.labelAt=
        (before.map (fun edge=>(site++[Step.fn,Step.body])++edge.drop site.length)).map source.labelAt := by
  obtain ⟨oldStamp,oldFn,oldArg,oldEndpoint⟩ := old_function_parent occurs
  obtain ⟨relative,old,startEq,oldLookup,retained⟩ :=
    step.unread_body_prefix_retained_start redex reading rfl atParent oldEndpoint resultUnread copiesUnread
  obtain ⟨oldPrefix,labels⟩ := step.retained_body_prefix_reflect_labelled redex reading startEq rfl
    oldLookup retained copiesUnread
  have oldTail := substituted_function_old_chain redex occurs
  have oldTail' : PrerequisiteChain source ((site++[Step.fn,Step.body])++parent)
      [(site++[Step.fn,Step.body])++(parent++[Step.fn]),site++[Step.fn]] := by
    simpa only [List.append_assoc] using oldTail
  exact ⟨relative,startEq,oldPrefix.close oldTail',labels⟩
end Lamping.Lambda.Labelled

