import Lamping.Lambda.RetainedBinderPrefixOrigins
import Lamping.Lambda.BetaIncomingEdgeOrigins
import Lamping.Lambda.PrerequisiteOrder
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

private theorem order_all_bound (t : LTerm) (p : Path) : prerequisiteOrder t p<prerequisiteNodeCount t := by
  induction t generalizing p with
  | var => cases p <;> simp only [prerequisiteOrder,prerequisiteNodeCount] <;> omega
  | lam stamp body ih =>
    cases p with
    | nil => simp only [prerequisiteOrder,prerequisiteNodeCount]; omega
    | cons step rest => cases step <;> simp only [prerequisiteOrder,prerequisiteNodeCount]; all_goals have bound := ih rest; omega
  | app stamp fn arg hf ha =>
    cases p with
    | nil => simp only [prerequisiteOrder,prerequisiteNodeCount]; have bound := ha []; omega
    | cons step rest => cases step <;> simp only [prerequisiteOrder,prerequisiteNodeCount]; all_goals have fb := hf rest; have ab := ha rest; omega

theorem prerequisiteOrder_function_descendant (lookup : t.subterm parent=some (.app stamp fn arg)) (relative : Path) :
    prerequisiteOrder t ((parent++[.fn])++relative)<prerequisiteOrder t parent := by
  obtain ⟨offset,order⟩ := prerequisiteOrder_subtree lookup
  have root := order []
  have child := order (.fn::relative)
  simp only [List.append_nil,prerequisiteOrder] at root child
  have bound := order_all_bound fn relative
  simpa only [List.append_assoc,List.cons_append,List.nil_append] using (show prerequisiteOrder t (parent++(.fn::relative))<prerequisiteOrder t parent by omega)

theorem PrerequisitePrefix.finish_order_bound (segment : PrerequisitePrefix t start before finish) :
    prerequisiteOrder t finish≤prerequisiteOrder t start := by
  induction segment with
  | refl => exact Nat.le_refl _
  | app lookup notLambda tail ih => have less := (PrerequisiteDependency.app lookup notLambda).order_lt; omega
  | @lam parent child stamp body es finish lookup notFunction tail ih =>
    rw [LTerm.subterm_append] at lookup
    cases atParent : t.subterm parent with
    | none => rw [atParent] at lookup; cases lookup
    | some old =>
      rw [atParent] at lookup
      have actualChild : t.subterm (parent++[child])=some (.lam stamp body) := by rw [LTerm.subterm_append,atParent]; exact lookup
      have less := (PrerequisiteDependency.lam atParent actualChild notFunction).order_lt
      omega
  | var lookup binder split depth tail ih =>
    have less := (PrerequisiteDependency.var lookup binder split depth).order_lt
    omega

private theorem contract_old_erased_shape
    (oldLookup : body.subterm relative=some old)
    (currentLookup : (LTerm.contract beta alpha body argument).subterm relative=some current) :
    current.erase=Lambda.subst (liftSubN (binderDepth relative) (singleSub argument.erase)) old.erase := by
  have oldBare : subtermAt body.erase relative=some old.erase := by rw [←LTerm.erase_subterm,oldLookup]; rfl
  have currentBare : subtermAt (Lambda.contract body.erase argument.erase) relative=some current.erase := by
    rw [←LTerm.erase_contract,←LTerm.erase_subterm,currentLookup]; rfl
  have forward := subtermAt_subst oldBare (singleSub argument.erase)
  exact (Option.some.inj (forward.symm.trans currentBare)).symm

private theorem retained_old_app
    (oldLookup : body.subterm relative=some old)
    (retained : ∀ stamp,old≠.var stamp (binderDepth relative))
    (currentLookup : (LTerm.contract beta alpha body argument).subterm relative=some (.app currentStamp fn arg)) :
    ∃ stamp oldFn oldArg,old=.app stamp oldFn oldArg := by
  have shape := contract_old_erased_shape oldLookup currentLookup
  cases old with
  | app stamp oldFn oldArg => exact ⟨stamp,oldFn,oldArg,rfl⟩
  | lam => cases shape
  | var stamp index =>
    have other : index≠binderDepth relative := by intro eq; exact retained stamp (by rw [eq])
    obtain ⟨j,keep⟩ := liftSingle_other (binderDepth relative) index argument.erase other
    simp only [LTerm.erase,Lambda.subst,keep] at shape
    cases shape
private theorem retained_old_lambda
    (oldLookup : body.subterm relative=some old)
    (retained : ∀ stamp,old≠.var stamp (binderDepth relative))
    (currentLookup : (LTerm.contract beta alpha body argument).subterm relative=some (.lam currentStamp currentBody)) :
    ∃ stamp oldBody,old=.lam stamp oldBody := by
  have shape := contract_old_erased_shape oldLookup currentLookup
  cases old with
  | lam stamp oldBody => exact ⟨stamp,oldBody,rfl⟩
  | app => cases shape
  | var stamp index =>
    have other : index≠binderDepth relative := by intro eq; exact retained stamp (by rw [eq])
    obtain ⟨j,keep⟩ := liftSingle_other (binderDepth relative) index argument.erase other
    simp only [LTerm.erase,Lambda.subst,keep] at shape
    cases shape
end Lamping.Lambda.Labelled


namespace Lamping.Lambda.Labelled
private theorem retained_old_variable
    (oldLookup : body.subterm relative=some old)
    (currentLookup : (LTerm.contract beta alpha body argument).subterm relative=some (.var currentStamp index)) :
    ∃ stamp oldIndex,old=.var stamp oldIndex := by
  have shape := contract_old_erased_shape oldLookup currentLookup
  cases old with
  | var stamp oldIndex => exact ⟨stamp,oldIndex,rfl⟩
  | lam => cases shape
  | app => cases shape
private theorem old_function_not_lambda
    (oldLookup : body.subterm relative=some (.app stamp oldFn oldArg))
    (currentLookup : (LTerm.contract beta alpha body argument).subterm relative=some (.app currentStamp currentFn currentArg))
    (notLambda : ∀ l b,currentFn≠.lam l b) : ∀ l b,oldFn≠.lam l b := by
  intro l b shape
  have oldChild : body.subterm (relative++[Step.fn])=some (.lam l b) := by
    rw [LTerm.subterm_append,oldLookup]; simpa only [Option.bind_some,LTerm.subterm] using congrArg some shape
  obtain ⟨newBody,newLookup⟩ := LTerm.subst_lambda_lookup oldChild (LTerm.single (argument.prepend alpha.under))
  have newChild : (LTerm.contract beta alpha body argument).subterm (relative++[Step.fn])=some (.lam l newBody) := by
    rw [LTerm.contract,LTerm.prepend_subterm_nonempty _ _ (by simp)]
    exact newLookup
  have actualChild : (LTerm.contract beta alpha body argument).subterm (relative++[Step.fn])=some currentFn := by
    rw [LTerm.subterm_append,currentLookup]; cases currentFn <;> rfl
  exact notLambda l newBody (Option.some.inj (actualChild.symm.trans newChild))

private theorem subst_retained_node_label
    (t : LTerm) (sigma : Nat → LTerm.SubValue) (selected : Nat)
    (onlyPut : ∀ i value,sigma i=.put value →i=selected)
    (oldLookup : t.subterm relative=some old)
    (retained : ∀ stamp,old≠.var stamp (selected+binderDepth relative)) :
    ∃ current,(t.subst sigma).subterm relative=some current ∧current.label=old.label := by
  induction relative generalizing t sigma selected with
  | nil =>
    have oldEq : t=old := by simpa only [LTerm.subterm,Option.some.injEq] using oldLookup
    subst old
    cases t with
    | app stamp fn arg => exact ⟨_,rfl,rfl⟩
    | lam stamp body => exact ⟨_,rfl,rfl⟩
    | var stamp index =>
      cases hs : sigma index with
      | keep j => exact ⟨.var stamp j,by simp only [LTerm.subst,hs,LTerm.subterm],rfl⟩
      | put value =>
        have eq := onlyPut index value hs
        exact False.elim (retained stamp (by simpa only [binderDepth,Nat.add_zero] using congrArg (LTerm.var stamp) eq))
  | cons child rest ih =>
    cases t with
    | var => cases child <;> simp [LTerm.subterm] at oldLookup
    | app stamp fn arg =>
      cases child with
      | body => simp [LTerm.subterm] at oldLookup
      | fn => exact ih fn sigma selected onlyPut oldLookup retained
      | arg => exact ih arg sigma selected onlyPut oldLookup retained
    | lam stamp body =>
      cases child with
      | fn | arg => simp [LTerm.subterm] at oldLookup
      | body =>
        apply ih body (LTerm.lift sigma) (selected+1) (LTerm.lift_put_index onlyPut) oldLookup
        simpa only [binderDepth,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using retained

theorem contract_retained_node_label
    (oldLookup : body.subterm relative=some old)
    (retained : ∀ stamp,old≠.var stamp (binderDepth relative))
    (currentLookup : (LTerm.contract beta alpha body argument).subterm relative=some current)
    (nonroot : relative≠[]) : current.label=old.label := by
  have onlyPut : ∀ i value,LTerm.single (argument.prepend alpha.under) i=.put value →i=0 := by
    intro i value put
    cases i with
    | zero => rfl
    | succ i => cases put
  obtain ⟨node,lookup,equal⟩ := subst_retained_node_label body
    (LTerm.single (argument.prepend alpha.under)) 0 onlyPut oldLookup (by simpa only [Nat.zero_add] using retained)
  rw [LTerm.contract,LTerm.prepend_subterm_nonempty _ _ nonroot] at currentLookup
  have same : node=current := Option.some.inj (lookup.symm.trans currentLookup)
  exact same ▸ equal

private theorem retained_global_labelAt
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (oldLookup : body.subterm relative=some old)
    (retained : ∀ stamp,old≠.var stamp (binderDepth relative))
    (currentLookup : (LTerm.contract beta alpha body argument).subterm relative=some current)
    (nonroot : relative≠[]) :
    target.labelAt (site++relative)=source.labelAt ((site++[Step.fn,Step.body])++relative) := by
  have labels := contract_retained_node_label oldLookup retained currentLookup nonroot
  simp only [LTerm.labelAt,LTerm.subterm_append,step.contract_lookup redex,redex,Option.bind_some,
    LTerm.subterm,currentLookup,oldLookup,Option.map_some]
  exact congrArg some labels

theorem StepAt.retained_body_prefix_reflect_labelled
    {source target body argument old : LTerm} {site start finish relative ending : Path} {beta alpha : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (segment : PrerequisitePrefix target start before finish)
    (startEq : start=site++relative) (finishEq : finish=site++ending)
    (oldLookup : body.subterm relative=some old)
    (retained : ∀ stamp,old≠.var stamp (binderDepth relative))
    (copyAbsent : ∀ q,ArgumentOccurrence body.erase q → site++q∉before) :
    PrerequisitePrefix source ((site++[Step.fn,Step.body])++relative)
      (before.map (fun edge=>(site++[Step.fn,Step.body])++edge.drop site.length))
      ((site++[Step.fn,Step.body])++ending) ∧
    before.map target.labelAt=
      (before.map (fun edge=>(site++[Step.fn,Step.body])++edge.drop site.length)).map source.labelAt := by
  induction segment generalizing relative old with
  | refl =>
    have sameRelative : relative=ending := List.append_cancel_left (startEq.symm.trans finishEq)
    subst relative
    exact ⟨.refl,rfl⟩
  | @app p a fn arg es endpoint lookup notLambda tail ih =>
    have current : (LTerm.contract beta alpha body argument).subterm relative=some (.app a fn arg) := by
      rw [startEq,LTerm.subterm_append,step.contract_lookup redex,Option.bind_some] at lookup
      exact lookup
    obtain ⟨stamp,oldFn,oldArg,oldShape⟩ := retained_old_app oldLookup retained current
    subst old
    have oldChild : body.subterm (relative++[Step.fn])=some oldFn := by
      rw [LTerm.subterm_append,oldLookup]; cases oldFn <;> rfl
    have childRetained : ∀ stamp,oldFn≠.var stamp (binderDepth (relative++[Step.fn])) := by
      intro stamp selected
      have occurs : ArgumentOccurrence body.erase (relative++[Step.fn]) := by
        change subtermAt body.erase (relative++[Step.fn])=some (.var (binderDepth (relative++[Step.fn])))
        rw [←LTerm.erase_subterm,oldChild,selected]; rfl
      apply copyAbsent (relative++[Step.fn]) occurs
      apply List.mem_cons.mpr
      left
      simp only [startEq,List.append_assoc]
    have absentTail : ∀ q,ArgumentOccurrence body.erase q →site++q∉es := by
      intro q occurs present
      exact copyAbsent q occurs (List.mem_cons_of_mem _ present)
    have nextEq : p++[Step.fn]=site++(relative++[Step.fn]) := by rw [startEq,List.append_assoc]
    have oldTail := ih nextEq finishEq oldChild childRetained absentTail
    have oldCurrent : source.subterm ((site++[Step.fn,Step.body])++relative)=some (.app stamp oldFn oldArg) := by
      rw [List.append_assoc,LTerm.subterm_append,redex]
      simpa only [LTerm.subterm,Option.bind_some] using oldLookup
    have oldTail' : PrerequisitePrefix source (((site++[Step.fn,Step.body])++relative)++[Step.fn])
        (es.map (fun edge=>(site++[Step.fn,Step.body])++edge.drop site.length))
        ((site++[Step.fn,Step.body])++ending) := by simpa only [List.append_assoc] using oldTail.1
    have mappedHead : (site++[Step.fn,Step.body])++(p++[Step.fn]).drop site.length=
        ((site++[Step.fn,Step.body])++relative)++[Step.fn] := by
      rw [nextEq,List.drop_left]; simp only [List.append_assoc]
    refine ⟨?_,?_⟩
    · simp only [List.map_cons]
      rw [mappedHead]
      exact .app oldCurrent (old_function_not_lambda oldLookup current notLambda) oldTail'
    · have currentChild : (LTerm.contract beta alpha body argument).subterm (relative++[Step.fn])=some fn := by
        rw [LTerm.subterm_append,current]; cases fn <;> rfl
      have headLabels := retained_global_labelAt step redex oldChild childRetained currentChild (by simp)
      simp only [List.map_cons]
      congr 1
      · simpa only [nextEq,List.drop_left,List.append_assoc] using headLabels
      · exact oldTail.2
  | @lam parent child a currentBody es endpoint lookup notFunction tail ih =>
    by_cases empty : relative=[]
    · have startAtHead : parent++[child]=site := by simpa only [empty,List.append_nil] using startEq
      have endBound := tail.finish_order_bound
      have atSite : target.subterm site=some (.lam a currentBody) := startAtHead ▸ lookup
      obtain ⟨offset,order⟩ := prerequisiteOrder_subtree atSite
      have atRoot := order []
      have atEnd := order ending
      simp only [List.append_nil,prerequisiteOrder] at atRoot
      rw [←finishEq] at atEnd
      have atChild := lookup
      rw [LTerm.subterm_append] at atChild
      cases atParent : target.subterm parent with
      | none => rw [atParent] at atChild; cases atChild
      | some oldParent =>
        have less := (PrerequisiteDependency.lam atParent lookup notFunction).order_lt
        rw [startAtHead] at less
        omega
    · have current : (LTerm.contract beta alpha body argument).subterm relative=some (.lam a currentBody) := by
        rw [startEq,LTerm.subterm_append,step.contract_lookup redex,Option.bind_some] at lookup
        exact lookup
      obtain ⟨stamp,oldBody,oldShape⟩ := retained_old_lambda oldLookup retained current
      subst old
      obtain ⟨initial,last,relativeEq⟩ := unsnoc_path relative empty
      have lastEq : (site++initial)++[last]=parent++[child] := by
        simpa only [relativeEq,List.append_assoc] using startEq.symm
      obtain ⟨parentEq,childEq⟩ := same_last_step lastEq
      have sourceChild : body.subterm (initial++[child])=some (.lam stamp oldBody) := by
        simpa only [relativeEq,childEq] using oldLookup
      rw [LTerm.subterm_append] at sourceChild
      cases atParent : body.subterm initial with
      | none => rw [atParent] at sourceChild; cases sourceChild
      | some oldParent =>
        have parentRetained : ∀ stamp,oldParent≠.var stamp (binderDepth initial) := by
          intro s shape
          rw [atParent,shape,Option.bind_some] at sourceChild
          cases child <;> cases sourceChild
        have absentTail : ∀ q,ArgumentOccurrence body.erase q →site++q∉es := by
          intro q occurs present
          exact copyAbsent q occurs (List.mem_cons_of_mem _ present)
        have oldTail := ih parentEq.symm finishEq atParent parentRetained absentTail
        have oldCurrent : source.subterm (((site++[Step.fn,Step.body])++initial)++[child])=some (.lam stamp oldBody) := by
          have global : source.subterm ((site++[Step.fn,Step.body])++relative)=some (.lam stamp oldBody) := by
            rw [List.append_assoc,LTerm.subterm_append,redex]
            simpa only [LTerm.subterm,Option.bind_some] using oldLookup
          simpa only [relativeEq,childEq,List.append_assoc] using global
        have mappedHead : (site++[Step.fn,Step.body])++(parent++[child]).drop site.length=
            ((site++[Step.fn,Step.body])++initial)++[child] := by
          rw [startEq,List.drop_left,relativeEq,childEq]; simp only [List.append_assoc]
        refine ⟨?_,?_⟩
        · simp only [List.map_cons]
          rw [mappedHead]
          simpa only [relativeEq,childEq,List.append_assoc] using
            (PrerequisitePrefix.lam oldCurrent notFunction oldTail.1)
        · have headLabels := retained_global_labelAt step redex oldLookup retained current empty
          simp only [List.map_cons]
          congr 1
          · simpa only [startEq,List.drop_left] using headLabels
          · exact oldTail.2
  | @var leaf a index parent origin currentBody rest es endpoint lookup binder split depth tail ih =>
    have current : (LTerm.contract beta alpha body argument).subterm relative=some (.var a index) := by
      rw [startEq,LTerm.subterm_append,step.contract_lookup redex,Option.bind_some] at lookup
      exact lookup
    obtain ⟨stamp,oldIndex,oldShape⟩ := retained_old_variable oldLookup current
    subst old
    have other : oldIndex≠binderDepth relative := by intro eq; exact retained stamp (by rw [eq])
    have currentLeaf : target.subterm (site++relative)=some (.var a (binderDepth rest)) := by
      rw [←startEq,←depth]; exact lookup
    have bindingSplit : site++relative=parent++(.body::rest) := startEq.symm.trans split
    obtain ⟨oldParent,oldStamp,oldBody,oldBinder,oldJump,location⟩ :=
      step.retained_binder_old_prefix redex oldLookup other binder currentLeaf bindingSplit
    rcases location with ⟨inside,parentEq,oldParentEq⟩ | ⟨outside,siteEq,oldParentEq⟩
    · have bodyBinder : body.subterm inside=some (.lam oldStamp oldBody) := by
        rw [oldParentEq,List.append_assoc,LTerm.subterm_append,redex] at oldBinder
        simpa only [LTerm.subterm,Option.bind_some] using oldBinder
      have oldTail := ih parentEq finishEq bodyBinder (by intro s impossible; cases impossible) copyAbsent
      rw [oldParentEq] at oldJump
      exact ⟨by simpa only [List.nil_append] using oldJump.append oldTail.1,oldTail.2⟩
    · have endBound := tail.finish_order_bound
      obtain ⟨offset,order⟩ := prerequisiteOrder_subtree binder
      have atRoot := order []
      have atEnd := order (.body::(outside++ending))
      simp only [List.append_nil,prerequisiteOrder] at atRoot atEnd
      have endPath : endpoint=parent++(.body::(outside++ending)) := by
        rw [finishEq,siteEq,List.append_assoc]; rfl
      rw [←endPath] at atEnd
      omega
end Lamping.Lambda.Labelled

