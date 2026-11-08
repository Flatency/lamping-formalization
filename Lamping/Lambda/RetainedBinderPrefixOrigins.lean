import Lamping.Lambda.CopiedBinderPrefixOrigins
namespace Lamping.Lambda
/-- Exact protected-versus-decremented index of a real nonselected slot. -/
theorem liftSingle_retained_index {argument : Term} {depth index current : Nat}
    (other : index≠depth) (value : liftSubN depth (singleSub argument) index=.var current) :
    (index<depth ∧current=index) ∨ (depth<index ∧current+1=index) := by
  induction depth generalizing index current with
  | zero =>
    cases index with
    | zero => exact False.elim (other rfl)
    | succ index => right; constructor; omega; have same := Term.var.inj value; omega
  | succ depth ih =>
    cases index with
    | zero => left; exact ⟨by omega,(Term.var.inj value).symm⟩
    | succ index =>
      obtain ⟨prior,priorEq⟩ := liftSingle_other depth index argument (by omega)
      have currentEq : prior+1=current := by
        simpa only [liftSubN,liftSub,priorEq,rename,Term.var.injEq] using value
      rcases ih (by omega) priorEq with ⟨inside,same⟩ | ⟨outside,same⟩
      · left; omega
      · right; omega
end Lamping.Lambda
namespace Lamping.Lambda.Labelled
/-- A genuine variable whose index is internal to its literal path supplies
its actual lexical lambda even when the whole term is open or non-INIT. -/
private theorem internal_variable_binder {t : LTerm} {p : Path} {stamp : Label}
    (lookup : t.subterm p=some (.var stamp index)) (inside : index<binderDepth p) :
    ∃ parent rest origin body,p=parent++(.body::rest) ∧
      t.subterm parent=some (.lam origin body) ∧index=binderDepth rest := by
  obtain ⟨env,ctx,atSite⟩ := SourceSubterm.of_lookup t lookup [] .external
  have lengths := atSite.env_length
  have bound : index<env.length := by simp only [List.length_nil,Nat.zero_add] at lengths; omega
  cases entry : env[index]? with
  | none => have outside := List.getElem?_eq_none_iff.mp entry; omega
  | some origin =>
    obtain ⟨parent,rest,body,split,atParent,depth⟩ := atSite.bound_binder_occurrence entry
    exact ⟨parent,rest,origin,body,split,atParent,depth⟩
end Lamping.Lambda.Labelled
namespace Lamping.Lambda
private theorem binding_above_prefix {site relative parent rest : Path}
    (split : site++relative=parent++(.body::rest)) (external : binderDepth relative≤binderDepth rest) :
    ∃ outside,site=parent++(.body::outside) := by
  have depthEq := congrArg binderDepth split
  simp only [binderDepth_append,binderDepth] at depthEq
  have above : binderDepth parent<binderDepth site := by omega
  have comparable : site <+: parent ∨parent <+: site :=
    List.prefix_or_prefix_of_prefix (l₃ := site++relative) ⟨relative,rfl⟩ ⟨.body::rest,split.symm⟩
  rcases comparable with ⟨suffix,eq⟩ | ⟨suffix,eq⟩
  · have depths := congrArg binderDepth eq; rw [binderDepth_append] at depths; omega
  · cases suffix with
    | nil => simp only [List.append_nil] at eq; have depths := congrArg binderDepth eq; omega
    | cons step tail =>
      have same : (step::tail)++relative=.body::rest := by
        apply List.append_cancel_left (as := parent)
        rw [←List.append_assoc,eq]
        exact split
      have headEq := (List.cons.inj same).1
      subst step
      exact ⟨tail,eq.symm⟩
end Lamping.Lambda
namespace Lamping.Lambda.Labelled
/-- A genuine retained (nonselected) body variable supplies its old binder
jump, either to its retained body lambda or to the unchanged outer lambda. -/
theorem StepAt.retained_binder_old_prefix
    {source target body argument binderBody : LTerm}
    {site relative parent rest : Path} {beta alpha binderStamp oldStamp leafStamp : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (oldLeaf : body.subterm relative=some (.var oldStamp oldIndex))
    (other : oldIndex≠binderDepth relative)
    (atBinder : target.subterm parent=some (.lam binderStamp binderBody))
    (atLeaf : target.subterm (site++relative)=some (.var leafStamp (binderDepth rest)))
    (split : site++relative=parent++(.body::rest)) :
    ∃ oldParent origin oldBody,
      source.subterm oldParent=some (.lam origin oldBody) ∧
      PrerequisitePrefix source ((site++[.fn,.body])++relative) [] oldParent ∧
      ((∃ inside,parent=site++inside ∧ oldParent=((site++[.fn,.body])++inside)) ∨ (∃ outside,site=parent++(.body::outside) ∧oldParent=parent)) := by
  have bareRedex : subtermAt source.erase site=some (.app (.lam body.erase) argument.erase) := by
    rw [←LTerm.erase_subterm,redex]; rfl
  have oldBare : subtermAt body.erase relative=some (.var oldIndex) := by
    rw [←LTerm.erase_subterm,oldLeaf]; rfl
  have currentBare : subtermAt (Lambda.contract body.erase argument.erase) relative=some (.var (binderDepth rest)) := by
    have current : subtermAt target.erase (site++relative)=some (.var (binderDepth rest)) := by
      rw [←LTerm.erase_subterm,atLeaf]; rfl
    rw [subtermAt_append,step.betaAt.contract_lookup bareRedex,Option.bind_some] at current
    exact current
  have substituted := subtermAt_subst oldBare (singleSub argument.erase)
  change subtermAt (Lambda.contract body.erase argument.erase) relative=
    some (liftSubN (binderDepth relative) (singleSub argument.erase) oldIndex) at substituted
  have value := Option.some.inj (substituted.symm.trans currentBare)
  have globalLeaf : source.subterm ((site++[.fn,.body])++relative)=some (.var oldStamp oldIndex) := by
    rw [List.append_assoc,LTerm.subterm_append,redex]
    simpa only [LTerm.subterm,Option.bind_some] using oldLeaf
  rcases Lambda.liftSingle_retained_index other value with ⟨inside,indexEq⟩ | ⟨outside,indexEq⟩
  · obtain ⟨oldParent,oldRest,origin,oldBody,bodySplit,bodyBinder,oldDepth⟩ :=
      internal_variable_binder oldLeaf inside
    have samePath : (site++oldParent)++(.body::oldRest)=parent++(.body::rest) := by
      rw [List.append_assoc,←bodySplit]; exact split
    have same := binding_prefix_depth_unique samePath (oldDepth.symm.trans indexEq.symm)
    have globalBinder : source.subterm ((site++[.fn,.body])++oldParent)=some (.lam origin oldBody) := by
      rw [List.append_assoc,LTerm.subterm_append,redex]
      simpa only [LTerm.subterm,Option.bind_some] using bodyBinder
    refine ⟨(site++[.fn,.body])++oldParent,origin,oldBody,globalBinder,?_,Or.inl ⟨oldParent,same.1.symm,rfl⟩⟩
    apply PrerequisitePrefix.var (rest := oldRest) globalLeaf globalBinder
    · simp only [bodySplit,List.append_assoc]
    · exact oldDepth
    · exact .refl
  · have external : binderDepth relative≤binderDepth rest := by omega
    obtain ⟨outsidePath,siteEq⟩ := Lambda.binding_above_prefix split external
    obtain ⟨suffix,oldBody,_,oldBinder⟩ := step.strict_lambda_ancestor atBinder siteEq (by simp)
    have restEq : rest=outsidePath++relative := by
      have equal : (.body::rest)=.body::(outsidePath++relative) := by
        apply List.append_cancel_left (as := parent)
        simpa only [siteEq,List.append_assoc] using split.symm
      exact (List.cons.inj equal).2
    have restDepth := congrArg binderDepth restEq
    refine ⟨parent,binderStamp,oldBody,oldBinder,?_,Or.inr ⟨outsidePath,siteEq,rfl⟩⟩
    apply PrerequisitePrefix.var (rest := outsidePath++(.fn::.body::relative)) globalLeaf oldBinder
    · simp only [siteEq,List.append_assoc,List.cons_append,List.nil_append]
    · simp only [binderDepth_append,binderDepth] at *; omega
    · exact .refl
end Lamping.Lambda.Labelled



