import Lamping.Lambda.PrerequisiteChainOrigins
import Lamping.Lambda.RetainedBinderPrefixOrigins
import Lamping.Lambda.PrerequisiteRegionExclusion
namespace Lamping.Lambda.Labelled
private theorem same_last_step {left right : Path} {s u : Step}
    (equal : left++[s]=right++[u]) : left=right ∧s=u := by
  have reversed := congrArg List.reverse equal
  simp only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append] at reversed
  have parts := List.cons.inj reversed
  exact ⟨by simpa only [List.reverse_reverse] using congrArg List.reverse parts.2,parts.1⟩
private theorem LTerm.CopyInterior.app_origin (interior : LTerm.CopyInterior original copy)
    (lookup : copy.subterm relative=some (.app currentStamp currentFn currentArg)) :
    ∃ oldStamp oldFn oldArg rho,original.subterm relative=some (.app oldStamp oldFn oldArg) ∧
      currentFn=oldFn.rename rho := by
  obtain ⟨rho,word,equal⟩ := interior
  cases relative with
  | nil =>
    rw [equal] at lookup
    cases original with
    | var => cases lookup
    | lam => cases lookup
    | app stamp fn arg =>
      have parts := LTerm.app.inj (Option.some.inj lookup)
      exact ⟨stamp,fn,arg,rho,rfl,parts.2.1.symm⟩
  | cons step rest =>
    rw [equal,LTerm.prepend_subterm_nonempty _ _ (by simp)] at lookup
    obtain ⟨tau,atRelative⟩ := LTerm.subterm_rename original rho (step::rest)
    rw [atRelative] at lookup
    obtain ⟨old,atOld,shape⟩ := Option.map_eq_some_iff.mp lookup
    cases old with
    | var => cases shape
    | lam => cases shape
    | app stamp fn arg =>
      have parts := LTerm.app.inj shape
      exact ⟨stamp,fn,arg,tau,atOld,parts.2.1.symm⟩

private theorem copy_root_old_chain
    {source body argument copy : LTerm} {site : Path} {beta alpha stamp : Label}
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (interior : LTerm.CopyInterior argument copy)
    (lookup : copy.subterm []=some (.lam stamp currentBody)) :
    PrerequisiteChain source (site++[Step.arg]) [site++[Step.arg],site++[Step.fn]] := by
  obtain ⟨oldStamp,oldBody,oldLookup,_⟩ := interior.lambda_origin lookup
  have shape : argument=.lam oldStamp oldBody := by simpa only [LTerm.subterm,Option.some.injEq] using oldLookup
  subst argument
  exact copied_lambda_prerequisite redex

end Lamping.Lambda.Labelled

namespace Lamping.Lambda.Labelled
private theorem unsnoc_path (p : Path) (nonempty : p≠[]) : ∃ before last,p=before++[last] := by
  induction p with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail ih =>
    cases tail with
    | nil => exact ⟨[],head,rfl⟩
    | cons next rest =>
      obtain ⟨before,last,equal⟩ := ih (by simp)
      exact ⟨head::before,last,congrArg (head::·) equal⟩

/-- In one actual argument copy, reaching its new incoming edge constructs
an old chain through this beta. No endpoint chain is assumed. -/
theorem StepAt.copy_chain_prefix_reflect
    {source target body argument copy : LTerm} {site copySite start relative : Path} {beta alpha : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (occurs : ArgumentOccurrence body.erase copySite)
    (atCopy : target.subterm (site++copySite)=some copy)
    (chain : PrerequisiteChain target start edges)
    (startEq : start=(site++copySite)++relative)
    (member : site++copySite∈edges) :
    ∃ before after,edges=before++((site++copySite)::after) ∧
      PrerequisitePrefix target start before (site++copySite) ∧
      (∀ edge∈before,∃ inside,inside≠[] ∧edge=(site++copySite)++inside) ∧
      PrerequisiteChain source ((site++[Step.arg])++relative)
        ((before.map (fun edge=>(site++[Step.arg])++edge.drop (site++copySite).length))++
          [site++[Step.arg],site++[Step.fn]]) := by
  have localCopy : (LTerm.contract beta alpha body argument).subterm copySite=some copy := by
    rw [LTerm.subterm_append,step.contract_lookup redex,Option.bind_some] at atCopy
    exact atCopy
  have interior := LTerm.contract_argument_copy_interior occurs localCopy
  have oldArgument : source.subterm (site++[Step.arg])=some argument := by
    rw [LTerm.subterm_append,redex]; cases argument <;> rfl
  induction chain generalizing relative with
  | @redex_app p a l b arg lookup =>
    have same := List.mem_singleton.mp member
    rw [startEq] at same
    have lengths := congrArg List.length same
    simp only [List.length_append,List.length_cons,List.length_nil] at lengths
    omega
  | @redex_lam p a l b arg lookup =>
    have same := List.mem_singleton.mp member
    have lengths := congrArg List.length (same.trans startEq)
    simp only [List.length_append] at lengths
    have empty : relative=[] := List.eq_nil_of_length_eq_zero (by omega)
    subst relative
    have currentLambda : target.subterm (site++copySite)=some (.lam l b) := by
      rw [same,LTerm.subterm_append,lookup]; rfl
    have copyEq : copy=.lam l b := Option.some.inj (atCopy.symm.trans currentLambda)
    have oldChain := copy_root_old_chain redex interior (show copy.subterm []=some (.lam l b) by rw [copyEq]; rfl)
    refine ⟨[],[],?_,?_,?_,?_⟩
    · simp only [List.nil_append]; rw [same]
    · rw [same]; exact .refl
    · intro edge impossible; cases impossible
    · simpa only [List.append_nil,List.map_nil,List.nil_append] using oldChain
  | @app p a fn arg es lookup notLambda tail ih =>
    have headDifferent : site++copySite≠p++[Step.fn] := by
      intro same
      rw [startEq] at same
      have lengths := congrArg List.length same
      simp only [List.length_append,List.length_cons,List.length_nil] at lengths
      omega
    have below : site++copySite∈es := (List.mem_cons.mp member).resolve_left headDifferent
    have nextEq : p++[Step.fn]=(site++copySite)++(relative++[Step.fn]) := by rw [startEq,List.append_assoc]
    obtain ⟨before,after,equal,segment,within,oldTail⟩ := ih nextEq below
    have localNode : copy.subterm relative=some (.app a fn arg) := by
      rw [startEq,LTerm.subterm_append,atCopy,Option.bind_some] at lookup
      exact lookup
    obtain ⟨oldStamp,oldFn,oldArg,rho,atOld,fnEq⟩ := interior.app_origin localNode
    have oldParent : source.subterm ((site++[Step.arg])++relative)=some (.app oldStamp oldFn oldArg) := by
      rw [LTerm.subterm_append,oldArgument,Option.bind_some]; exact atOld
    have oldNotLambda : ∀ l b,oldFn≠.lam l b := by
      intro l b shape
      rw [shape,LTerm.rename] at fnEq
      exact notLambda l _ fnEq
    have oldTail' : PrerequisiteChain source (((site++[Step.arg])++relative)++[Step.fn])
        (before.map (fun edge=>(site++[Step.arg])++edge.drop (site++copySite).length)++
          [site++[Step.arg],site++[Step.fn]]) := by
      simpa only [List.append_assoc] using oldTail
    have mappedHead : (site++[Step.arg])++(p++[Step.fn]).drop (site++copySite).length=
        ((site++[Step.arg])++relative)++[Step.fn] := by
      rw [nextEq,List.drop_left]
      simp only [List.append_assoc]
    refine ⟨(p++[Step.fn])::before,after,by rw [equal]; rfl,.app lookup notLambda segment,?_,?_⟩
    · intro edge appears
      rcases List.mem_cons.mp appears with equal | below
      · subst edge; exact ⟨relative++[Step.fn],by simp,nextEq⟩
      · exact within edge below
    · simp only [List.map_cons,List.cons_append]
      rw [mappedHead]
      exact PrerequisiteChain.app oldParent oldNotLambda oldTail'
  | @lam parent child a currentBody es lookup notFunction tail ih =>
    by_cases empty : relative=[]
    · subst relative
      have same : parent++[child]=site++copySite := by simpa only [List.append_nil] using startEq
      have currentLambda : target.subterm (site++copySite)=some (.lam a currentBody) := same ▸ lookup
      have copyEq : copy=.lam a currentBody := Option.some.inj (atCopy.symm.trans currentLambda)
      have oldChain := copy_root_old_chain redex interior (show copy.subterm []=some (.lam a currentBody) by rw [copyEq]; rfl)
      refine ⟨[],es,?_,?_,?_,?_⟩
      · simp only [List.nil_append]; rw [same]
      · simpa only [same] using (PrerequisitePrefix.refl (t := target) (p := parent++[child]))
      · intro edge impossible; cases impossible
      · simpa only [List.append_nil,List.map_nil,List.nil_append] using oldChain
    · obtain ⟨initial,last,relativeEq⟩ := unsnoc_path relative empty
      have lastEq : ((site++copySite)++initial)++[last]=parent++[child] := by
        simpa only [relativeEq,List.append_assoc] using startEq.symm
      obtain ⟨parentEq,childEq⟩ := same_last_step lastEq
      have headDifferent : site++copySite≠parent++[child] := by
        intro same
        have lengths := congrArg List.length (same.trans startEq)
        simp only [List.length_append] at lengths
        exact empty (List.eq_nil_of_length_eq_zero (by omega))
      have below : site++copySite∈es := (List.mem_cons.mp member).resolve_left headDifferent
      obtain ⟨before,after,equal,segment,within,oldTail⟩ := ih parentEq.symm below
      have localNode : copy.subterm relative=some (.lam a currentBody) := by
        rw [startEq,LTerm.subterm_append,atCopy,Option.bind_some] at lookup
        exact lookup
      obtain ⟨oldStamp,oldBody,atOld,_⟩ := interior.lambda_origin localNode
      have oldCurrent : source.subterm (((site++[Step.arg])++initial)++[child])=some (.lam oldStamp oldBody) := by
        have global : source.subterm ((site++[Step.arg])++relative)=some (.lam oldStamp oldBody) := by
          rw [LTerm.subterm_append,oldArgument,Option.bind_some]; exact atOld
        simpa only [relativeEq,childEq,List.append_assoc] using global
      have mappedHead : (site++[Step.arg])++(parent++[child]).drop (site++copySite).length=
          ((site++[Step.arg])++initial)++[child] := by
        rw [startEq,List.drop_left,relativeEq,childEq]
        simp only [List.append_assoc]
      refine ⟨(parent++[child])::before,after,by rw [equal]; rfl,.lam lookup notFunction segment,?_,?_⟩
      · intro edge appears
        rcases List.mem_cons.mp appears with equal | below
        · subst edge; exact ⟨relative,empty,startEq⟩
        · exact within edge below
      · simp only [List.map_cons,List.cons_append]
        rw [mappedHead]
        simpa only [relativeEq,childEq,List.append_assoc] using
          (PrerequisiteChain.lam oldCurrent notFunction oldTail)
  | @var leaf a index parent origin binderBody rest es lookup binder split depth tail ih =>
    have currentLeaf : target.subterm ((site++copySite)++relative)=some (.var a (binderDepth rest)) := by
      rw [←startEq,←depth]; exact lookup
    have bindingSplit : ((site++copySite)++relative)=parent++(.body::rest) := startEq.symm.trans split
    obtain ⟨oldParent,oldStamp,oldBody,oldBinder,oldJump,location⟩ :=
      step.copied_binder_old_prefix redex occurs binder currentLeaf bindingSplit
    rcases location with ⟨inside,parentEq,oldParentEq⟩ | ⟨outside,siteEq,oldParentEq⟩
    · obtain ⟨before,after,equal,segment,within,oldTail⟩ := ih parentEq member
      rw [oldParentEq] at oldJump
      exact ⟨before,after,equal,.var lookup binder split depth segment,within,by simpa only [List.nil_append] using oldJump.close oldTail⟩
    · have absent := tail.excludes_lambda_body (descendant := outside++copySite) binder
      have present : parent++(.body::(outside++copySite))∈es := by
        simpa only [siteEq,List.append_assoc,List.cons_append,List.nil_append] using member
      exact False.elim (absent present)
end Lamping.Lambda.Labelled





namespace Lamping.Lambda.Labelled
private theorem LTerm.CopyInterior.nonroot_labelAt (interior : LTerm.CopyInterior original copy)
    (nonroot : relative≠[]) : copy.labelAt relative=original.labelAt relative := by
  obtain ⟨rho,word,equal⟩ := interior
  unfold LTerm.labelAt
  rw [equal,LTerm.prepend_subterm_nonempty _ _ nonroot]
  obtain ⟨tau,subtermEq⟩ := LTerm.subterm_rename original rho relative
  rw [subtermEq,Option.map_map]
  simp only [Function.comp_def,LTerm.rename_label]

private theorem copy_prefix_labels
    {source target body argument copy : LTerm} {site copySite : Path} {before : List Path} {beta alpha : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (occurs : ArgumentOccurrence body.erase copySite)
    (atCopy : target.subterm (site++copySite)=some copy)
    (within : ∀ edge∈before,∃ inside,inside≠[] ∧edge=(site++copySite)++inside) :
    before.map target.labelAt=
      (before.map (fun edge=>(site++[Step.arg])++edge.drop (site++copySite).length)).map source.labelAt := by
  have localCopy : (LTerm.contract beta alpha body argument).subterm copySite=some copy := by
    rw [LTerm.subterm_append,step.contract_lookup redex,Option.bind_some] at atCopy
    exact atCopy
  have interior := LTerm.contract_argument_copy_interior occurs localCopy
  have oldArgument : source.subterm (site++[Step.arg])=some argument := by
    rw [LTerm.subterm_append,redex]; cases argument <;> rfl
  rw [List.map_map]
  apply List.map_congr_left
  intro edge member
  obtain ⟨inside,nonroot,edgeEq⟩ := within edge member
  subst edge
  simp only [Function.comp_def,List.drop_left]
  have eq := interior.nonroot_labelAt nonroot
  simpa only [LTerm.labelAt,LTerm.subterm_append,atCopy,oldArgument,Option.bind_some] using eq
end Lamping.Lambda.Labelled

namespace Lamping.Lambda.Labelled
/-- The actual same-copy prefix reflection also preserves its entire ordered
list of incoming labels, derived from strict relative origins internally. -/
theorem StepAt.copy_chain_prefix_reflect_labelled
    {source target body argument copy : LTerm} {site copySite start relative : Path} {beta alpha : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (occurs : ArgumentOccurrence body.erase copySite)
    (atCopy : target.subterm (site++copySite)=some copy)
    (chain : PrerequisiteChain target start edges)
    (startEq : start=(site++copySite)++relative)
    (member : site++copySite∈edges) :
    ∃ before after,edges=before++((site++copySite)::after) ∧
      PrerequisitePrefix target start before (site++copySite) ∧
      (∀ edge∈before,∃ inside,inside≠[] ∧edge=(site++copySite)++inside) ∧
      PrerequisiteChain source ((site++[Step.arg])++relative)
        ((before.map (fun edge=>(site++[Step.arg])++edge.drop (site++copySite).length))++
          [site++[Step.arg],site++[Step.fn]]) ∧
      before.map target.labelAt=
        (before.map (fun edge=>(site++[Step.arg])++edge.drop (site++copySite).length)).map source.labelAt := by
  obtain ⟨before,after,equal,segment,within,oldChain⟩ :=
    step.copy_chain_prefix_reflect redex occurs atCopy chain startEq member
  exact ⟨before,after,equal,segment,within,oldChain,copy_prefix_labels step redex occurs atCopy within⟩
end Lamping.Lambda.Labelled
