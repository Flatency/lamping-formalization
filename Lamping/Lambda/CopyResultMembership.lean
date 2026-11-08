import Lamping.Lambda.ContractumPositionOrigins
import Lamping.Lambda.ResultRetainedPrefixTransport
import Lamping.Lambda.CopyChainPrefixTransport
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
private theorem strict_copy_not_site (nonempty : copySite≠[]) :
    ((site++copySite)++relative : Path)≠site := by
  intro equal
  have lengths := congrArg List.length equal
  simp only [List.length_append] at lengths
  exact nonempty (List.eq_nil_of_length_eq_zero (by omega))
/-- A chain from inside an actual copy cannot reach the RESULT reading
without reading that copy's incoming root. External lexical jumps cannot
supply a bypass: their remaining chain excludes the containing lambda body. -/
theorem StepAt.copy_root_on_chain_to_result
    {source target body argument : LTerm} {site copySite start relative : Path} {beta alpha : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (occurs : ArgumentOccurrence body.erase copySite)
    (chain : PrerequisiteChain target start edges)
    (startEq : start=(site++copySite)++relative) (member : site∈edges) :
    site++copySite∈edges := by
  by_cases emptyCopy : copySite=[]
  · simpa only [emptyCopy,List.append_nil] using member
  induction chain generalizing relative with
  | @redex_app p a l b arg lookup =>
    have atSite : site=p++[Step.fn] := by simpa only [List.mem_singleton] using member
    have lengths := congrArg List.length atSite
    have startLengths := congrArg List.length startEq
    simp only [List.length_append,List.length_cons,List.length_nil] at lengths startLengths
    omega
  | @redex_lam p a l b arg lookup =>
    have atSite : site=p++[Step.fn] := by simpa only [List.mem_singleton] using member
    exact False.elim (strict_copy_not_site (relative := relative) emptyCopy (startEq.symm.trans atSite.symm))
  | @app p a fn arg es lookup notLambda tail ih =>
    have nextEq : p++[Step.fn]=(site++copySite)++(relative++[Step.fn]) := by rw [startEq,List.append_assoc]
    have tailMember : site∈es := by
      rcases List.mem_cons.mp member with equal | below
      · exact False.elim (strict_copy_not_site (relative := relative++[Step.fn]) emptyCopy (nextEq.symm.trans equal.symm))
      · exact below
    exact List.mem_cons_of_mem _ (ih nextEq tailMember)
  | @lam parent child a currentBody es lookup notFunction tail ih =>
    by_cases empty : relative=[]
    · have rootEq : parent++[child]=site++copySite := by simpa only [empty,List.append_nil] using startEq
      exact List.mem_cons.mpr (Or.inl rootEq.symm)
    · obtain ⟨initial,last,relativeEq⟩ := unsnoc_path relative empty
      have lastEq : ((site++copySite)++initial)++[last]=parent++[child] := by
        simpa only [relativeEq,List.append_assoc] using startEq.symm
      obtain ⟨parentEq,childEq⟩ := same_last_step lastEq
      have tailMember : site∈es := by
        rcases List.mem_cons.mp member with equal | below
        · exact False.elim (strict_copy_not_site (relative := relative) emptyCopy (startEq.symm.trans equal.symm))
        · exact below
      exact List.mem_cons_of_mem _ (ih parentEq.symm tailMember)
  | @var leaf a index parent origin binderBody rest es lookup binder split depth tail ih =>
    have currentLeaf : target.subterm ((site++copySite)++relative)=some (.var a (binderDepth rest)) := by
      rw [←startEq,←depth]; exact lookup
    have bindingSplit : ((site++copySite)++relative)=parent++(.body::rest) := startEq.symm.trans split
    obtain ⟨oldParent,oldStamp,oldBody,oldBinder,oldJump,location⟩ :=
      step.copied_binder_old_prefix redex occurs binder currentLeaf bindingSplit
    rcases location with ⟨inside,parentEq,oldParentEq⟩ | ⟨outside,siteEq,oldParentEq⟩
    · exact ih parentEq member
    · have absent := tail.excludes_lambda_body (descendant := outside) binder
      have present : parent++(.body::outside)∈es := by simpa only [←siteEq] using member
      exact False.elim (absent present)
end Lamping.Lambda.Labelled
namespace Lamping.Lambda.Labelled
/-- In a retained result lambda, the copy incoming edge must already occur
in the literal BEFORE segment. Nothing is excluded from the whole after. -/
theorem StepAt.copy_start_forces_before_result
    {source target body argument : LTerm} {site copySite start relative : Path} {beta alpha : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (bodyLambda : ∃ stamp inner,body=.lam stamp inner)
    (occurs : ArgumentOccurrence body.erase copySite)
    (chain : PrerequisiteChain target start edges)
    (startEq : start=(site++copySite)++relative) (member : site∈edges) :
    ∃ before after,edges=before++(site::after) ∧PrerequisitePrefix target start before site ∧
      site++copySite∈before := by
  have copyMember := step.copy_root_on_chain_to_result redex occurs chain startEq member
  have insideEq : start=site++(copySite++relative) := by simpa only [List.append_assoc] using startEq
  obtain ⟨before,after,equal,segment,remainder⟩ := chain.split_at_incoming insideEq member
  obtain ⟨stamp,inner,bodyEq⟩ := bodyLambda
  subst body
  have atResult := step.contract_lookup redex
  have lambdaShape : ∃ currentStamp currentBody,target.subterm site=some (.lam currentStamp currentBody) := by
    exact ⟨_,_,atResult⟩
  obtain ⟨currentStamp,currentBody,resultLookup⟩ := lambdaShape
  have copyUnderBody : ∃ rest,copySite=.body::rest := by
    cases copySite with
    | nil => cases occurs
    | cons child rest => cases child with
      | fn | arg => cases occurs
      | body => exact ⟨rest,rfl⟩
  obtain ⟨rest,copyEq⟩ := copyUnderBody
  have absent := remainder.excludes_lambda_body (descendant := rest) resultLookup
  have absentCopy : site++copySite∉site::after := by simpa only [copyEq] using absent
  rw [equal] at copyMember
  rcases List.mem_append.mp copyMember with beforeMember | afterMember
  · exact ⟨before,after,equal,segment,beforeMember⟩
  · exact False.elim (absentCopy afterMember)
end Lamping.Lambda.Labelled
namespace Lamping.Lambda.Labelled
private theorem PrerequisiteChain.start_lookup (chain : PrerequisiteChain t start edges) :
    ∃ current,t.subterm start=some current := by
  cases chain with
  | redex_app lookup => exact ⟨_,lookup⟩
  | redex_lam lookup => exact ⟨_,by rw [LTerm.subterm_append,lookup]; rfl⟩
  | app lookup => exact ⟨_,lookup⟩
  | lam lookup => exact ⟨_,lookup⟩
  | var lookup => exact ⟨_,lookup⟩
private theorem labelled_lookup_of_bare {t : LTerm} {p : Path} {bare : Term} (lookup : subtermAt t.erase p=some bare) :
    ∃ old,t.subterm p=some old ∧old.erase=bare := by
  rw [←LTerm.erase_subterm] at lookup
  exact Option.map_eq_some_iff.mp lookup
/-- The actual first-RESULT restriction rules out a copied start. Thus the
old retained lookup is derived from the supplied current chain, not input. -/
theorem StepAt.first_result_retained_start
    {source target body argument : LTerm} {site start relative : Path} {beta alpha : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (bodyLambda : ∃ stamp inner,body=.lam stamp inner)
    (chain : PrerequisiteChain target start edges)
    (startEq : start=site++relative) (member : site∈edges)
    (firstResult : ∀ before after,edges=before++(site::after) →
      ∀ q,ArgumentOccurrence body.erase q →site++q∉before) :
    ∃ old,body.subterm relative=some old ∧∀ stamp,old≠.var stamp (binderDepth relative) := by
  obtain ⟨current,currentLookup⟩ := chain.start_lookup
  have localLookup : (LTerm.contract beta alpha body argument).subterm relative=some current := by
    rw [startEq,LTerm.subterm_append,step.contract_lookup redex,Option.bind_some] at currentLookup
    exact currentLookup
  have bareLookup : subtermAt (Lambda.contract body.erase argument.erase) relative=some current.erase := by
    rw [←LTerm.erase_contract,←LTerm.erase_subterm,localLookup]; rfl
  rcases subtermAt_contract_origins bareLookup with ⟨oldBare,oldBareLookup,nonvar,_⟩ |
      ⟨k,j,oldBareLookup,other,_,_⟩ | ⟨q,r,split,occurs,_⟩
  · obtain ⟨old,oldLookup,erased⟩ := labelled_lookup_of_bare oldBareLookup
    refine ⟨old,oldLookup,?_⟩
    intro stamp equal
    exact nonvar _ (erased.symm.trans (congrArg LTerm.erase equal))
  · obtain ⟨old,oldLookup,erased⟩ := labelled_lookup_of_bare oldBareLookup
    refine ⟨old,oldLookup,?_⟩
    intro stamp equal
    exact other (Term.var.inj (erased.symm.trans (congrArg LTerm.erase equal)))
  · have copyStart : start=(site++q)++r := by rw [startEq,split,List.append_assoc]
    obtain ⟨before,after,equal,segment,copyBefore⟩ :=
      step.copy_start_forces_before_result redex bodyLambda occurs chain copyStart member
    exact False.elim (firstResult before after equal q occurs copyBefore)

/-- Automatic retained-start version: only the real chain, first RESULT
reading restriction and original body-lambda role are supplied. -/
theorem StepAt.first_result_chain_prefix_reflect_labelled
    {source target body argument : LTerm} {site start relative : Path} {beta alpha : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (bodyLambda : ∃ stamp inner,body=.lam stamp inner)
    (chain : PrerequisiteChain target start edges)
    (startEq : start=site++relative) (member : site∈edges)
    (firstResult : ∀ before after,edges=before++(site::after) →
      ∀ q,ArgumentOccurrence body.erase q →site++q∉before) :
    ∃ before after,edges=before++(site::after) ∧
      PrerequisitePrefix target start before site ∧
      PrerequisiteChain source ((site++[Step.fn,Step.body])++relative)
        ((before.map (fun edge=>(site++[Step.fn,Step.body])++edge.drop site.length))++
          [site++[Step.fn,Step.body],site++[Step.fn]]) ∧
      before.map target.labelAt=
        (before.map (fun edge=>(site++[Step.fn,Step.body])++edge.drop site.length)).map source.labelAt := by
  obtain ⟨old,oldLookup,retained⟩ := step.first_result_retained_start redex bodyLambda chain startEq member firstResult
  exact step.result_retained_chain_prefix_reflect_labelled redex bodyLambda oldLookup retained chain startEq member firstResult
end Lamping.Lambda.Labelled

