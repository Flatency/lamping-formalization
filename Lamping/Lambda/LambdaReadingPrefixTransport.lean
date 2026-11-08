import Lamping.Lambda.LambdaPrefixContainment
import Lamping.Lambda.CopyResultMembership
namespace Lamping.Lambda.Labelled
/-- A supplied actual COPY-lambda reading determines its start's copy-relative
coordinate internally; no source lookup, old chain or start coordinate is input. -/
theorem StepAt.copy_lambda_reading_prefix_reflect
    {source target body argument currentBody : LTerm} {site copySite start : Path}
    {beta alpha currentStamp : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (occurs : ArgumentOccurrence body.erase copySite)
    (atCopy : target.subterm (site++copySite)=some (.lam currentStamp currentBody))
    (chain : PrerequisiteChain target start edges) (member : site++copySite∈edges)
    (reading : PrerequisitePrefix target start preceding (site++copySite)) :
    ∃ relative before after,start=(site++copySite)++relative ∧
      edges=before++((site++copySite)::after) ∧
      PrerequisitePrefix target start before (site++copySite) ∧
      PrerequisiteChain source ((site++[Step.arg])++relative)
        ((before.map (fun edge=>(site++[Step.arg])++edge.drop (site++copySite).length))++
          [site++[Step.arg],site++[Step.fn]]) ∧
      before.map target.labelAt=
        (before.map (fun edge=>(site++[Step.arg])++edge.drop (site++copySite).length)).map source.labelAt := by
  obtain ⟨relative,startEq⟩ := reading.lambda_finish_contains_start atCopy
  obtain ⟨before,after,equal,segment,within,oldChain,labels⟩ :=
    step.copy_chain_prefix_reflect_labelled redex occurs atCopy chain startEq member
  exact ⟨relative,before,after,startEq,equal,segment,oldChain,labels⟩

/-- A real RESULT-lambda reading is either a retained body lambda or the
root copy overlap. Its relative start and old root are both derived inside. -/
theorem StepAt.result_lambda_reading_prefix_reflect
    {source target body argument currentBody : LTerm} {site start : Path}
    {beta alpha currentStamp : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (atResult : target.subterm site=some (.lam currentStamp currentBody))
    (chain : PrerequisiteChain target start edges) (member : site∈edges)
    (reading : PrerequisitePrefix target start preceding site)
    (firstResult : ∀ before after,edges=before++(site::after) →
      ∀ q,ArgumentOccurrence body.erase q →site++q∉before) :
    ∃ relative oldRoot before after,start=site++relative ∧
      ((oldRoot=site++[Step.fn,Step.body] ∧∃ stamp inner,body=.lam stamp inner) ∨
        (oldRoot=site++[Step.arg] ∧∃ stamp argStamp argBody,
          body=.var stamp 0 ∧argument=.lam argStamp argBody)) ∧
      edges=before++(site::after) ∧PrerequisitePrefix target start before site ∧
      PrerequisiteChain source (oldRoot++relative)
        ((before.map (fun edge=>oldRoot++edge.drop site.length))++[oldRoot,site++[Step.fn]]) ∧
      before.map target.labelAt=
        (before.map (fun edge=>oldRoot++edge.drop site.length)).map source.labelAt := by
  obtain ⟨relative,startEq⟩ := reading.lambda_finish_contains_start atResult
  have shape : LTerm.contract beta alpha body argument=.lam currentStamp currentBody :=
    Option.some.inj ((step.contract_lookup redex).symm.trans atResult)
  rcases LTerm.contract_root_lambda_origin shape with ⟨oldStamp,oldBody,bodyEq,_⟩ |
      ⟨variableStamp,argumentStamp,argumentBody,bodyEq,argumentEq,_⟩
  · obtain ⟨before,after,equal,segment,oldChain,labels⟩ :=
      step.first_result_chain_prefix_reflect_labelled redex ⟨oldStamp,oldBody,bodyEq⟩ chain startEq member firstResult
    exact ⟨relative,site++[Step.fn,Step.body],before,after,startEq,Or.inl ⟨rfl,oldStamp,oldBody,bodyEq⟩,equal,segment,oldChain,labels⟩
  · have occurs : ArgumentOccurrence body.erase [] := by rw [bodyEq]; rfl
    have atCopy : target.subterm (site++[])=some (.lam currentStamp currentBody) := by
      simpa only [List.append_nil] using atResult
    obtain ⟨before,after,equal,segment,within,oldChain,labels⟩ :=
      step.copy_chain_prefix_reflect_labelled redex occurs atCopy chain (by simpa only [List.append_nil] using startEq)
        (by simpa only [List.append_nil] using member)
    refine ⟨relative,site++[Step.arg],before,after,startEq,Or.inr ⟨rfl,variableStamp,argumentStamp,argumentBody,bodyEq,argumentEq⟩,?_,?_,?_,?_⟩
    · simpa only [List.append_nil] using equal
    · simpa only [List.append_nil] using segment
    · simpa only [List.append_nil] using oldChain
    · simpa only [List.append_nil] using labels
end Lamping.Lambda.Labelled
