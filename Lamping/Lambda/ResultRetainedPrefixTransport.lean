import Lamping.Lambda.RetainedBodyPrefixTransport
namespace Lamping.Lambda.Labelled
/-- Starting inside an incoming edge's subtree forces its member to be
read at that subtree's node, not at the parent application's other end. -/
theorem PrerequisiteChain.split_at_incoming
    (chain : PrerequisiteChain t start edges) (startEq : start=site++relative) (member : site∈edges) :
    ∃ before after,edges=before++(site::after) ∧PrerequisitePrefix t start before site ∧
      PrerequisiteChain t site (site::after) := by
  obtain ⟨before,after,middle,equal,segment,remainder,reading⟩ := chain.split_at_member member
  rcases reading with ⟨stamp,fn,arg,atMiddle,edgeEq⟩ | ⟨stamp,body,atMiddle,edgeEq⟩
  · have bound := segment.finish_order_bound
    have less := prerequisiteOrder_function_descendant atMiddle relative
    rw [←edgeEq,←startEq] at less
    omega
  · subst site
    exact ⟨before,after,equal,segment,remainder⟩

private theorem result_prefix_reflect_aux
    {source target body argument old : LTerm} {site start finish relative : Path} {beta alpha : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (bodyLambda : ∃ stamp inner,body=.lam stamp inner)
    (segment : PrerequisitePrefix target start before finish)
    (startEq : start=site++relative) (finishEq : finish=site)
    (oldLookup : body.subterm relative=some old)
    (retained : ∀ stamp,old≠.var stamp (binderDepth relative))
    (copyAbsent : ∀ q,ArgumentOccurrence body.erase q → site++q∉before) :
    PrerequisiteChain source ((site++[Step.fn,Step.body])++relative)
      ((before.map (fun edge=>(site++[Step.fn,Step.body])++edge.drop site.length))++
        [site++[Step.fn,Step.body],site++[Step.fn]]) ∧
    before.map target.labelAt=
      (before.map (fun edge=>(site++[Step.fn,Step.body])++edge.drop site.length)).map source.labelAt := by
  obtain ⟨oldPrefix,labels⟩ := step.retained_body_prefix_reflect_labelled redex segment startEq
    (ending := []) (by simpa only [List.append_nil] using finishEq) oldLookup retained copyAbsent
  have oldPrefix' : PrerequisitePrefix source ((site++[Step.fn,Step.body])++relative)
      (before.map (fun edge=>(site++[Step.fn,Step.body])++edge.drop site.length))
      (site++[Step.fn,Step.body]) := by simpa only [List.append_nil] using oldPrefix
  have oldTail : PrerequisiteChain source (site++[Step.fn,Step.body])
      [site++[Step.fn,Step.body],site++[Step.fn]] := by
    obtain ⟨stamp,inner,bodyEq⟩ := bodyLambda
    rw [bodyEq] at redex
    exact result_lambda_prerequisite redex
  exact ⟨oldPrefix'.close oldTail,labels⟩
end Lamping.Lambda.Labelled

namespace Lamping.Lambda.Labelled
/-- A real first-new RESULT reading reflects the retained body prefix.
The no-copy restriction concerns only literal before segments, never after. -/
theorem StepAt.result_retained_chain_prefix_reflect
    {source target body argument old : LTerm} {site start relative : Path} {beta alpha : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (bodyLambda : ∃ stamp inner,body=.lam stamp inner)
    (oldLookup : body.subterm relative=some old)
    (retained : ∀ stamp,old≠.var stamp (binderDepth relative))
    (chain : PrerequisiteChain target start edges)
    (startEq : start=site++relative) (member : site∈edges)
    (firstResult : ∀ before after,edges=before++(site::after) →
      ∀ q,ArgumentOccurrence body.erase q →site++q∉before) :
    ∃ before after,edges=before++(site::after) ∧
      PrerequisitePrefix target start before site ∧
      PrerequisiteChain source ((site++[Step.fn,Step.body])++relative)
        ((before.map (fun edge=>(site++[Step.fn,Step.body])++edge.drop site.length))++
          [site++[Step.fn,Step.body],site++[Step.fn]]) := by
  obtain ⟨before,after,equal,segment,remainder⟩ := chain.split_at_incoming startEq member
  exact ⟨before,after,equal,segment,(result_prefix_reflect_aux step redex bodyLambda segment startEq
    rfl oldLookup retained (firstResult before after equal)).1⟩
end Lamping.Lambda.Labelled

namespace Lamping.Lambda.Labelled
/-- The retained RESULT reflection preserves the entire ordered before-label list. -/
theorem StepAt.result_retained_chain_prefix_reflect_labelled
    {source target body argument old : LTerm} {site start relative : Path} {beta alpha : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (bodyLambda : ∃ stamp inner,body=.lam stamp inner)
    (oldLookup : body.subterm relative=some old)
    (retained : ∀ stamp,old≠.var stamp (binderDepth relative))
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
  obtain ⟨before,after,equal,segment,remainder⟩ := chain.split_at_incoming startEq member
  obtain ⟨oldChain,labels⟩ := result_prefix_reflect_aux step redex bodyLambda segment startEq
    rfl oldLookup retained (firstResult before after equal)
  exact ⟨before,after,equal,segment,oldChain,labels⟩
end Lamping.Lambda.Labelled

