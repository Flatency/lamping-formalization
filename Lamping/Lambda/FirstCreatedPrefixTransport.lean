import Lamping.Lambda.FirstCreatedIncoming
import Lamping.Lambda.FunctionResultPrefixTransport
import Lamping.Lambda.CopyFunctionPrefixTransport
import Lamping.Lambda.LambdaReadingPrefixTransport
namespace Lamping.Lambda.Labelled
/-- These are actual beta coordinate changes, not an arbitrary transport. -/
inductive BetaPrefixRegion where
  | context
  | retainedBody
  | copiedArgument (copySite : Path)
def BetaPrefixRegion.reindex (region : BetaPrefixRegion) (site path : Path) : Path :=
  match region with
  | .context => path
  | .retainedBody => (site++[.fn,.body])++path.drop site.length
  | .copiedArgument q => (site++[.arg])++path.drop (site++q).length
private theorem PrerequisiteReads.function_lookup
    (reads : PrerequisiteReads t middle edge) (equal : edge=middle++[.fn]) :
    ∃ stamp fn arg,t.subterm middle=some (.app stamp fn arg) := by
  rcases reads with ⟨stamp,fn,arg,lookup,_⟩ | ⟨stamp,body,lookup,edgeEq⟩
  · exact ⟨stamp,fn,arg,lookup⟩
  · have sizeEq := congrArg List.length (edgeEq.symm.trans equal)
    simp only [List.length_append,List.length_cons,List.length_nil] at sizeEq
    omega
private theorem PrerequisiteReads.lambda_lookup
    (reads : PrerequisiteReads t middle edge) (equal : middle=edge) :
    ∃ stamp body,t.subterm edge=some (.lam stamp body) := by
  rcases reads with ⟨stamp,fn,arg,lookup,edgeEq⟩ | ⟨stamp,body,lookup,edgeEq⟩
  · have sizeEq := congrArg List.length (equal.trans edgeEq)
    simp only [List.length_append,List.length_cons,List.length_nil] at sizeEq
    omega
  · exact ⟨stamp,body,by simpa only [equal] using lookup⟩
end Lamping.Lambda.Labelled
namespace Lamping.Lambda.Labelled
/-- Full old-prefix reflection for the actual computed first-created reading.
The other old endpoint is only an occurrence and never needs its own chain. -/
theorem StepAt.first_created_prefix_of_reading
    {source target body argument : LTerm} {site start : Path} {beta alpha : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (chain : PrerequisiteChain target start edges)
    (computed : firstCreatedCut body site edges=some (before,edge,after))
    (segment : PrerequisitePrefix target start before middle)
    (reads : PrerequisiteReads target middle edge)
    (origin : BetaIncomingReadingOrigin body argument site edge middle oldMiddle first last) :
    ∃ region : BetaPrefixRegion,
      PrerequisiteChain source (region.reindex site start)
        (before.map (region.reindex site)++[first,site++[.fn]]) ∧
      before.map target.labelAt=(before.map (region.reindex site)).map source.labelAt := by
  obtain ⟨equal,created,unread⟩ := firstCreatedCut_sound computed
  have member : edge∈edges := by rw [equal]; exact List.mem_append_right _ List.mem_cons_self
  obtain ⟨resultUnread,copiesUnread⟩ := first_created_unread_heads unread
  cases origin with
  | resultFunction result function =>
    obtain ⟨stamp,fn,arg,atParent⟩ := reads.function_lookup (result.trans function)
    obtain ⟨oldChain,labels⟩ := step.function_result_prefix_old_chain redex function atParent segment
    have mapEq : before.map (BetaPrefixRegion.context.reindex first)=before := by
      change before.map (fun x=>x)=before
      exact List.map_id before
    refine ⟨.context,?_,?_⟩
    · rw [mapEq]; exact oldChain
    · rw [mapEq]; exact labels
  | @resultLambda stamp inner result reading oldLambda =>
    have atResult := reads.lambda_lookup (reading.trans result.symm)
    obtain ⟨currentStamp,currentBody,atResult⟩ := atResult
    rw [result] at atResult
    have reading' : PrerequisitePrefix target start before last := by simpa only [reading] using segment
    obtain ⟨relative,startEq⟩ := reading'.lambda_finish_contains_start atResult
    have firstResult := chain.first_created_result_before (by simpa only [result] using computed)
    obtain ⟨old,oldLookup,retained⟩ := step.first_result_retained_start redex
      ⟨stamp,inner,oldLambda⟩ chain startEq (result ▸ member) firstResult
    obtain ⟨oldPrefix,labels⟩ := step.retained_body_prefix_reflect_labelled redex
      (ending := []) reading' startEq (by simp) oldLookup retained copiesUnread
    simp only [List.append_nil] at oldPrefix
    have oldTail := result_lambda_prerequisite (oldLambda ▸ redex)
    refine ⟨.retainedBody,?_,?_⟩
    · simpa only [BetaPrefixRegion.reindex,startEq,List.drop_left] using oldPrefix.close oldTail
    · exact labels
  | @copyFunction parent occurs copy reading =>
    obtain ⟨stamp,fn,arg,atParent⟩ := reads.function_lookup (by rw [copy,reading]; simp only [List.append_assoc])
    rw [reading] at atParent segment
    obtain ⟨relative,startEq,oldChain,labels⟩ := step.copy_function_prefix_reflect_labelled
      redex occurs atParent segment resultUnread copiesUnread
    refine ⟨.retainedBody,?_,labels⟩
    simpa only [BetaPrefixRegion.reindex,startEq,List.drop_left] using oldChain
  | @copyLambda q stamp inner occurs copy reading oldLambda =>
    obtain ⟨currentStamp,currentBody,atCopy⟩ := reads.lambda_lookup reading
    rw [copy] at atCopy
    have segment' : PrerequisitePrefix target start before (site++q) := by simpa only [reading,copy] using segment
    obtain ⟨relative,startEq⟩ := segment'.lambda_finish_contains_start atCopy
    obtain ⟨otherBefore,otherAfter,otherEqual,otherSegment,within,oldChain,labels⟩ :=
      step.copy_chain_prefix_reflect_labelled redex occurs atCopy chain startEq (copy ▸ member)
    have equal' : edges=before++((site++q)::after) := by simpa only [copy] using equal
    obtain ⟨beforeEq,afterEq⟩ := chain.first_created_split_unique equal' otherEqual
    subst otherBefore
    refine ⟨.copiedArgument q,?_,labels⟩
    simpa only [BetaPrefixRegion.reindex,startEq,List.drop_left] using oldChain
end Lamping.Lambda.Labelled
namespace Lamping.Lambda.Labelled
/-- The first-created prefix and its whole old chain are constructed from
THIS target chain. No caller start coordinate, reading, old chain or unread
before certificate remains. The old last endpoint may be auxiliary. -/
theorem StepAt.first_created_prefix_reflect
    {source target body argument : LTerm} {site start : Path} {beta alpha : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (chain : PrerequisiteChain target start edges)
    (hasCreated : ∃ edge∈edges,BetaCreatedIncoming body site edge) :
    ∃ before edge after middle oldMiddle first last,∃ region : BetaPrefixRegion,
      firstCreatedCut body site edges=some (before,edge,after) ∧
      edges=before++(edge::after) ∧PrerequisitePrefix target start before middle ∧
      PrerequisiteChain target middle (edge::after) ∧PrerequisiteReads target middle edge ∧
      BetaIncomingReadingOrigin body argument site edge middle oldMiddle first last ∧
      PrerequisiteChain source (region.reindex site start)
        (before.map (region.reindex site)++[first,site++[.fn]]) ∧
      before.map target.labelAt=(before.map (region.reindex site)).map source.labelAt ∧
      (∃ oldLast,source.subterm last=some oldLast) ∧
      BetaCreatedIncoming body site edge ∧∀ old∈before,¬BetaCreatedIncoming body site old := by
  obtain ⟨before,edge,after,middle,oldMiddle,first,last,computed,equal,segment,remainder,
      reads,origin,oldTwo,lastLookup,created,unread⟩ :=
    step.first_created_reading_origins redex chain hasCreated
  obtain ⟨region,oldChain,labels⟩ :=
    step.first_created_prefix_of_reading redex chain computed segment reads origin
  exact ⟨before,edge,after,middle,oldMiddle,first,last,region,computed,equal,segment,
    remainder,reads,origin,oldChain,labels,lastLookup,created,unread⟩
end Lamping.Lambda.Labelled