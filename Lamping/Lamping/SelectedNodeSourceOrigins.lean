import Lamping.Lambda.NodeIncomingFirstCreation
import Lamping.Lambda.UncreatedSourceHistory
import Lamping.Lambda.ResidualFunctionPreimages
import Lamping.Lamping.AuxiliaryEndpointAvailability
import Lamping.Lambda.NodeLabelSuffixOrigins
namespace Lamping.Lambda.Labelled
open Marked
/-- Synchronous schedule bookkeeping on an ALREADY actual first event.
There is no new origin/earliest induction or caller selected-name certificate. -/
theorem NodeIncomingFirstCreation.old_split
    {F ps pre : List Path} {site : Path} {post : List Path} {m n : Marked}
    {source target : LTerm} {labels : Labelled.History ps source target} {p oldEdge : Path}
    (first : NodeIncomingFirstCreation labels p oldEdge pre site post)
    (old : RelativeOldHistory F ps m n) :
    ∃before after,RelativeOldHistory F pre m before ∧ReductionAt site before after ∧
      site∈setResidualPositions F before ∧RelativeOldHistory F post after n := by
  induction first generalizing m n with
  | here =>
    cases old with
    | cons reduction member tail => exact ⟨_,_,.nil _,reduction,member,tail⟩
  | later redex origin uncreated tail ih =>
    cases old with
    | cons reduction member rest =>
      obtain ⟨before,after,earlier,event,inside,later⟩ := ih rest
      exact ⟨before,after,.cons reduction member earlier,event,inside,later⟩
end Lamping.Lambda.Labelled

namespace Lamping.AG
open Lambda Lambda.Labelled SyntaxIncidence
private theorem source_at_original_selected_name
    {pre : List Path} {source before node body argument originalBody originalArg : LTerm}
    {labels : History pre source before} {site name beforeEdge oldEdge : Path}
    {beta alpha originalBeta originalAlpha : Label}
    (redex : before.subterm site=some (.app beta (.lam alpha body) argument))
    (originalRedex : source.subterm name=some (.app originalBeta (.lam originalAlpha originalBody) originalArg))
    (appTrace : BetaNodeHistoryPreimage labels site name)
    (fnTrace : BetaNodeHistoryPreimage labels (site++[.fn]) (name++[.fn]))
    (uncreated : UncreatedNodeHistoryPreimage labels beforeEdge oldEdge)
    (lookup : before.subterm beforeEdge=some node)
    (root : beforeEdge=site++[.fn,.body] ∨beforeEdge=site++[.arg]) :
    ∃original vertex,source.subterm oldEdge=some original ∧
      Source source oldEdge (some vertex) ∧
      (vertex.val=name ∨vertex.val=name++[.fn]) ∧
      EndpointChain source (some vertex) [name++[.fn]] := by
  rcases root with retained |copied
  · let parent : ProperPosition before := ⟨site++[.fn],Or.inr ⟨alpha,body,by rw [LTerm.subterm_append,redex];rfl⟩⟩
    have endpoint : Source before beforeEdge (some parent) :=
      ⟨.body,.lam alpha body,.lamBody alpha,
        by change beforeEdge=(site++[Step.fn])++[Step.body];simpa only [List.append_assoc] using retained,
        by rw [LTerm.subterm_append,redex];rfl,.body⟩
    obtain ⟨original,vertex,atOriginal,sameLabel,sourceSpec,vertexTrace⟩ :=
      uncreated.source_history lookup endpoint
    cases vertexTrace with
    | @proper current old trace =>
      have same : old.val=name++[.fn] := trace.unique fnTrace
      refine ⟨original,old,atOriginal,sourceSpec,Or.inr same,?_⟩
      change PrerequisiteChain source old.val [name++[Step.fn]]
      rw [same]
      exact PrerequisiteChain.redex_lam originalRedex
  · let parent : ProperPosition before := ⟨site,Or.inl ⟨beta,.lam alpha body,argument,redex⟩⟩
    have endpoint : Source before beforeEdge (some parent) :=
      ⟨.arg,.app beta (.lam alpha body) argument,.appArg beta,copied,redex,.arg⟩
    obtain ⟨original,vertex,atOriginal,sameLabel,sourceSpec,vertexTrace⟩ :=
      uncreated.source_history lookup endpoint
    cases vertexTrace with
    | @proper current old trace =>
      have same : old.val=name := trace.unique appTrace
      refine ⟨original,old,atOriginal,sourceSpec,Or.inl same,?_⟩
      change PrerequisiteChain source old.val [name++[Step.fn]]
      rw [same]
      exact PrerequisiteChain.redex_app originalRedex

/-- Internal assembly from the actual first creation certificate. All source
coordinates come from incidence and residual-node traces, not equal labels. -/
private theorem first_creation_selected_source
    {F ps pre : List Path} {site : Path} {post : List Path} {n : Lambda.Marked}
    {source target current : LTerm} {labels : History ps source target} {p oldEdge : Path}
    (first : NodeIncomingFirstCreation labels p oldEdge pre site post)
    (old : Marked.RelativeOldHistory F ps (Marked.mark F source.erase) n)
    (lookup : target.subterm p=some current) :
    ∃name∈F,∃beta alpha body argument,
      source.subterm name=some (.app beta (.lam alpha body) argument) ∧
      ∃original vertex,source.subterm oldEdge=some original ∧
        Source source oldEdge (some vertex) ∧
        (vertex.val=name ∨vertex.val=name++[.fn]) ∧
        EndpointChain source (some vertex) [name++[.fn]] := by
  obtain ⟨schedule,before,after,bp,ap,body,argument,beta,alpha,earlierLabels,event,suffix,
      redex,uncreated,origin,created,tailTrace⟩ := first.split
  obtain ⟨markedBefore,markedAfter,oldPrefix,markedEvent,member,oldSuffix⟩ := first.old_split old
  obtain ⟨name,chosen,originalRedex,appTrace,fnTrace⟩ :=
    oldPrefix.selected_app_function_preimages earlierLabels member
  obtain ⟨originalBeta,originalAlpha,originalBody,originalArg,atOriginalRedex⟩ := originalRedex
  obtain ⟨ap',afterNode,atAfter,afterTrace⟩ := suffix.node_preimage_from_lookup lookup
  have samePosition := afterTrace.unique tailTrace
  subst ap'
  obtain ⟨beforeNode,atBefore,_⟩ := event.preimage_node_constructor redex origin atAfter
  obtain ⟨original,vertex,atOriginal,endpoint,position,chain⟩ :=
    source_at_original_selected_name redex atOriginalRedex appTrace fnTrace uncreated atBefore
      (created_old_edge_root origin created)
  exact ⟨name,chosen,originalBeta,originalAlpha,originalBody,originalArg,atOriginalRedex,
    original,vertex,atOriginal,endpoint,position,chain⟩

/-- A marked incoming node in an actual OLD schedule has its original Source
at an original selected APP or FUNCTION lambda. Only the ORIGINAL source is
safe. This is source identity and a real singleton, not an endpoint iso or REP. -/
theorem marked_node_source_selected
    {F ps : List Path} {n : Lambda.Marked} {source target current : LTerm}
    {labels : History ps source target} {p oldEdge : Path} {alpha : Label}
    (old : Marked.RelativeOldHistory F ps (Marked.mark F source.erase) n)
    (selected : ∀name∈F,source.degreeAt name=some alpha)
    (trace : BetaNodeHistoryPreimage labels p oldEdge)
    (lookup : target.subterm p=some current)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠alpha))
    (marked : ¬current.label.OuterBarsSafe (fun x=>x≠alpha)) :
    ∃name∈F,∃beta body argument,
      source.subterm name=some (.app beta (.lam alpha body) argument) ∧
      ∃original vertex,source.subterm oldEdge=some original ∧
        Source source oldEdge (some vertex) ∧
        (vertex.val=name ∨vertex.val=name++[.fn]) ∧
        EndpointChain source (some vertex) [name++[.fn]] := by
  rcases trace.incoming_partition with uncreated |⟨pre,site,post,first⟩
  · obtain ⟨original,atOriginal,same⟩ := uncreated.source_label lookup
    have safe := (LTerm.outerBarsSafe_iff _ _).mp sourceSafe original.label (LTerm.label_mem_of_subterm atOriginal)
    exact False.elim (marked (same ▸ safe))
  · obtain ⟨name,chosen,beta,degree,body,argument,redex,original,vertex,atOriginal,endpoint,position,chain⟩ :=
      first_creation_selected_source first old lookup
    have atDegree:=selected name chosen
    simp only [LTerm.degreeAt,redex,Option.bind_some,LTerm.degree] at atDegree
    have same:=Option.some.inj atDegree
    subst degree
    exact ⟨name,chosen,beta,body,argument,redex,original,vertex,atOriginal,endpoint,position,chain⟩
#print axioms Labelled.NodeIncomingFirstCreation.old_split
#print axioms marked_node_source_selected
end Lamping.AG
