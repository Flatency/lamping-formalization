import Lamping.Lamping.ExpandedLastEndpointChains
import Lamping.Lamping.BackwardOtherLastFarSources
namespace Lamping.Lambda.Labelled
open Lamping.AG SyntaxIncidence

private theorem terminal_function_coordinate
    (reading : PrerequisiteReadsDirected t reader edge false)
    (terminal : PrerequisiteChain t reader [edge]) : ∃parent,edge=parent++[.fn] := by
  have backward : edge=reader := reading.2
  rcases reading.1 with ⟨stamp,fn,arg,lookup,split⟩ | ⟨stamp,body,lookup,split⟩
  · have bad:=congrArg List.length (backward.symm.trans split)
    simp at bad
  · rcases terminal.lambda_cases lookup with ⟨parent,a,arg,split,atParent,es⟩ |
      ⟨parent,step,tail,split,notFn,listEq,chain⟩
    · exact ⟨parent,backward.trans split⟩
    · have empty : tail=[] := (List.cons.inj listEq).2.symm
      exact False.elim (chain.nonempty empty)

private theorem same_last {p q : Path} {s u : Step} (eq : p++[s]=q++[u]) : p=q ∧s=u := by
  have rev:=congrArg List.reverse eq
  simp only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append] at rev
  have pair:=List.cons.inj rev
  exact ⟨by simpa using congrArg List.reverse pair.2,pair.1⟩

private theorem unsnoc (q : Path) (nonempty : q≠[]) : ∃p s,q=p++[s] := by
  induction q with
  | nil => exact False.elim (nonempty rfl)
  | cons s tail ih =>
    cases tail with
    | nil => exact ⟨[],s,rfl⟩
    | cons u rest =>
      obtain ⟨p,v,eq⟩:=ih (by simp)
      exact ⟨s::p,v,by rw [eq];rfl⟩

private theorem backward_forms
    {body argument target : LTerm} {site edge reader oldReader first last : Path}
    (origin : BetaIncomingReadingOrigin body argument site edge reader oldReader first last)
    (reading : PrerequisiteReadsDirected target reader edge false) :
    (edge=site ∧last=site) ∨
      ∃q,ArgumentOccurrence body.erase q ∧edge=site++q ∧last=(site++[.fn,.body])++q := by
  have backward : edge=reader:=reading.2
  cases origin with
  | resultFunction result function =>
    have length:=congrArg List.length (backward.symm.trans (result.trans function))
    simp at length
  | resultLambda result => exact Or.inl ⟨result,rfl⟩
  | @copyFunction p occurs copy read =>
    have same : reader=reader++[.fn] := by
      calc reader=edge := backward.symm
           _=site++(p++[.fn]) := copy
           _=(site++p)++[.fn] := (List.append_assoc _ _ _).symm
           _=reader++[.fn] := by rw [read]
    have length:=congrArg List.length same;simp at length
  | @copyLambda q _ _ occurs copy => exact Or.inr ⟨q,occurs,copy,rfl⟩

private theorem function_child_far
    {t node : LTerm} {parent : Path} {edges : List Path}
    (lookup : t.subterm (parent++[.fn])=some node)
    (chain : PrerequisiteChain t parent edges) :
    ∃far : ProperPosition t,Source t (parent++[.fn]) (some far) ∧
      EndpointChain t (some far) edges ∧∃stamp fn arg,t.subterm far.val=some (.app stamp fn arg) := by
  rw [LTerm.subterm_append] at lookup
  cases atParent : t.subterm parent with
  | none => rw [atParent] at lookup;cases lookup
  | some old =>
    rw [atParent,Option.bind_some] at lookup
    cases old with
    | var => cases lookup
    | lam => cases lookup
    | app stamp fn arg =>
      let far : ProperPosition t:=⟨parent,Or.inl ⟨stamp,fn,arg,atParent⟩⟩
      exact ⟨far,⟨.fn,_,_,rfl,atParent,.fn⟩,chain,stamp,fn,arg,atParent⟩

theorem BetaIncomingReadingOrigin.terminal_expanded_last_endpoint_chains
    {middle target body argument : LTerm} {site : Path} {beta alpha : Label}
    {edge reader oldReader first last : Path} {es : List Path} {ds : List Bool}
    (_step : StepAt site middle target)
    (redex : middle.subterm site=some (.app beta (.lam alpha body) argument))
    (origin : BetaIncomingReadingOrigin body argument site edge reader oldReader first last)
    (reading : PrerequisiteReadsDirected target reader edge false)
    (terminal : PrerequisiteChain target reader [edge])
    (expansion : CreatedReadingExpansion body site first last false es ds) :
    ∃ far : ProperPosition middle,
      ∃ _low : ExpandedLastSelectedEndpoint middle site (es.getLastD []) false (some far),
        EndpointChain middle (some far) [es.getLastD [],site++[.fn]] ∧
        (∃stamp fn arg,middle.subterm far.val=some (.app stamp fn arg)) := by
  obtain ⟨parent,terminalAt⟩:=terminal_function_coordinate reading terminal
  have forms:=backward_forms origin reading
  have supply (lastEdge : Path) (eq : es.getLastD []=lastEdge)
      (available : ∃far : ProperPosition middle,Source middle lastEdge (some far) ∧
        EndpointChain middle (some far) [lastEdge,site++[.fn]] ∧
        ∃stamp fn arg,middle.subterm far.val=some (.app stamp fn arg)) :
      ∃far : ProperPosition middle,
        ∃low : ExpandedLastSelectedEndpoint middle site (es.getLastD []) false (some far),
          EndpointChain middle (some far) [es.getLastD [],site++[.fn]] ∧
          ∃stamp fn arg,middle.subterm far.val=some (.app stamp fn arg) := by
    obtain ⟨far,source,chain,atApp⟩:=available
    have actualSource : Source middle (es.getLastD []) (some far) := eq ▸ source
    obtain ⟨low⟩:=origin.expanded_last_selected_endpoint redex expansion (by simpa using actualSource)
    exact ⟨far,low,eq ▸ chain,atApp⟩
  cases expansion with
  | resultLambda =>
    have siteEq : site=parent++[.fn] := by
      rcases forms with ⟨result,_⟩ | ⟨q,_occurs,_copy,lastEq⟩
      · exact result.symm.trans terminalAt
      · have length:=congrArg List.length lastEq;simp at length
    apply supply site rfl
    have chain:=result_function_old_chain (siteEq ▸ redex)
    obtain ⟨far,sourceSpec,complete,atApp⟩:=function_child_far (siteEq ▸ redex) chain
    exact ⟨far,siteEq ▸ sourceSpec,by simpa only [←siteEq] using complete,atApp⟩
  | @copyLambda q nonroot =>
    obtain ⟨p,s,qEq⟩:=unsnoc q nonroot
    have copiedAndOccurs : edge=site++q ∧ArgumentOccurrence body.erase q := by
      rcases forms with ⟨_result,lastEq⟩ | ⟨other,occurs,copy,lastEq⟩
      · have length:=congrArg List.length lastEq;simp at length
      · have equal : q=other:=List.append_cancel_left lastEq
        exact ⟨equal ▸ copy,equal ▸ occurs⟩
    have copied:=copiedAndOccurs.1
    have shape : (site++p)++[s]=parent++[.fn] := by
      simpa only [qEq,←List.append_assoc] using copied.symm.trans terminalAt
    have lastEq : s=.fn := (same_last shape).2
    subst s
    have occurs : ArgumentOccurrence body.erase (p++[.fn]) := by
      simpa only [qEq] using copiedAndOccurs.2
    have chain:=substituted_function_old_chain redex occurs
    obtain ⟨node,lookup⟩:=origin.old_prerequisite redex |>.2
    have lookup' : middle.subterm (((site++[.fn,.body])++p)++[.fn])=some node := by
      simpa only [qEq,List.append_assoc] using lookup
    obtain ⟨far,sourceSpec,complete,atApp⟩:=function_child_far lookup' chain
    apply supply ((site++[.fn,.body])++q) rfl
    exact ⟨far,by simpa only [qEq,List.append_assoc] using sourceSpec,
      by simpa only [qEq,List.append_assoc] using complete,atApp⟩
  | copyOverlap =>
    have siteEq : site=parent++[.fn] := by
      rcases forms with ⟨_result,lastEq⟩ | ⟨q,_occurs,copy,lastEq⟩
      · have length:=congrArg List.length lastEq;simp at length
      · have empty : q=[] := by
          have equal : (site++[.fn,.body])++[]=(site++[.fn,.body])++q := by simpa using lastEq
          exact (List.append_cancel_left equal).symm
        simpa only [empty,List.append_nil] using copy.symm.trans terminalAt
    apply supply site rfl
    have chain:=result_function_old_chain (siteEq ▸ redex)
    obtain ⟨far,sourceSpec,complete,atApp⟩:=function_child_far (siteEq ▸ redex) chain
    exact ⟨far,siteEq ▸ sourceSpec,by simpa only [←siteEq] using complete,atApp⟩

theorem SelectedOldTurn.terminal_expanded_last_original_endpoint_chains
    {F pre : List Path} {source middle target : LTerm} {degree : Label} {site : Path}
    {edge reader oldReader first last : Path} {es : List Path} {ds : List Bool}
    (event : SelectedOldTurn F source degree pre middle target site)
    (origin : BetaIncomingReadingOrigin event.body event.argument site edge reader oldReader first last)
    (reading : PrerequisiteReadsDirected target reader edge false)
    (terminal : PrerequisiteChain target reader [edge])
    (expansion : CreatedReadingExpansion event.body site first last false es ds) :
    ∃far : ProperPosition middle,
      ∃_low : ExpandedLastSelectedEndpoint middle site (es.getLastD []) false (some far),
        EndpointChain middle (some far) [es.getLastD [],site++[.fn]] ∧
        ∃(oldEdge : Path) (original : LTerm) (oldFrom oldTo : ProperPosition source)
          (sourceEdges targetEdges : List Path),
          BetaNodeHistoryPreimage event.labels (es.getLastD []) oldEdge ∧
          source.subterm oldEdge=some original ∧
          Source source oldEdge (some oldFrom) ∧Target source oldEdge (some oldTo) ∧
          EndpointChain source (some oldFrom) sourceEdges ∧
          EndpointChain source (some oldTo) targetEdges := by
  obtain ⟨far,low,farChain,_app⟩:=origin.terminal_expanded_last_endpoint_chains event.turn event.redex reading terminal expansion
  obtain ⟨oldEdge,original,lookup,trace⟩:=event.labels.node_preimage_from_lookup low.lookup
  obtain ⟨original',oldFrom,oldTo,sourceEdges,targetEdges,lookup',sourceSpec,targetSpec,fromChain,toChain⟩:=
    history_edge_endpoint_availability trace low.lookup low.sourceSpec low.targetSpec farChain low.singleton
  cases oldFrom with
  | none => exact False.elim fromChain
  | some oldFrom =>
    cases oldTo with
    | none => exact False.elim toChain
    | some oldTo => exact ⟨far,low,farChain,oldEdge,original',oldFrom,oldTo,sourceEdges,targetEdges,trace,lookup',sourceSpec,targetSpec,fromChain,toChain⟩

#print axioms BetaIncomingReadingOrigin.terminal_expanded_last_endpoint_chains
#print axioms SelectedOldTurn.terminal_expanded_last_original_endpoint_chains
end Lamping.Lambda.Labelled
