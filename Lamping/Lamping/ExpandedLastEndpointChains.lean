import Lamping.Lamping.RecentSpineFarOrigins
import Lamping.Lamping.SelectedNodeSourceOrigins
import Lamping.Lambda.SafeIncomingHistory
namespace Lamping.Lambda.Labelled
open SyntaxIncidence
variable {source : LTerm}

/-- A selected endpoint is an actual APP or FUNCTION lambda, not a label guess. -/
structure ExpandedLastSelectedEndpoint (middle : LTerm) (site : Path)
    (edge : Path) (forward : Bool) (far : Vertex middle) where
  node : LTerm
  lookup : middle.subterm edge=some node
  near : ProperPosition middle
  selected : near.val=site ∨near.val=site++[.fn]
  sourceSpec : Source middle edge (if forward then some near else far)
  targetSpec : Target middle edge (if forward then far else some near)
  singleton : AG.EndpointChain middle (some near) [site++[.fn]]

private theorem copied_bound_occurrence
    (origin : BetaIncomingReadingOrigin body argument site edge reader oldReader first last)
    (firstEq : first=site++[.arg]) (lastEq : last=(site++[.fn,.body])++q) :
    ArgumentOccurrence body.erase q := by
  cases origin with
  | resultFunction => have size:=congrArg List.length firstEq;simp at size
  | resultLambda => have size:=congrArg List.length lastEq;simp at size
  | copyFunction =>
    have bad:=List.append_cancel_left (by simpa only [List.append_assoc] using lastEq)
    cases bad
  | copyLambda actual =>
    have equal:=List.append_cancel_left lastEq
    simpa only [equal] using actual

private theorem bound_target
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (occurs : ArgumentOccurrence body.erase q) :
    Target source ((site++[.fn,.body])++q)
      (some (⟨site++[.fn],Or.inr ⟨alpha,body,by rw [LTerm.subterm_append,redex];rfl⟩⟩ : ProperPosition source)) := by
  change subtermAt body.erase q=some (.var (binderDepth q)) at occurs
  rw [←LTerm.erase_subterm] at occurs
  obtain ⟨node,lookup,same⟩:=Option.map_eq_some_iff.mp occurs
  cases node with
  | var stamp index =>
    cases same
    refine Or.inr ⟨stamp,_,alpha,body,q,?_,?_,?_,rfl⟩
    · rw [List.append_assoc,LTerm.subterm_append,redex];exact lookup
    · rw [LTerm.subterm_append,redex];rfl
    · simp only [List.append_assoc,List.cons_append,List.nil_append]
  | app => cases same
  | lam => cases same

/-- Six finite created-reading cases retain the genuine expanded LAST edge.
The other endpoint has a selected singleton; the supplied FAR incidence is
never replaced by the triple LAST or by a selected binder. -/
theorem BetaIncomingReadingOrigin.expanded_last_selected_endpoint
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (origin : BetaIncomingReadingOrigin body argument site edge reader oldReader first last)
    (expansion : CreatedReadingExpansion body site first last forward es ds)
    (farSpec : if forward then Target source (es.getLastD []) far else Source source (es.getLastD []) far) :
    Nonempty (ExpandedLastSelectedEndpoint source site (es.getLastD []) forward far) := by
  have lamAt : source.subterm (site++[.fn])=some (.lam alpha body) := by rw [LTerm.subterm_append,redex];rfl
  let app : ProperPosition source:=⟨site,Or.inl ⟨beta,.lam alpha body,argument,redex⟩⟩
  let lam : ProperPosition source:=⟨site++[.fn],Or.inr ⟨alpha,body,lamAt⟩⟩
  have appChain : AG.EndpointChain source (some app) [site++[.fn]]:=PrerequisiteChain.redex_app redex
  have lamChain : AG.EndpointChain source (some lam) [site++[.fn]]:=PrerequisiteChain.redex_lam redex
  have argAt : source.subterm (site++[.arg])=some argument := by rw [LTerm.subterm_append,redex];cases argument <;> rfl
  have bodyAt : source.subterm (site++[.fn,.body])=some body := by rw [LTerm.subterm_append,redex];cases body <;> rfl
  have argSource : Source source (site++[.arg]) (some app):=⟨.arg,_,_,rfl,redex,.arg⟩
  have bodySource : Source source (site++[.fn,.body]) (some lam):=⟨.body,_,_,by simp [lam,List.append_assoc],lamAt,.body⟩
  cases expansion with
  | resultFunction other =>
    exact ⟨⟨body,bodyAt,lam,Or.inr rfl,bodySource,farSpec,lamChain⟩⟩
  | resultOverlap shape =>
    exact ⟨⟨argument,argAt,app,Or.inl rfl,argSource,farSpec,appChain⟩⟩
  | copyFunction =>
    exact ⟨⟨argument,argAt,app,Or.inl rfl,argSource,farSpec,appChain⟩⟩
  | resultLambda =>
    exact ⟨⟨_,redex,app,Or.inl rfl,farSpec,Or.inl rfl,appChain⟩⟩
  | @copyLambda q nonroot =>
    obtain ⟨lastNode,lastAt⟩:=origin.old_prerequisite redex |>.2
    have occurs : ArgumentOccurrence body.erase q := copied_bound_occurrence origin rfl rfl
    exact ⟨⟨lastNode,lastAt,lam,Or.inr rfl,farSpec,bound_target redex occurs,lamChain⟩⟩
  | copyOverlap =>
    exact ⟨⟨_,redex,app,Or.inl rfl,farSpec,Or.inl rfl,appChain⟩⟩

end Lamping.Lambda.Labelled
namespace Lamping.AG
open Lambda Lambda.Labelled SyntaxIncidence
variable {source middle target : LTerm}

/-- Exact selected source endpoint and literal singleton, only as a result. -/
def SelectedOriginalSingleton (F : List Path) (source : LTerm) (degree : Label)
    (vertex : ProperPosition source) (edges : List Path) : Prop :=
  ∃name∈F,∃beta body argument,
    source.subterm name=some (.app beta (.lam degree body) argument) ∧
    (vertex.val=name ∨vertex.val=name++[.fn]) ∧edges=[name++[Step.fn]]

private theorem selected_origin
    (event : SelectedOldTurn F source degree pre middle target site)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (near : ProperPosition middle) (position : near.val=site ∨near.val=site++[.fn]) :
    ∃original es,SelectedOriginalSingleton F source degree original es ∧
      EndpointChain source (some original) es ∧
      BetaVertexHistoryPreimage event.labels (some near) (some original) := by
  obtain ⟨name,member,⟨beta,alpha,body,argument,redex⟩,appTrace,fnTrace⟩ :=
    event.beforeOld.selected_app_function_preimages event.labels event.member
  have degreeEq:=selected name member
  simp only [LTerm.degreeAt,redex,Option.bind_some,LTerm.degree] at degreeEq
  have same:=Option.some.inj degreeEq
  subst alpha
  rcases position with app | lam
  · let original : ProperPosition source:=⟨name,Or.inl ⟨beta,.lam degree body,argument,redex⟩⟩
    refine ⟨original,[name++[Step.fn]],⟨name,member,beta,body,argument,redex,Or.inl rfl,rfl⟩,
      PrerequisiteChain.redex_app redex,.proper ?_⟩
    change BetaNodeHistoryPreimage event.labels near.val name
    rw [app];exact appTrace
  · have lamAt : source.subterm (name++[.fn])=some (.lam degree body) := by rw [LTerm.subterm_append,redex];rfl
    let original : ProperPosition source:=⟨name++[.fn],Or.inr ⟨degree,body,lamAt⟩⟩
    refine ⟨original,[name++[Step.fn]],⟨name,member,beta,body,argument,redex,Or.inr rfl,rfl⟩,
      PrerequisiteChain.redex_lam redex,.proper ?_⟩
    change BetaNodeHistoryPreimage event.labels near.val (name++[.fn])
    rw [lam];exact fnTrace

/-- Both original endpoint chains, with explicit source safety refinement.
A marked SOURCE is selected but need not be the canonical FAR ancestor. -/
structure ExpandedLastOriginalEndpoints
    (F : List Path) (source middle : LTerm) (degree : Label)
    {pre : List Path} (labels : History pre source middle)
    (edge : Path) (node : LTerm) (forward : Bool)
    (originalFar : ProperPosition source) (farEdges : List Path) where
  oldEdge : Path
  original : LTerm
  lookup : source.subterm oldEdge=some original
  nodeTrace : BetaNodeHistoryPreimage labels edge oldEdge
  fromVertex : ProperPosition source
  toVertex : ProperPosition source
  sourceSpec : Source source oldEdge (some fromVertex)
  targetSpec : Target source oldEdge (some toVertex)
  sourceEdges : List Path
  targetEdges : List Path
  sourceChain : EndpointChain source (some fromVertex) sourceEdges
  targetChain : EndpointChain source (some toVertex) targetEdges
  safeLabel : node.label.OuterBarsSafe (fun x=>x≠degree) →original.label=node.label
  targetAncestry : ∃v,Target middle edge v ∧BetaVertexHistoryPreimage labels v (some toVertex)
  safeSourceAncestry : node.label.OuterBarsSafe (fun x=>x≠degree) →
    ∃v,Source middle edge v ∧BetaVertexHistoryPreimage labels v (some fromVertex)
  sourceClass : if forward then SelectedOriginalSingleton F source degree fromVertex sourceEdges
    else (node.label.OuterBarsSafe (fun x=>x≠degree) ∧fromVertex=originalFar ∧sourceEdges=farEdges) ∨
      (¬node.label.OuterBarsSafe (fun x=>x≠degree) ∧SelectedOriginalSingleton F source degree fromVertex sourceEdges)
  targetClass : if forward then toVertex=originalFar ∧targetEdges=farEdges
    else SelectedOriginalSingleton F source degree toVertex targetEdges

private theorem original_endpoints
    (event : SelectedOldTurn F source degree pre middle target site)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    {edge : Path} {forward : Bool} {far : ProperPosition middle}
    (low : ExpandedLastSelectedEndpoint middle site edge forward (some far))
    (originalFar : ProperPosition source) (farEdges : List Path)
    (farTrace : BetaVertexHistoryPreimage event.labels (some far) (some originalFar))
    (farChain : EndpointChain source (some originalFar) farEdges) :
    Nonempty (ExpandedLastOriginalEndpoints F source middle degree event.labels edge low.node forward originalFar farEdges) := by
  obtain ⟨near,nearEdges,nearSelected,nearChain,nearTrace⟩:=selected_origin event selected low.near low.selected
  obtain ⟨oldEdge,original,atOriginal,trace⟩:=event.labels.node_preimage_from_lookup low.lookup
  cases forward with
  | true =>
    obtain ⟨oldTo,oldTarget,targetTrace⟩:=trace.target_history low.targetSpec
    have toEq:=targetTrace.unique farTrace
    have actualTarget : Target source oldEdge (some originalFar):=toEq ▸ oldTarget
    by_cases safe : low.node.label.OuterBarsSafe (fun x=>x≠degree)
    · obtain ⟨node,oldFrom,atNode,sameLabel,oldSource,sourceTrace⟩:=
        event.beforeOld.safe_incoming_source_history selected trace low.lookup safe low.sourceSpec
      have fromEq:=sourceTrace.unique nearTrace
      have nodeEq:=Option.some.inj (atOriginal.symm.trans atNode)
      subst node
      exact ⟨⟨oldEdge,original,atOriginal,trace,near,originalFar,fromEq ▸ oldSource,actualTarget,
        nearEdges,farEdges,nearChain,farChain,fun _=>sameLabel,
        ⟨some far,low.targetSpec,farTrace⟩,(fun _=>⟨some low.near,low.sourceSpec,nearTrace⟩),nearSelected,⟨rfl,rfl⟩⟩⟩
    · obtain ⟨name,member,beta,body,argument,redex,node,oldFrom,atNode,oldSource,position,oldChain⟩:=
        marked_node_source_selected event.beforeOld selected trace low.lookup sourceSafe safe
      exact ⟨⟨oldEdge,original,atOriginal,trace,oldFrom,originalFar,oldSource,actualTarget,
        [name++[Step.fn]],farEdges,oldChain,farChain,fun h=>False.elim (safe h),
        ⟨some far,low.targetSpec,farTrace⟩,(fun h=>False.elim (safe h)),⟨name,member,beta,body,argument,redex,position,rfl⟩,⟨rfl,rfl⟩⟩⟩
  | false =>
    obtain ⟨oldTo,oldTarget,targetTrace⟩:=trace.target_history low.targetSpec
    have toEq:=targetTrace.unique nearTrace
    have actualTarget : Target source oldEdge (some near):=toEq ▸ oldTarget
    by_cases safe : low.node.label.OuterBarsSafe (fun x=>x≠degree)
    · obtain ⟨node,oldFrom,atNode,sameLabel,oldSource,sourceTrace⟩:=
        event.beforeOld.safe_incoming_source_history selected trace low.lookup safe low.sourceSpec
      have fromEq:=sourceTrace.unique farTrace
      have nodeEq:=Option.some.inj (atOriginal.symm.trans atNode)
      subst node
      exact ⟨⟨oldEdge,original,atOriginal,trace,originalFar,near,fromEq ▸ oldSource,actualTarget,
        farEdges,nearEdges,farChain,nearChain,fun _=>sameLabel,
        ⟨some low.near,low.targetSpec,nearTrace⟩,(fun _=>⟨some far,low.sourceSpec,farTrace⟩),Or.inl ⟨safe,rfl,rfl⟩,nearSelected⟩⟩
    · obtain ⟨name,member,beta,body,argument,redex,node,oldFrom,atNode,oldSource,position,oldChain⟩:=
        marked_node_source_selected event.beforeOld selected trace low.lookup sourceSafe safe
      exact ⟨⟨oldEdge,original,atOriginal,trace,oldFrom,near,oldSource,actualTarget,
        [name++[Step.fn]],nearEdges,oldChain,nearChain,fun h=>False.elim (safe h),
        ⟨some low.near,low.targetSpec,nearTrace⟩,(fun h=>False.elim (safe h)),Or.inr ⟨safe,⟨name,member,beta,body,argument,redex,position,rfl⟩⟩,nearSelected⟩⟩

/-- Public high bridge consumes the GIVEN recent/canonical compatibility.
No endpoint chain, old position, source homomorphism or paired iso is supplied. -/
theorem RecentFarCompatibility.expanded_last_endpoints
    {labels : History ps source current}
    {cut : ActualUnsafeMarkerCut F ps source current degree start edges}
    {leaf : DirectedMarkerLeafOutput F source degree cut.forward ps (cut.node.label.readLetters cut.forward)}
    {snapshot : IncomingIncidenceSnapshot current cut.edge}
    {geometry : SpineIncidenceProvenance F source degree cut.forward cut.spine cut.lookup leaf snapshot}
    {canonical : CanonicalAfterFarOutput labels cut snapshot} {recent : RecentSpineFrame geometry}
    (compat : RecentFarCompatibility canonical recent)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree)) :
    ∃low : ExpandedLastSelectedEndpoint recent.packet.middle recent.packet.site
      (recent.packet.frame.edges.getLastD []) cut.forward (some compat.expandedProper),
      Nonempty (ExpandedLastOriginalEndpoints F source recent.packet.middle degree recent.packet.event.labels
        (recent.packet.frame.edges.getLastD []) low.node cut.forward canonical.sourceProper compat.originalEdges) := by
  have farSpec : if cut.forward then Target recent.packet.middle (recent.packet.frame.edges.getLastD []) (some compat.expandedProper)
      else Source recent.packet.middle (recent.packet.frame.edges.getLastD []) (some compat.expandedProper) := by
    rw [←compat.expandedEq];exact recent.packet.frame.finalIncidence
  obtain ⟨low⟩:=recent.packet.origin.expanded_last_selected_endpoint recent.packet.event.redex recent.packet.frame.expansion farSpec
  refine ⟨low,original_endpoints recent.packet.event selected sourceSafe low canonical.sourceProper compat.originalEdges compat.prefixVertexTrace ?_⟩
  exact Eq.mp (congrArg (fun p : Path=>PrerequisiteChain source p compat.originalEdges) compat.sourceCoordinate) compat.originalChain

end Lamping.AG
