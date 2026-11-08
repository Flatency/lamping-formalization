import Lamping.Lamping.PairedMarkerSpineReannotation
import Lamping.Lamping.InteriorSourceBlockEndpoints
import Lamping.Lamping.CanonicalAfterFarComparison
import Lamping.Lambda.NonterminalReadingDirections
import Lamping.Lambda.TargetHistoryPreimages

namespace Lamping.Lambda.Labelled
namespace NonterminalFarBoundary
open SyntaxIncidence InteriorSourceBlock
variable {source target : LTerm}
variable {label : Label}

theorem relabel_node_history
    {labels : History ps source target}
    (trace : BetaNodeHistoryPreimage labels position original) (s : Nat → Label) :
    BetaNodeHistoryPreimage (labels.relabel s) position original := by
  induction trace with
  | nil => exact .nil _ _
  | @one site ps source middle target body argument beta alpha position mid original step rest redex origin tail ih =>
    have atRedex : (source.relabel s).subterm site=some
        (.app (beta.relabel s) (.lam (alpha.relabel s) (body.relabel s)) (argument.relabel s)) := by
      simpa only [LTerm.relabel] using lookup_relabel redex s
    have other : BetaNodePreimage (body.relabel s) (argument.relabel s) site mid original :=
      origin.reannotate (LTerm.erase_relabel s body).symm (LTerm.erase_relabel s argument).symm
    exact .one (step:=step.relabel s) atRedex other ih

/-- Retain the actual selected subtree routes and original binder environment. -/
theorem selected_at_lookup
    (routes : SelectedTermRoutes edges allowed env ctx target)
    (lookup : target.subterm position=some node) :
    ∃innerEnv innerCtx,SelectedTermRoutes edges allowed innerEnv innerCtx node := by
  induction routes generalizing position with
  | var route =>
    cases position with
    | nil => cases lookup;exact ⟨_,_,.var route⟩
    | cons step rest => cases step <;> simp [LTerm.subterm] at lookup
  | lam route body ih =>
    cases position with
    | nil => cases lookup;exact ⟨_,_,.lam route body⟩
    | cons step rest =>
      cases step with
      | fn | arg => simp [LTerm.subterm] at lookup
      | body => exact ih lookup
  | app route fn arg fnIH argIH =>
    cases position with
    | nil => cases lookup;exact ⟨_,_,.app route fn arg⟩
    | cons step rest =>
      cases step with
      | body => simp [LTerm.subterm] at lookup
      | fn => exact fnIH lookup
      | arg => exact argIH lookup

/-- The principal route and ARG child share THIS original parent identity. -/
theorem selected_app_parent
    (routes : SelectedTermRoutes edges allowed env ctx target)
    (lookup : target.subterm parent=some (.app stamp fn arg)) :
    ∃innerEnv innerCtx origin,
      SelectedSourceRoute edges allowed innerCtx stamp (.appContext origin) ∧
      SelectedTermRoutes edges allowed innerEnv (.appFn origin) fn ∧
      SelectedTermRoutes edges allowed innerEnv (.appArg origin) arg := by
  obtain ⟨innerEnv,innerCtx,actual⟩:=selected_at_lookup routes lookup
  cases actual with
  | app principal fn arg => exact ⟨_,_,_,principal,fn,arg⟩

/-- The principal route and BODY child share THIS original parent identity. -/
theorem selected_lam_parent
    (routes : SelectedTermRoutes edges allowed env ctx target)
    (lookup : target.subterm parent=some (.lam stamp body)) :
    ∃innerEnv innerCtx origin,
      SelectedSourceRoute edges allowed innerCtx stamp (.lamContext origin) ∧
      SelectedTermRoutes edges allowed (origin::innerEnv) (.lamBody origin) body := by
  obtain ⟨innerEnv,innerCtx,actual⟩:=selected_at_lookup routes lookup
  cases actual with
  | lam principal body => exact ⟨_,_,_,principal,body⟩

structure BoundaryGeometry (source : LTerm) (F : List Path) (n : Nat)
    (kind forward : Bool) (start finish : SourcePort) where
  edge : SourceEdge
  member : edge∈sourceEdges [] .external source
  atomic : edge.atom=Label.atom n
  selected : SelectedRedex source F
  ports : if forward then edge.fromPort=selected.afterPort kind ∧edge.toPort=finish
    else edge.fromPort=start ∧edge.toPort=selected.beforePort kind

/-- Literal whole-word far boundary, in the real reading direction. -/
theorem selected_route_far_boundary (initial : INIT source)
    (route : SelectedSourceRoute (sourceEdges [] .external source) (SelectedDegree source F) start label finish)
    (boundary : label.readLetters forward=preLetters++[bar kind degree,.atom n]) :
    Nonempty (BoundaryGeometry source F n kind forward start finish) := by
  have walk:=route_walk route
  cases forward with
  | true =>
    change label.letters=preLetters++[bar kind degree,.atom n] at boundary
    rw [boundary] at walk
    obtain ⟨middle,_before,after⟩:=walk.split
    cases after with
    | cons marker tail =>
      cases tail with
      | cons atom tail =>
        cases tail
        obtain ⟨redex,_degree,_start,atEnd⟩:=marker_step_redex initial marker
        cases atom with
        | atom member atomic => exact ⟨⟨_,member,atomic,redex,atEnd,rfl⟩⟩
  | false =>
    have boundary' : label.letters=[.atom n,bar kind degree]++preLetters.reverse := by
      have reversed:=congrArg List.reverse boundary
      simpa only [Label.readLetters,Bool.false_eq_true,ite_false,List.reverse_reverse,
        List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append] using reversed
    rw [boundary'] at walk
    cases walk with
    | cons atom tail =>
      cases tail with
      | cons marker after =>
        obtain ⟨redex,_degree,atStart,_finish⟩:=marker_step_redex initial marker
        cases atom with
        | atom member atomic => exact ⟨⟨_,member,atomic,redex,rfl,atStart⟩⟩

/-- A literal last atom identifies only its own actual local INIT preimage. -/
theorem local_last_atom_trace
    {localTarget node basisNode : LTerm} {position original : Path}
    (history : History ps (initLabels source.erase) localTarget)
    (lookup : localTarget.subterm position=some node)
    (basisLookup : (initLabels source.erase).subterm original=some basisNode)
    (atomic : basisNode.label=Label.atom n) (lastAtom : node.label.lastAtom=some n) :
    BetaNodeHistoryPreimage history position original := by
  obtain ⟨oldPosition,old,atOld,trace⟩:=history.node_preimage_from_lookup lookup
  obtain ⟨ancestor,atAncestor,last,tag⟩:=trace.lastAtom_constructor lookup
  obtain ⟨m,atom⟩:=(init_is_INIT source.erase).1 ancestor.label (LTerm.label_mem_of_subterm atAncestor)
  have equal : n=m := by
    have atoms:=lastAtom.symm.trans last
    simpa only [atom,Label.lastAtom,Label.atom,Option.some.injEq] using atoms
  have labels : ancestor.label=basisNode.label:=atom.trans ((congrArg Label.atom equal.symm).trans atomic.symm)
  have coordinates:=LTerm.subterm_label_injective _ (init_is_INIT source.erase).2 atAncestor basisLookup labels
  exact coordinates ▸ trace

/-- Re-annotation transports an actual occurrence trace through ALL beta origins. -/
theorem local_trace_global
    {localTarget current : LTerm}
    (history : History ps (initLabels source.erase) localTarget)
    (labels : History ps source current)
    (trace : BetaNodeHistoryPreimage history position original) :
    BetaNodeHistoryPreimage labels position original := by
  let s:=initialRelabelling source 0
  have factor : (initLabels source.erase).relabel s=source:=initialRelabelling_factor source 0
  have lifted : History ps source (localTarget.relabel s) := by
    simpa only [factor] using history.relabel s
  have same : localTarget.relabel s=current:=lifted.deterministic labels
  simpa only [factor,same] using relabel_node_history trace s

/-- The current incoming node's target trace handles VAR binding as well as APP. -/
theorem true_far_target
    {current localTarget node basisNode : LTerm}
    (labels : History ps source current)
    (history : History ps (initLabels source.erase) localTarget)
    (cut : Lamping.AG.ActualUnsafeMarkerCut F ps source current degree start es)
    (snapshot : IncomingIncidenceSnapshot current cut.edge)
    (canonical : Lamping.AG.CanonicalAfterFarOutput labels cut snapshot)
    (forward : cut.forward=true)
    (lookup : localTarget.subterm cut.edge=some node)
    (basisLookup : (initLabels source.erase).subterm original=some basisNode)
    (atomic : basisNode.label=Label.atom n) (lastAtom : node.label.lastAtom=some n) :
    Target source original (some canonical.sourceProper) := by
  have localTrace:=local_last_atom_trace history lookup basisLookup atomic lastAtom
  have trace:=local_trace_global history labels localTrace
  have endpoint : Target current cut.edge (some canonical.currentProper) := by
    have eq : snapshot.toVertex=some canonical.currentProper := by
      simpa only [IncomingIncidenceSnapshot.far,forward,if_true] using canonical.farEq
    exact eq ▸ snapshot.toSpec
  obtain ⟨oldVertex,targetSpec,vertexTrace⟩:=trace.target_history endpoint
  have same:=vertexTrace.unique canonical.vertexTrace
  exact same ▸ targetSpec

/-- The actual whole OLD schedule supplies these exact selected term routes. -/
theorem actual_old_routes
    {localTarget : LTerm}
    (old : Marked.RelativeOldHistory F ps (Marked.mark F source.erase) marked)
    (history : History ps (initLabels source.erase) localTarget) :
    SelectedTermRoutes (sourceEdges [] .external (initLabels source.erase))
      (SelectedDegree (initLabels source.erase) F) [] .external localTarget := by
  have localOld : Marked.RelativeOldHistory F ps (Marked.mark F (initLabels source.erase).erase) marked := by
    simpa only [erase_initLabels] using old
  exact relative_development_selected_routes (init_is_INIT _)
    ((Marked.relativeOld_iff_relative (Marked.selected_mark F _)).mp localOld) history

theorem selected_incoming
    (routes : SelectedTermRoutes edges allowed env ctx node) :
    ∃finish,SelectedSourceRoute edges allowed ctx node.label finish := by
  cases routes with
  | var route => exact ⟨_,route⟩
  | lam route body => exact ⟨_,route⟩
  | app route fn arg => exact ⟨_,route⟩

/-- An actual APP parent route locks the original principal occurrence. -/
theorem app_parent_origin
    {localTarget : LTerm}
    (history : History ps (initLabels source.erase) localTarget)
    (lookup : localTarget.subterm position=some (.app stamp fn arg))
    (route : SourceRoute (sourceEdges [] .external (initLabels source.erase)) ctx stamp (.appContext origin)) :
    ∃original oldFn oldArg,
      (initLabels source.erase).subterm original=some (.app origin oldFn oldArg) ∧
      BetaNodeHistoryPreimage history position original := by
  obtain ⟨n,last,originEq⟩:=route.app_last_atom
  obtain ⟨original,old,atOld,trace⟩:=history.node_preimage_from_lookup lookup
  obtain ⟨ancestor,atAncestor,lastEq,tag⟩:=trace.lastAtom_constructor lookup
  obtain ⟨m,atomic⟩:=(init_is_INIT source.erase).1 ancestor.label (LTerm.label_mem_of_subterm atAncestor)
  have nm : n=m := by
    have same:=last.symm.trans lastEq
    simpa only [atomic,Label.lastAtom,Label.atom,Option.some.injEq] using same
  have labelEq : ancestor.label=origin:=atomic.trans ((congrArg Label.atom nm.symm).trans originEq.symm)
  cases ancestor with
  | var => simp [LTerm.constructorTag] at tag
  | lam => simp [LTerm.constructorTag] at tag
  | app label fn arg =>
    change label=origin at labelEq
    cases labelEq
    exact ⟨original,fn,arg,atAncestor,trace⟩

/-- An actual lambda parent route locks its original principal occurrence. -/
theorem lam_parent_origin
    {localTarget : LTerm}
    (history : History ps (initLabels source.erase) localTarget)
    (lookup : localTarget.subterm position=some (.lam stamp body))
    (route : SourceRoute (sourceEdges [] .external (initLabels source.erase)) ctx stamp (.lamContext origin)) :
    ∃original oldBody,
      (initLabels source.erase).subterm original=some (.lam origin oldBody) ∧
      BetaNodeHistoryPreimage history position original := by
  obtain ⟨n,last,originEq⟩:=route.lam_last_atom
  obtain ⟨original,old,atOld,trace⟩:=history.node_preimage_from_lookup lookup
  obtain ⟨ancestor,atAncestor,lastEq,tag⟩:=trace.lastAtom_constructor lookup
  obtain ⟨m,atomic⟩:=(init_is_INIT source.erase).1 ancestor.label (LTerm.label_mem_of_subterm atAncestor)
  have nm : n=m := by
    have same:=last.symm.trans lastEq
    simpa only [atomic,Label.lastAtom,Label.atom,Option.some.injEq] using same
  have labelEq : ancestor.label=origin:=atomic.trans ((congrArg Label.atom nm.symm).trans originEq.symm)
  cases ancestor with
  | var => simp [LTerm.constructorTag] at tag
  | app => simp [LTerm.constructorTag] at tag
  | lam label body =>
    change label=origin at labelEq
    cases labelEq
    exact ⟨original,body,atAncestor,trace⟩

theorem occurrence_arg_parent (initial : INIT source)
    (occurrence : SourceSubterm [] .external source position env ctx node)
    (lookup : source.subterm parent=some (.app stamp fn arg))
    (contextEq : ctx=.appArg stamp) : position=parent++[Step.arg] := by
  rcases occurrence.last_departure with ⟨empty,external⟩ |⟨actual,step,term,split,atParent,role⟩
  · rw [external] at contextEq;cases contextEq
  · cases role with
    | fn => cases contextEq
    | body => cases contextEq
    | arg =>
      have sameLabel:=SourcePort.appArg.inj contextEq
      have sameParent:=LTerm.subterm_label_injective source initial.2 atParent lookup sameLabel
      simpa only [sameParent] using split

theorem occurrence_body_parent (initial : INIT source)
    (occurrence : SourceSubterm [] .external source position env ctx node)
    (lookup : source.subterm parent=some (.lam stamp body))
    (contextEq : ctx=.lamBody stamp) : position=parent++[Step.body] := by
  rcases occurrence.last_departure with ⟨empty,external⟩ |⟨actual,step,term,split,atParent,role⟩
  · rw [external] at contextEq;cases contextEq
  · cases role with
    | fn => cases contextEq
    | arg => cases contextEq
    | body =>
      have sameLabel:=SourcePort.lamBody.inj contextEq
      have sameParent:=LTerm.subterm_label_injective source initial.2 atParent lookup sameLabel
      simpa only [sameParent] using split

theorem last_atom_suffix {label : Label}
    (equation : label.letters=pre++[Letter.atom n]) : label.lastAtom=some n := by
  induction pre generalizing label with
  | nil =>
    have same : label=Label.atom n:=Label.letters_injective equation
    rw [same];rfl
  | cons letter rest ih =>
    cases label with
    | single a =>
      have empty : []=rest++[Letter.atom n]:=(List.cons.inj equation).2
      have impossible:=congrArg List.length empty
      simp only [List.length_nil,List.length_append,List.length_singleton] at impossible
      omega
    | cons a tail => exact ih (label:=tail) (List.cons.inj equation).2

private theorem nonterminal_not_redex
    (chain : PrerequisiteChain t reader (edge::after)) (more : after≠[]) :
    ¬PrerequisiteRedexEdge t edge := by
  obtain ⟨before,last,split,redex,earlier⟩:=chain.redex_only_last
  cases before with
  | nil => simp only [List.nil_append,List.cons.injEq] at split;exact False.elim (more split.2)
  | cons first rest =>
    have same:= (List.cons.inj split).1
    exact earlier edge (by rw [same];exact List.mem_cons_self)

theorem forward_nonterminal_not_lambda
    {current : LTerm}
    (cut : Lamping.AG.ActualUnsafeMarkerCut F ps source current degree start es)
    (more : cut.after≠[]) (forward : cut.forward=true) :
    ∀stamp body,cut.node≠.lam stamp body := by
  intro stamp body equal
  have notRedex:=nonterminal_not_redex cut.remaining more
  rcases cut.reading.1 with ⟨a,fn,arg,atReader,split⟩ |⟨a,body,atReader,split⟩
  · have atFunction : current.subterm cut.edge=some fn := by
      rw [split,LTerm.subterm_append,atReader];cases fn <;> rfl
    have fnEq : fn=.lam stamp body:=Option.some.inj (atFunction.symm.trans (equal ▸ cut.lookup))
    exact notRedex ⟨cut.reader,a,stamp,body,arg,split,by simpa only [fnEq] using atReader⟩
  · have function : cut.edge=cut.reader++[.fn]:=by simpa only [forward,if_true] using cut.reading.2
    have sizes:=congrArg List.length (split.symm.trans function)
    simp at sizes

theorem local_node_global
    {current localTarget localNode : LTerm}
    (labels : History ps source current)
    (history : History ps (initLabels source.erase) localTarget)
    (lookup : localTarget.subterm position=some localNode)
    (globalLookup : current.subterm position=some node) :
    localNode.relabel (initialRelabelling source 0)=node := by
  let s:=initialRelabelling source 0
  have factor : (initLabels source.erase).relabel s=source:=initialRelabelling_factor source 0
  have lifted : History ps source (localTarget.relabel s) := by
    simpa only [factor] using history.relabel s
  have same : localTarget.relabel s=current:=lifted.deterministic labels
  have atGlobal : current.subterm position=some (localNode.relabel s) := by
    rw [←same];exact lookup_relabel lookup s
  exact Option.some.inj (atGlobal.symm.trans globalLookup)

/-- Proper literal SOURCE is transported from an ARG parent of THIS false read. -/
theorem arg_far_source
    {current localTarget localNode : LTerm}
    (labels : History ps source current)
    (history : History ps (initLabels source.erase) localTarget)
    (routes : SelectedTermRoutes (sourceEdges [] .external (initLabels source.erase)) allowed [] .external localTarget)
    (parentLookup : localTarget.subterm parent=some (.app stamp fn arg))
    (nodeLookup : localTarget.subterm (parent++[.arg])=some localNode)
    (route : SourceRoute (sourceEdges [] .external (initLabels source.erase)) routeCtx localNode.label finish)
    (occurrence : SourceSubterm [] .external (initLabels source.erase) original env ctx basisNode)
    (contextEq : ctx=routeCtx)
    (far : ProperPosition source)
    (farTrace : BetaNodeHistoryPreimage labels parent far.val) :
    Source source original (some far) := by
  obtain ⟨innerEnv,innerCtx,origin,parentRoute,fnRoutes,argRoutes⟩:=selected_app_parent routes parentLookup
  have actual : arg=localNode := by
    have atArg : localTarget.subterm (parent++[.arg])=some arg := by
      rw [LTerm.subterm_append,parentLookup];cases arg <;> rfl
    exact Option.some.inj (atArg.symm.trans nodeLookup)
  rw [actual] at argRoutes
  obtain ⟨childFinish,childRoute⟩:=selected_incoming argRoutes
  have contexts : routeCtx=.appArg origin :=
    route.start_eq_of_firstAtom (init_is_INIT _) childRoute.forget rfl
  obtain ⟨oldParent,oldFn,oldArg,oldLookup,parentTrace⟩:=app_parent_origin history parentLookup parentRoute.forget
  have split:=occurrence_arg_parent (init_is_INIT _) occurrence oldLookup (contextEq.trans contexts)
  have coordinate : oldParent=far.val:=(local_trace_global history labels parentTrace).unique farTrace
  have globalParent : source.subterm oldParent=some
      (.app (origin.relabel (initialRelabelling source 0))
        (oldFn.relabel (initialRelabelling source 0)) (oldArg.relabel (initialRelabelling source 0))) := by
    have factor : (initLabels source.erase).relabel (initialRelabelling source 0)=source:=initialRelabelling_factor source 0
    simpa only [factor,LTerm.relabel] using lookup_relabel oldLookup (initialRelabelling source 0)
  exact ⟨.arg,_,.appArg _,by simpa only [coordinate] using split,by simpa only [coordinate] using globalParent,.arg⟩

theorem body_far_source
    {current localTarget localNode : LTerm}
    (labels : History ps source current)
    (history : History ps (initLabels source.erase) localTarget)
    (routes : SelectedTermRoutes (sourceEdges [] .external (initLabels source.erase)) allowed [] .external localTarget)
    (parentLookup : localTarget.subterm parent=some (.lam stamp body))
    (nodeLookup : localTarget.subterm (parent++[.body])=some localNode)
    (route : SourceRoute (sourceEdges [] .external (initLabels source.erase)) routeCtx localNode.label finish)
    (occurrence : SourceSubterm [] .external (initLabels source.erase) original env ctx basisNode)
    (contextEq : ctx=routeCtx)
    (far : ProperPosition source)
    (farTrace : BetaNodeHistoryPreimage labels parent far.val) :
    Source source original (some far) := by
  obtain ⟨innerEnv,innerCtx,origin,parentRoute,bodyRoutes⟩:=selected_lam_parent routes parentLookup
  have actual : body=localNode := by
    have atBody : localTarget.subterm (parent++[.body])=some body := by
      rw [LTerm.subterm_append,parentLookup];cases body <;> rfl
    exact Option.some.inj (atBody.symm.trans nodeLookup)
  rw [actual] at bodyRoutes
  obtain ⟨childFinish,childRoute⟩:=selected_incoming bodyRoutes
  have contexts : routeCtx=.lamBody origin :=
    route.start_eq_of_firstAtom (init_is_INIT _) childRoute.forget rfl
  obtain ⟨oldParent,oldBody,oldLookup,parentTrace⟩:=lam_parent_origin history parentLookup parentRoute.forget
  have split:=occurrence_body_parent (init_is_INIT _) occurrence oldLookup (contextEq.trans contexts)
  have coordinate : oldParent=far.val:=(local_trace_global history labels parentTrace).unique farTrace
  have globalParent : source.subterm oldParent=some
      (.lam (origin.relabel (initialRelabelling source 0)) (oldBody.relabel (initialRelabelling source 0))) := by
    have factor : (initLabels source.erase).relabel (initialRelabelling source 0)=source:=initialRelabelling_factor source 0
    simpa only [factor,LTerm.relabel] using lookup_relabel oldLookup (initialRelabelling source 0)
  exact ⟨.body,_,.lamBody _,by simpa only [coordinate] using split,by simpa only [coordinate] using globalParent,.body⟩

theorem backward_lambda_lookup
    {current : LTerm}
    (cut : Lamping.AG.ActualUnsafeMarkerCut F ps source current degree start es)
    (backward : cut.forward=false) :
    ∃stamp body,current.subterm cut.edge=some (.lam stamp body) := by
  have edgeReader : cut.edge=cut.reader:=by simpa only [backward,if_false,Bool.false_eq_true] using cut.reading.2
  rcases cut.reading.1 with ⟨a,fn,arg,lookup,split⟩ |⟨a,body,lookup,split⟩
  · have lengths:=congrArg List.length (edgeReader.symm.trans split)
    simp at lengths
  · exact ⟨a,body,by simpa only [edgeReader] using lookup⟩

/-- The FALSE far atom's source is the OWN ancestor of the actual parent. -/
theorem false_far_source
    {current localTarget localNode : LTerm}
    (labels : History ps source current)
    (history : History ps (initLabels source.erase) localTarget)
    (routes : SelectedTermRoutes (sourceEdges [] .external (initLabels source.erase)) allowed [] .external localTarget)
    (cut : Lamping.AG.ActualUnsafeMarkerCut F ps source current degree start es)
    (more : cut.after≠[])
    (snapshot : IncomingIncidenceSnapshot current cut.edge)
    (canonical : Lamping.AG.CanonicalAfterFarOutput labels cut snapshot)
    (backward : cut.forward=false)
    (lookup : localTarget.subterm cut.edge=some localNode)
    (route : SourceRoute (sourceEdges [] .external (initLabels source.erase)) routeCtx localNode.label finish)
    (occurrence : SourceSubterm [] .external (initLabels source.erase) original env ctx basisNode)
    (contextEq : ctx=routeCtx) :
    Source source original (some canonical.sourceProper) := by
  have sourceSpec : Source current cut.edge (some canonical.currentProper) := by
    have eq : snapshot.fromVertex=some canonical.currentProper := by
      simpa only [IncomingIncidenceSnapshot.far,backward,if_false,Bool.false_eq_true] using canonical.farEq
    exact eq ▸ snapshot.fromSpec
  obtain ⟨step,parentTerm,parentPort,split,parentLookup,role⟩:=sourceSpec
  have sameErase:=SpineReannotation.history_erase labels history (erase_initLabels source.erase).symm
  obtain ⟨localParent,localParentLookup,erased⟩:=SpineReannotation.paired_lookup sameErase parentLookup
  cases role with
  | @fn parentStamp fn arg =>
    obtain ⟨stamp,body,atLambda⟩:=backward_lambda_lookup cut backward
    have atChild : current.subterm cut.edge=some fn := by
      rw [split,LTerm.subterm_append,parentLookup];cases fn <;> rfl
    have fnEq : fn=.lam stamp body:=Option.some.inj (atChild.symm.trans atLambda)
    exact False.elim ((nonterminal_not_redex cut.remaining more)
      ⟨canonical.currentProper.val,_,stamp,body,_,split,by simpa only [fnEq] using parentLookup⟩)
  | arg =>
    cases localParent with
    | var => cases erased
    | lam => cases erased
    | app localStamp localFn localArg =>
      exact arg_far_source labels history routes localParentLookup
        (by rw [←split];exact lookup) route occurrence contextEq canonical.sourceProper canonical.nodeTrace
  | body =>
    cases localParent with
    | var => cases erased
    | app => cases erased
    | lam localStamp localBody =>
      exact body_far_source labels history routes localParentLookup
        (by rw [←split];exact lookup) route occurrence contextEq canonical.sourceProper canonical.nodeTrace

/-- Actual occurrence input roles are literal even when labels repeat. -/
theorem occurrence_incoming_step
    (occurrence : SourceSubterm [] .external source position env ctx node) :
    ctx.incomingStep=position.getLast? := by
  rcases occurrence.last_departure with ⟨empty,external⟩ |⟨parent,step,term,split,lookup,role⟩
  · rw [external,empty];rfl
  · rw [split]
    cases role <;> simp only [SourcePort.incomingStep,List.getLast?_append,List.getLast?_singleton,Option.some_or]

theorem original_incoming_role
    {localTarget localNode : LTerm}
    (history : History ps (initLabels source.erase) localTarget)
    (lookup : localTarget.subterm position=some localNode)
    (route : SourceRoute (sourceEdges [] .external (initLabels source.erase)) routeCtx localNode.label finish)
    (occurrence : SourceSubterm [] .external (initLabels source.erase) original env ctx basisNode)
    (contextEq : ctx=routeCtx) : original.getLast?=position.getLast? := by
  obtain ⟨otherCtx,otherFinish,otherRoute,role⟩:=history.node_incoming_route (init_is_INIT _) lookup
  have same:=route.start_eq_of_firstAtom (init_is_INIT _) otherRoute rfl
  exact (occurrence_incoming_step occurrence).symm.trans
    ((congrArg SourcePort.incomingStep (contextEq.trans same)).trans role)

def global_redex (redex : SelectedRedex (initLabels source.erase) F) : SelectedRedex source F where
  position:=redex.position
  member:=redex.member
  beta:=redex.beta.relabel (initialRelabelling source 0)
  degree:=redex.degree.relabel (initialRelabelling source 0)
  body:=redex.body.relabel (initialRelabelling source 0)
  argument:=redex.argument.relabel (initialRelabelling source 0)
  lookup:=by
    have factor : (initLabels source.erase).relabel (initialRelabelling source 0)=source:=initialRelabelling_factor source 0
    simpa only [factor,LTerm.relabel] using lookup_relabel redex.lookup (initialRelabelling source 0)

theorem forward_original_not_lambda
    {current : LTerm} (labels : History ps source current)
    (cut : Lamping.AG.ActualUnsafeMarkerCut F ps source current degree start es)
    (more : cut.after≠[]) (forward : cut.forward=true)
    (trace : BetaNodeHistoryPreimage labels cut.edge original) :
    ¬∃stamp body,source.subterm original=some (.lam stamp body) := by
  rintro ⟨stamp,body,lookup⟩
  obtain ⟨old,oldLookup,lastAtom,tag⟩:=trace.lastAtom_constructor cut.lookup
  have same : old=.lam stamp body:=Option.some.inj (oldLookup.symm.trans lookup)
  rw [same] at tag
  have forbidden:=forward_nonterminal_not_lambda cut more forward
  cases actual : cut.node with
  | var => simp [actual,LTerm.constructorTag] at tag
  | app => simp [actual,LTerm.constructorTag] at tag
  | lam a b => exact forbidden a b actual

structure OriginalFarAtom (source : LTerm) (F : List Path) (n : Nat)
    (kind forward : Bool) (far : ProperPosition source) where
  position : Path
  env : List Label
  ctx : SourcePort
  node : LTerm
  occurrence : SourceSubterm [] .external (initLabels source.erase) position env ctx node
  atomic : node.label=Label.atom n
  lookup : source.subterm position=some (node.relabel (initialRelabelling source 0))
  selected : SelectedRedex source F
  auxiliary : AuxiliaryAt source position
  endpoints : if forward then Source source position (some (selected.vertex kind)) ∧Target source position (some far)
    else Source source position (some far) ∧Target source position (some (selected.vertex (!kind)))

def OriginalFarAtom.edge (out : OriginalFarAtom source F n kind forward far) : Edge source :=
  ⟨out.position,by rw [←LTerm.erase_subterm,out.lookup];rfl⟩

theorem OriginalFarAtom.full_image (out : OriginalFarAtom source F n kind forward far) :
    SyntaxIncidence.label source out.edge=initialRelabelling source 0 n := by
  rw [SyntaxIncidence.label_of_lookup source out.edge out.lookup,label_relabel,out.atomic]
  rfl

/-- Both actual whole-word far directions, with genuine selected and canonical endpoints. -/
theorem actual_old_far_atom
    {current localTarget localNode : LTerm}
    (labels : History ps source current)
    (old : Marked.RelativeOldHistory F ps (Marked.mark F source.erase) marked)
    (history : History ps (initLabels source.erase) localTarget)
    (cut : Lamping.AG.ActualUnsafeMarkerCut F ps source current degree start es)
    (more : cut.after≠[])
    (snapshot : IncomingIncidenceSnapshot current cut.edge)
    (canonical : Lamping.AG.CanonicalAfterFarOutput labels cut snapshot)
    (lookup : localTarget.subterm cut.edge=some localNode)
    (boundary : localNode.label.readLetters cut.forward=pre++[bar kind d,.atom n]) :
    Nonempty (OriginalFarAtom source F n kind cut.forward canonical.sourceProper) := by
  obtain ⟨routeCtx,finish,route⟩:=actual_old_node_route old history lookup
  obtain ⟨geometry⟩:=selected_route_far_boundary (init_is_INIT _) route boundary
  obtain ⟨position,env,ctx,node,occurrence,edgeEq⟩:=edge_occurrence geometry.member
  have atomic : node.label=Label.atom n :=
    (source_edge_label env ctx node).symm.trans ((congrArg SourceEdge.atom edgeEq).trans geometry.atomic)
  have globalLookup : source.subterm position=some (node.relabel (initialRelabelling source 0)) := by
    have factor : (initLabels source.erase).relabel (initialRelabelling source 0)=source:=initialRelabelling_factor source 0
    simpa only [factor] using lookup_relabel occurrence.lookup (initialRelabelling source 0)
  let redex : SelectedRedex source F:=global_redex geometry.selected
  cases direction : cut.forward with
  | true =>
    have ports : geometry.edge.fromPort=geometry.selected.afterPort kind ∧geometry.edge.toPort=finish := by
      simpa only [direction,if_true] using geometry.ports
    have contextEq : ctx=geometry.selected.afterPort kind :=
      (source_edge_departure env ctx node).symm.trans ((congrArg SourceEdge.fromPort edgeEq).trans ports.1)
    have departure:=occurrence_after_marker (init_is_INIT _) occurrence geometry.selected contextEq
    have globalDeparture : position=departurePosition redex kind:=by cases kind <;> exact departure
    have lastAtom : localNode.label.lastAtom=some n := by
      apply last_atom_suffix (pre:=pre++[bar kind d])
      simpa only [direction,Label.readLetters,if_true,List.append_assoc,List.cons_append,List.nil_append] using boundary
    have trace:=local_trace_global history labels (local_last_atom_trace history lookup occurrence.lookup atomic lastAtom)
    have notLambda:=forward_original_not_lambda labels cut more direction trace
    have auxiliary : AuxiliaryAt source position := by
      constructor
      · rintro ⟨parent,a,fn,arg,split,atParent⟩
        have last:=congrArg List.getLast? (globalDeparture.symm.trans split)
        cases kind <;> simp [departurePosition] at last
      · exact notLambda
    have sourceSpec : Source source position (some (redex.vertex kind)) := by
      cases kind with
      | false => exact ⟨.arg,_,.appArg _,globalDeparture,redex.lookup,.arg⟩
      | true => exact ⟨.body,_,.lamBody _,globalDeparture,redex.function_lookup,.body⟩
    have targetSpec:=true_far_target labels history cut snapshot canonical direction lookup occurrence.lookup atomic lastAtom
    exact ⟨⟨position,env,ctx,node,occurrence,atomic,globalLookup,redex,auxiliary,by simpa only [direction,if_true] using And.intro sourceSpec targetSpec⟩⟩
  | false =>
    have ports : geometry.edge.fromPort=routeCtx ∧geometry.edge.toPort=geometry.selected.beforePort kind := by
      simpa only [direction,if_false,Bool.false_eq_true] using geometry.ports
    have contextEq : ctx=routeCtx :=
      (source_edge_departure env ctx node).symm.trans ((congrArg SourceEdge.fromPort edgeEq).trans ports.1)
    have arrival:=occurrence_before_marker (init_is_INIT _) occurrence geometry.selected
      ((congrArg SourceEdge.toPort edgeEq).trans ports.2)
    have sourceSpec:=false_far_source labels history (actual_old_routes old history) cut more snapshot canonical
      direction lookup route.forget occurrence contextEq
    have notFunction : ¬∃parent a fn arg,position=parent++[Step.fn] ∧source.subterm parent=some (.app a fn arg) := by
      rintro ⟨parent,a,fn,arg,split,atParent⟩
      have role:=original_incoming_role history lookup route.forget occurrence contextEq
      have last : position.getLast?=some .fn := by rw [split];simp
      have forward:=(cut.reading.nonredex_forward_iff_function (nonterminal_not_redex cut.remaining more)).mpr (role.symm.trans last)
      cases direction.symm.trans forward
    have targetSpec : Target source position (some (redex.vertex (!kind))) := by
      cases kind with
      | true => exact Or.inl arrival
      | false =>
        obtain ⟨stamp,index,rest,nodeEq,split,depth⟩:=arrival
        exact Or.inr ⟨stamp.relabel (initialRelabelling source 0),index,redex.degree,redex.body,rest,
          by simpa only [nodeEq,LTerm.relabel] using globalLookup,redex.function_lookup,split,depth⟩
    have notLambda : ¬∃stamp body,source.subterm position=some (.lam stamp body) := by
      rintro ⟨stamp,body,atLambda⟩
      cases kind with
      | true =>
        change position=redex.position at arrival
        have selectedLookup:=redex.lookup
        rw [←arrival] at selectedLookup
        rw [selectedLookup] at atLambda
        cases atLambda
      | false =>
        obtain ⟨a,index,rest,nodeEq,split,depth⟩:=arrival
        rw [nodeEq] at globalLookup
        simp only [LTerm.relabel] at globalLookup
        rw [globalLookup] at atLambda
        cases atLambda
    exact ⟨⟨position,env,ctx,node,occurrence,atomic,globalLookup,redex,⟨notFunction,notLambda⟩,
      by simpa only [direction,if_false,Bool.false_eq_true] using And.intro sourceSpec targetSpec⟩⟩

open Lamping.AG

structure Comparison (source : LTerm) (F : List Path) (n m : Nat) (kind forward : Bool)
    (closed : Closed source.erase) (leftFar rightFar : ProperPosition source) where
  left : OriginalFarAtom source F n kind forward leftFar
  right : OriginalFarAtom source F m kind forward rightFar
  labelEq : SyntaxIncidence.label source left.edge=SyntaxIncidence.label source right.edge
  sourceIso : SuccessfulEndpointIso source closed (SyntaxIncidence.source source left.edge) (SyntaxIncidence.source source right.edge)
  targetIso : SuccessfulEndpointIso source closed (SyntaxIncidence.target source closed left.edge) (SyntaxIncidence.target source closed right.edge)

def compare_original_atoms
    {current : LTerm} {labels : History ps source current}
    {leftCut : ActualUnsafeMarkerCut F ps source current degree leftStart leftEdges}
    {rightCut : ActualUnsafeMarkerCut F ps source current degree rightStart rightEdges}
    {leftSnapshot : IncomingIncidenceSnapshot current leftCut.edge}
    {rightSnapshot : IncomingIncidenceSnapshot current rightCut.edge}
    (closed : Closed source.erase)
    (selected : ∀name∈F,source.degreeAt name=some alpha)
    (leftCanonical : CanonicalAfterFarOutput labels leftCut leftSnapshot)
    (rightCanonical : CanonicalAfterFarOutput labels rightCut rightSnapshot)
    (good : CanonicalFarFullComparison closed leftCanonical rightCanonical)
    (left : OriginalFarAtom source F n kind forward leftCanonical.sourceProper)
    (right : OriginalFarAtom source F m kind forward rightCanonical.sourceProper)
    (sameImage : initialRelabelling source 0 n=initialRelabelling source 0 m) :
    Comparison source F n m kind forward closed leftCanonical.sourceProper rightCanonical.sourceProper := by
  have farIso : SuccessfulEndpointIso source closed (some leftCanonical.sourceProper) (some rightCanonical.sourceProper) :=
    ⟨leftCanonical.sourceEdges,rightCanonical.sourceEdges,leftCanonical.sourceChain,rightCanonical.sourceChain,good.2⟩
  have selectedIso : SuccessfulEndpointIso source closed (some (left.selected.vertex kind)) (some (right.selected.vertex kind)) :=
    SelectedRedex.endpoint_iso closed selected left.selected right.selected kind
  have oppositeIso : SuccessfulEndpointIso source closed (some (left.selected.vertex (!kind))) (some (right.selected.vertex (!kind))) :=
    SelectedRedex.endpoint_iso closed selected left.selected right.selected (!kind)
  refine ⟨left,right,left.full_image.trans (sameImage.trans right.full_image.symm),?_,?_⟩
  · cases forward with
    | true =>
      have ls : Source source left.position (some (left.selected.vertex kind)):=left.endpoints.1
      have rs : Source source right.position (some (right.selected.vertex kind)):=right.endpoints.1
      rw [SyntaxIncidence.source_eq_of_spec source left.edge ls,SyntaxIncidence.source_eq_of_spec source right.edge rs]
      exact selectedIso
    | false =>
      have ls : Source source left.position (some leftCanonical.sourceProper):=left.endpoints.1
      have rs : Source source right.position (some rightCanonical.sourceProper):=right.endpoints.1
      rw [SyntaxIncidence.source_eq_of_spec source left.edge ls,SyntaxIncidence.source_eq_of_spec source right.edge rs]
      exact farIso
  · cases forward with
    | true =>
      have lt : Target source left.position (some leftCanonical.sourceProper):=left.endpoints.2
      have rt : Target source right.position (some rightCanonical.sourceProper):=right.endpoints.2
      rw [SyntaxIncidence.target_eq_of_spec source closed left.edge lt,SyntaxIncidence.target_eq_of_spec source closed right.edge rt]
      exact farIso
    | false =>
      have lt : Target source left.position (some (left.selected.vertex (!kind))):=left.endpoints.2
      have rt : Target source right.position (some (right.selected.vertex (!kind))):=right.endpoints.2
      rw [SyntaxIncidence.target_eq_of_spec source closed left.edge lt,SyntaxIncidence.target_eq_of_spec source closed right.edge rt]
      exact oppositeIso

section
variable {N B W : Type} [Graph.FiniteNames N] [Graph.FiniteNames B] [Graph.FiniteNames W]
variable {g : Graph.Net signature N B W} {root : B}

theorem Comparison.atom_words_equal
    (out : Comparison source F n m kind forward closed leftFar rightFar)
    (matching : Matches g root source.erase)
    (sourceSelection : OccurrenceFragmentSelection source g root)
    (selection : SourceEdgeSelection (initLabels source.erase) g root)
    (auxiliary : AuxiliarySeparation closed sourceSelection) :
    selection.atomWord n=selection.atomWord m := by
  have localMatching : Matches g root (initLabels source.erase).erase:=by simpa only [erase_initLabels] using matching
  have leftEval:=selection.atomWord_occurrence_segments (init_is_INIT _) localMatching matching
    out.left.occurrence out.left.atomic (sourceSelection out.left.edge)
  have rightEval:=selection.atomWord_occurrence_segments (init_is_INIT _) localMatching matching
    out.right.occurrence out.right.atomic (sourceSelection out.right.edge)
  have same : (sourceSelection out.left.edge).fragment.segments=(sourceSelection out.right.edge).fragment.segments := by
    apply Classical.byContradiction
    intro different
    exact auxiliary out.left.edge out.right.edge out.left.auxiliary out.right.auxiliary out.labelEq different ⟨out.sourceIso,out.targetIso⟩
  exact leftEval.trans (same.trans rightEval.symm)
end

end NonterminalFarBoundary
end Lamping.Lambda.Labelled

#print axioms Lamping.Lambda.Labelled.NonterminalFarBoundary.relabel_node_history
#print axioms Lamping.Lambda.Labelled.NonterminalFarBoundary.selected_app_parent
#print axioms Lamping.Lambda.Labelled.NonterminalFarBoundary.selected_lam_parent
#print axioms Lamping.Lambda.Labelled.NonterminalFarBoundary.selected_route_far_boundary

#print axioms Lamping.Lambda.Labelled.NonterminalFarBoundary.local_last_atom_trace
#print axioms Lamping.Lambda.Labelled.NonterminalFarBoundary.local_trace_global
#print axioms Lamping.Lambda.Labelled.NonterminalFarBoundary.true_far_target

#print axioms Lamping.Lambda.Labelled.NonterminalFarBoundary.app_parent_origin

#print axioms Lamping.Lambda.Labelled.NonterminalFarBoundary.lam_parent_origin

#print axioms Lamping.Lambda.Labelled.NonterminalFarBoundary.arg_far_source

#print axioms Lamping.Lambda.Labelled.NonterminalFarBoundary.body_far_source

#print axioms Lamping.Lambda.Labelled.NonterminalFarBoundary.false_far_source

#print axioms Lamping.Lambda.Labelled.NonterminalFarBoundary.actual_old_far_atom

#print axioms Lamping.Lambda.Labelled.NonterminalFarBoundary.compare_original_atoms

#print axioms Lamping.Lambda.Labelled.NonterminalFarBoundary.Comparison.atom_words_equal
