import Lamping.Lamping.PairedStreamCuts
import Lamping.Lamping.PairedStreamAppend
import Lamping.Lamping.PairedStreamAssignments
import Lamping.Lamping.RootTypedDetours
namespace Lamping.AG
open Graph
private theorem app_context_flow (actual : Graph.Label signature) (p : Port actual.sort) (i : Nat)
    (lab : actual=label .app i) (role : HEq p appCtx) (base : Bool) : flowPort actual.sort base p=false := by
  subst actual
  cases eq_of_heq role
  rfl
private theorem same_lambda_port {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} {n m : N}
    {T : Type} {canonical : T} {p : Port (g.label n).sort} {q : Port (g.label m).sort}
    (same : n=m) (left : HEq p canonical) (right : HEq q canonical) :
    (.inl ⟨n,p⟩ : Endpoint g)=.inl ⟨m,q⟩ := by
  subst m
  cases eq_of_heq (left.trans right.symm)
  rfl
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}

theorem ExpandedBindingLoop.beta_ports {loop : List (Endpoint g)} {seam output : Context}
    (binding : ExpandedBindingLoop g loop seam output) (edge : BetaEdge g) (same : binding.binder=edge.lam) :
    loop.head?=some (.inl ⟨edge.lam,edge.lamBody⟩) ∧
      loop.getLast?=some (g.wire (.inl ⟨edge.lam,edge.lamBind⟩)) ∧
      Context.SameShell edge.index seam output := by
  have body := same_lambda_port same binding.body_role edge.lamBody_role
  have bind := same_lambda_port same binding.bind_role edge.lamBind_role
  have index : (g.label binding.binder).index=edge.index := by rw [same,edge.lamLabel]; rfl
  exact ⟨binding.start.trans (congrArg some body),
    binding.finish.trans (congrArg (fun e => some (g.wire e)) bind),by simpa only [index] using binding.shell⟩

/-- Construct an inserted stream from actual PREVIOUS paired assignments and
an actual same-assignment expanded binding loop. Both the prefix and loop
may be expanded. The new whole path's labels are derived, never assumed.
Bare generatedness/support alone does not satisfy these input premises. -/
theorem RootInputs.insert_expanded_paired_body
    (inputs : RootInputs g root) {boundary : B → Bool} (flow : FlowBalance g boundary)
    (positive : boundary root=true) {heights : B → Int} (balance : IndexedLevelBalance g heights)
    (rootDepth : heights root=0) (nesting : Nesting g root) (transparency : Transparency g root)
    (edge : BetaEdge g) (pre loop suffix : List (Endpoint g))
    (argument : ∀ requested : Context,∃ output count,
      BetaDetourBlocks g (pre++edge.argEnd::suffix) requested output count)
    {a seam endBody : Context} {bodyCount : Nat}
    (body : BetaDetourBlocks g (pre++edge.principal++loop) a endBody bodyCount)
    (prefixLabels : ExpandedLabelling g pre a seam)
    (binding : ExpandedBindingLoop g loop seam endBody) (sameBinder : binding.binder=edge.lam)
    (prefixRoot : pre.head?=some (.inr (.inl root)))
    (prefixEnd : pre.getLast?=some (g.wire (.inl ⟨edge.app,edge.appCtx⟩)))
    (terminal : Endpoint g) (role : ProperRole) (level : Nat)
    (tailEnd : (edge.argEnd::suffix).getLast?=some (g.wire terminal))
    (atTerminal : AtProperRole g root terminal role level) (incoming : role.incoming) :
    ∃ count,∀ requested : Context,∃ output,
      CoherentExpandedCore g root
        (pre++edge.principal++loop++edge.reverseRoute++[edge.argEnd]++suffix) requested output ∧
      BetaDetourBlocks g
        (pre++edge.principal++loop++edge.reverseRoute++[edge.argEnd]++suffix) requested output count := by
  obtain ⟨_loopStart,loopEnd,shell⟩ := binding.beta_ports edge sameBinder
  have prefixCutPositive : flowEndpoint g flow.nodes boundary flow.vertices
      (g.wire (.inl ⟨edge.app,edge.appCtx⟩))=true := by
    rw [flow.wiring]
    have negative := app_context_flow (g.label edge.app) edge.appCtx edge.index edge.appLabel edge.appCtx_role (flow.nodes edge.app)
    change flowEndpoint g flow.nodes boundary flow.vertices (.inl ⟨edge.app,edge.appCtx⟩)=false at negative
    rw [negative]
    rfl
  have body' : BetaDetourBlocks g (pre++(edge.principal++loop)) a endBody bodyCount := by
    simpa only [List.append_assoc] using body
  obtain ⟨_prefixCount,_prefixBound,prefixStream⟩ :=
    body'.prefix_at_positive_assignment flow positive prefixLabels prefixEnd prefixCutPositive
  obtain ⟨argumentInput,argumentPrefix⟩ := prefixStream.relabel_app_prefix_indexed
    flow positive balance rootDepth edge prefixRoot prefixEnd shell
  obtain ⟨result,argumentCount,argumentStream⟩ := argument argumentInput
  have beforeArgument : ExpandedLabelling g (pre++[edge.argEnd]) argumentInput endBody := by
    apply (argumentPrefix.labelling g).splice prefixEnd (.single edge.argEnd endBody) rfl
    simpa only [Pairing.involutive] using ExpandedTurn.ordinary (edge.app_arg_turn endBody)
  have argumentPositive : flowEndpoint g flow.nodes boundary flow.vertices edge.argEnd=true :=
    (AtProperRole.appArg edge.app edge.appArg edge.index edge.appLabel edge.appArg_role).outgoing_flow
      trivial flow.nodes boundary flow.vertices positive
  obtain ⟨tailCount,_tailBound,tailStream⟩ :=
    argumentStream.suffix_at_positive_assignment flow positive beforeArgument argumentPositive
  have bodyEnd : (pre++edge.principal++loop).getLast?=
      some (g.wire (.inl ⟨edge.lam,edge.lamBind⟩)) := by
    simp only [List.getLast?_append,loopEnd,Option.some_or]
  have seed := body.append_backward_paired edge tailStream bodyEnd rfl
  have rooted : (pre++edge.principal++loop++edge.reverseRoute++(edge.argEnd::suffix)).head?=
      some (.inr (.inl root)) := by
    simp only [List.head?_append,prefixRoot,Option.some_or]
  have finish : (pre++edge.principal++loop++edge.reverseRoute++(edge.argEnd::suffix)).getLast?=
      some (g.wire terminal) := by
    simp only [List.getLast?_append,tailEnd,Option.some_or]
  have allInputs := seed.typed_root_inputs_indexed flow positive balance rootDepth inputs nesting transparency
    rooted terminal role level finish atTerminal incoming
  refine ⟨bodyCount+tailCount+1,?_⟩
  intro requested
  obtain ⟨output,core⟩ := allInputs requested
  have paired := seed.relabel (core.labelling g)
  exact ⟨output,by simpa only [List.append_assoc,List.singleton_append] using core,
    by simpa only [List.append_assoc,List.singleton_append] using paired⟩
end
end Lamping.AG
