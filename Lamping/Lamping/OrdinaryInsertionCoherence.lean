import Lamping.Lamping.RootTypedDetours
import Lamping.Lamping.InitialPathConstruction
import Lamping.Lamping.PairedStreamAssignments
namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}

/-- Construct actual coherent labels for a single ordinary-body insertion.
The premises are genuine ordinary source paths sharing one literal prefix,
not labels or generation of the inserted path. Its argument is reset using
structural indexed balance, then relabelled through source RootInputs. -/
theorem RootInputs.ordinary_insert_coherent_streams
    (inputs : RootInputs g root) {boundary : B → Bool} (flow : FlowBalance g boundary)
    (positive : boundary root=true) {heights : B → Int} (balance : IndexedLevelBalance g heights)
    (rootDepth : heights root=0) (nesting : Nesting g root) (transparency : Transparency g root)
    (edge : BetaEdge g) (pre loop suffix : List (Endpoint g))
    (argument : RootAccess g root) (argumentSplit : argument.val=pre++edge.argEnd::suffix)
    {a middle final : Context} (binding : BindingLoop g loop middle final)
    (sameBinder : binding.binder=edge.lam) (prefixLabels : Labelling g pre a middle)
    (prefixRoot : pre.head?=some (.inr (.inl root)))
    (prefixEnd : pre.getLast?=some (g.wire (.inl ⟨edge.app,edge.appCtx⟩))) :
    ∀ requested : Context,∃ output,CoherentExpandedCore g root
      (pre++edge.principal++loop++edge.reverseRoute++[edge.argEnd]++suffix) requested output ∧
      BetaDetourBlocks g (pre++edge.principal++loop++edge.reverseRoute++[edge.argEnd]++suffix) requested output 1 := by
  obtain ⟨loopStart,loopEnd,shell⟩ := binding.beta_ports edge sameBinder
  have frontLabels : Labelling g (pre++edge.principal) a middle := by
    apply prefixLabels.append_seam (edge.principal_labeling middle)
    intro e f finish head
    have eEq := Option.some.inj (finish.symm.trans prefixEnd)
    have fEq := Option.some.inj (head.symm.trans edge.principalStart)
    rw [eEq,fEq,Pairing.involutive]
    exact edge.app_fun_turn middle
  have frontEnd : (pre++edge.principal).getLast?=some (g.wire edge.ctxEnd) := by
    simp only [List.getLast?_append,edge.principalEnd,Option.some_or,BetaEdge.ctxEnd]
  have bodyLabels : Labelling g (pre++edge.principal++loop) a final := by
    apply frontLabels.append_seam binding.proper
    intro e f finish head
    have eEq := Option.some.inj (finish.symm.trans frontEnd)
    have fEq := Option.some.inj (head.symm.trans loopStart)
    rw [eEq,fEq,Pairing.involutive]
    exact edge.lam_body_turn middle
  have prefixForward := prefixLabels.root_forward_of_flow flow root prefixRoot positive
  obtain ⟨argumentInput,argumentPrefix⟩ :=
    balance.relabel_app_prefix rootDepth edge prefixLabels prefixForward prefixRoot prefixEnd shell
  obtain ⟨output,argumentLabels⟩ := inputs.access argument argumentInput
  rw [argumentSplit] at argumentLabels
  have tailExpanded := edge.argument_tail_labeling pre suffix argumentPrefix.expanded prefixEnd argumentLabels.expanded
  have argAt : argument.val[pre.length]?=some edge.argEnd := by
    rw [argumentSplit,List.getElem?_append_right (Nat.le_refl _),Nat.sub_self]; rfl
  have tailForward := argument.property.1.2.suffix_at pre.length _ argAt
  rw [argumentSplit,List.drop_append] at tailForward
  simp only [List.drop_length,Nat.sub_self,List.drop_zero,List.nil_append] at tailForward
  have tailLabels := tailExpanded.ordinary_of_forward g tailForward
  have bodyEnd : (pre++edge.principal++loop).getLast?=some (g.wire (.inl ⟨edge.lam,edge.lamBind⟩)) := by
    simp only [List.getLast?_append,loopEnd,Option.some_or]
  have stream := (tailLabels.detour_blocks g).append_backward g edge bodyLabels bodyEnd rfl
  have rooted : (pre++edge.principal++loop++edge.reverseRoute++(edge.argEnd::suffix)).head?=
      some (.inr (.inl root)) := by
    repeat rw [List.head?_append]
    rw [prefixRoot]; rfl
  obtain ⟨terminal,role,level,argumentEnd,atTerminal,incoming⟩ := argument.incoming_endpoint
  have tailEnd : (edge.argEnd::suffix).getLast?=some (g.wire terminal) := by
    rw [argumentSplit,List.getLast?_append] at argumentEnd
    cases h : (edge.argEnd::suffix).getLast? with
    | none => cases List.getLast?_eq_none_iff.mp h
    | some e => rw [h,Option.some_or] at argumentEnd; exact argumentEnd
  have finish : (pre++edge.principal++loop++edge.reverseRoute++(edge.argEnd::suffix)).getLast?=
      some (g.wire terminal) := by
    simp only [List.getLast?_append,tailEnd,Option.some_or]
  have allInputs := stream.typed_root_inputs_indexed flow positive balance rootDepth inputs nesting transparency
    rooted terminal role level finish atTerminal incoming
  intro requested
  obtain ⟨result,coherent⟩ := allInputs requested
  have paired := stream.relabel (coherent.labelling g)
  exact ⟨result,by simpa only [List.append_assoc,List.singleton_append] using coherent,
    by simpa only [List.append_assoc,List.singleton_append] using paired⟩
/-- Original coherence-only interface, retained unchanged. The stronger
paired-shape result above records one actual reverse block. -/
theorem RootInputs.ordinary_insert_coherent
    (inputs : RootInputs g root) {boundary : B → Bool} (flow : FlowBalance g boundary)
    (positive : boundary root=true) {heights : B → Int} (balance : IndexedLevelBalance g heights)
    (rootDepth : heights root=0) (nesting : Nesting g root) (transparency : Transparency g root)
    (edge : BetaEdge g) (pre loop suffix : List (Endpoint g))
    (argument : RootAccess g root) (argumentSplit : argument.val=pre++edge.argEnd::suffix)
    {a middle final : Context} (binding : BindingLoop g loop middle final)
    (sameBinder : binding.binder=edge.lam) (prefixLabels : Labelling g pre a middle)
    (prefixRoot : pre.head?=some (.inr (.inl root)))
    (prefixEnd : pre.getLast?=some (g.wire (.inl ⟨edge.app,edge.appCtx⟩))) :
    ∀ requested : Context,∃ output,CoherentExpandedCore g root
      (pre++edge.principal++loop++edge.reverseRoute++[edge.argEnd]++suffix) requested output := by
  intro requested
  obtain ⟨output,coherent,_paired⟩ := inputs.ordinary_insert_coherent_streams flow positive balance rootDepth
    nesting transparency edge pre loop suffix argument argumentSplit binding sameBinder prefixLabels
    prefixRoot prefixEnd requested
  exact ⟨output,coherent⟩
end
end Lamping.AG

