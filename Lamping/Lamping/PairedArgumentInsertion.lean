import Lamping.Lamping.OrdinaryInsertionCoherence
import Lamping.Lamping.PairedStreamOrdinarySuffix
namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}

/-- An ordinary source body can be inserted into an already constructed
paired argument. The argument totality/count is an actual earlier construction,
not totality of the NEW result; the new stream has one additional block. -/
theorem RootInputs.insert_into_paired_argument
    (inputs : RootInputs g root) {boundary : B → Bool} (flow : FlowBalance g boundary)
    (positive : boundary root=true) {heights : B → Int} (balance : IndexedLevelBalance g heights)
    (rootDepth : heights root=0) (nesting : Nesting g root) (transparency : Transparency g root)
    (edge : BetaEdge g) (pre loop suffix : List (Endpoint g)) (count : Nat)
    (argument : ∀ requested : Context,∃ output,
      BetaDetourBlocks g (pre++edge.argEnd::suffix) requested output count)
    {a middle final : Context} (binding : BindingLoop g loop middle final)
    (sameBinder : binding.binder=edge.lam) (prefixLabels : Labelling g pre a middle)
    (prefixRoot : pre.head?=some (.inr (.inl root)))
    (prefixEnd : pre.getLast?=some (g.wire (.inl ⟨edge.app,edge.appCtx⟩)))
    (terminal : Endpoint g) (role : ProperRole) (level : Nat)
    (tailEnd : (edge.argEnd::suffix).getLast?=some (g.wire terminal))
    (atTerminal : AtProperRole g root terminal role level) (incoming : role.incoming) :
    ∀ requested : Context,∃ output,CoherentExpandedCore g root
      (pre++edge.principal++loop++edge.reverseRoute++[edge.argEnd]++suffix) requested output ∧
      BetaDetourBlocks g (pre++edge.principal++loop++edge.reverseRoute++[edge.argEnd]++suffix)
        requested output (count+1) := by
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
  obtain ⟨output,argumentStream⟩ := argument argumentInput
  have before : Labelling g (pre++[edge.argEnd]) argumentInput final := by
    apply argumentPrefix.append_seam (.single edge.argEnd final)
    intro e f finish head
    have eEq := Option.some.inj (finish.symm.trans prefixEnd)
    have fEq : f=edge.argEnd := Option.some.inj head.symm
    rw [eEq,fEq,Pairing.involutive]
    exact edge.app_arg_turn final
  have tailStream := argumentStream.ordinary_suffix before
  have bodyEnd : (pre++edge.principal++loop).getLast?=
      some (g.wire (.inl ⟨edge.lam,edge.lamBind⟩)) := by
    simp only [List.getLast?_append,loopEnd,Option.some_or]
  have stream := tailStream.append_backward g edge bodyLabels bodyEnd rfl
  have rooted : (pre++edge.principal++loop++edge.reverseRoute++(edge.argEnd::suffix)).head?=
      some (.inr (.inl root)) := by
    repeat rw [List.head?_append]
    rw [prefixRoot]; rfl
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
end
end Lamping.AG


