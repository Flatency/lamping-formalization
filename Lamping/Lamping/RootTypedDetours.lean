import Lamping.Lamping.RootBinderUniform
import Lamping.Lamping.RootPathInputs
import Lamping.Lamping.MarkerBinderUniform
import Lamping.Lamping.BetaDetourCoherence
namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}

private theorem head_prefix {T : Type} {pre tail : List T} {e : T}
    (nonempty : pre≠[]) (head : (pre++tail).head?=some e) : pre.head?=some e := by
  cases pre with
  | nil => exact False.elim (nonempty rfl)
  | cons x xs => exact head

private theorem last_suffix {T : Type} (pre tail : List T) (nonempty : tail≠[]) :
    (pre++tail).getLast?=tail.getLast? := by
  have existsLast : tail.getLast?≠none := by
    intro empty
    exact nonempty (List.getLast?_eq_none_iff.mp empty)
  cases last : tail.getLast? with
  | none => exact False.elim (existsLast last)
  | some x => simp only [List.getLast?_append,last,Option.some_or]

/-- Total-input reconstruction for an actual paired stream with a proper
incoming terminal. This is about the SAME ordered stream, rather than every
erased bare derivation. The first backward block's ordinary body is relabelled
by root-input existence; N/T and finite marker separation preserve its selected binder
occurrence's shell. The argument stream has strictly fewer backward blocks. -/
theorem BetaDetourBlocks.typed_root_inputs_indexed {boundary : B → Bool} (flow : FlowBalance g boundary)
    (rootPolarity : boundary root=true) {heights : B → Int}
    (balance : IndexedLevelBalance g heights) (rootDepth : heights root=0)
    (inputs : RootInputs g root) (nesting : Nesting g root) (transparency : Transparency g root)
    {es : List (Endpoint g)} {input output : Context} {count : Nat}
    (path : BetaDetourBlocks g es input output count)
    (rooted : es.head?=some (.inr (.inl root)))
    (terminal : Endpoint g) (role : ProperRole) (level : Nat)
    (finish : es.getLast?=some (g.wire terminal))
    (atTerminal : AtProperRole g root terminal role level) (incoming : role.incoming) :
    ∀ requested : Context, ∃ result,CoherentExpandedCore g root es requested result := by
  induction count using Nat.strongRecOn generalizing es input output with
  | ind count ih =>
    intro requested
    by_cases zero : count=0
    · subst count
      have labels := path.zero_ordinary g
      have forward := labels.root_forward_of_flow flow root rooted rootPolarity
      obtain ⟨result,changed⟩ := inputs es input output terminal role level labels forward rooted finish
        atTerminal incoming requested
      exact ⟨result,.base changed forward rooted⟩
    · obtain ⟨edge,pre,tail,seam,remaining,countEq,decomp,preLabels,preEnd,tailHead,rest⟩ :=
        path.first_backward g (by omega)
      have preRoot : pre.head?=some (.inr (.inl root)) :=
        head_prefix preLabels.nonempty (by simpa only [List.append_assoc,decomp] using rooted)
      have preForward := preLabels.root_forward_of_flow flow root preRoot rootPolarity
      obtain ⟨stem,loop,middle,binding,prefixSplit,sameBinder,stemEnd,stemLabels⟩ :=
        transparency pre input seam edge.lam edge.lamCtx edge.lamBody edge.lamBind
          (congrArg Label.sort edge.lamLabel) edge.lamCtx_role edge.lamBody_role edge.lamBind_role
          preRoot preEnd preForward preLabels
      have stemNonempty : stem≠[] := by intro empty; rw [empty] at stemEnd; cases stemEnd
      have stemRoot := head_prefix stemNonempty (by rw [←prefixSplit]; exact preRoot)
      have stemForward := stemLabels.root_forward_of_flow flow root stemRoot rootPolarity
      obtain ⟨preApp,principalSplit,appEnd,appRoot,appForward,appLabels⟩ :=
        edge.principal_prefix_reflection stemForward stemRoot stemLabels stemEnd
      obtain ⟨loopStart,loopEnd,shell⟩ := binding.beta_ports edge sameBinder
      obtain ⟨originalArgumentInput,originalApp⟩ := balance.relabel_app_prefix rootDepth
        edge appLabels appForward appRoot appEnd shell
      have originalArgument := rest.splice_ordinary g originalApp appEnd tailHead (by
        simpa only [Pairing.involutive] using edge.app_arg_turn seam)
      obtain ⟨suffix,tailSplit⟩ := List.head?_eq_some_iff.mp tailHead
      have tailNonempty : tail≠[] := by rw [tailSplit]; simp
      have tailFinish : tail.getLast?=some (g.wire terminal) := by
        rw [decomp,last_suffix _ _ tailNonempty] at finish
        exact finish
      have argumentFinish : (preApp++tail).getLast?=some (g.wire terminal) := by
        rw [last_suffix _ _ tailNonempty]; exact tailFinish
      have argumentRoot : (preApp++tail).head?=some (.inr (.inl root)) := by
        cases preApp with
        | nil => cases appRoot
        | cons x xs => exact appRoot
      obtain ⟨newBodyOutput,newBodyLabels⟩ := inputs pre input seam (.inl ⟨edge.lam,edge.lamBind⟩)
        .lamBind edge.index preLabels preForward preRoot preEnd
        (.lamBind edge.lam edge.lamBind edge.index edge.lamLabel edge.lamBind_role) trivial requested
      have bodySplit : pre=preApp++edge.principal++loop := by rw [prefixSplit,principalSplit]
      have appNonempty : preApp≠[] := by intro empty; rw [empty] at appEnd; cases appEnd
      obtain ⟨newMiddle,newApp⟩ := (show Labelling g (preApp++(edge.principal++loop)) requested newBodyOutput by
        simpa only [bodySplit,List.append_assoc] using newBodyLabels).prefix appNonempty
      have newStem : Labelling g stem requested newMiddle := by
        have expanded : ExpandedLabelling g (preApp++edge.principal) requested newMiddle :=
          newApp.expanded.splice appEnd (edge.principal_labeling newMiddle).expanded edge.principalStart (by
            simpa only [Pairing.involutive] using ExpandedTurn.ordinary (edge.app_fun_turn newMiddle))
        rw [←principalSplit] at expanded
        exact expanded.ordinary_of_forward g stemForward
      have newShell := Marker.binder_shell_stable_rootInputs inputs nesting
        transparency edge pre stem loop input middle seam preRoot preForward preEnd
        preLabels prefixSplit stemLabels stemEnd shell requested newMiddle newBodyOutput newBodyLabels newStem
      obtain ⟨newArgumentInput,newArgumentPrefix⟩ := balance.relabel_app_prefix rootDepth edge
        newApp appForward appRoot appEnd newShell
      obtain ⟨result,newArgument⟩ := ih remaining (by omega) originalArgument argumentRoot
        argumentFinish newArgumentInput
      have newLoopExpanded := edge.body_loop_labeling preApp loop newApp.expanded appEnd loopStart
        (show ExpandedLabelling g (preApp++edge.principal++loop) requested newBodyOutput by
          rw [←bodySplit]; exact newBodyLabels.expanded)
      have newLoop : Labelling g loop newMiddle newBodyOutput :=
        newLoopExpanded.ordinary_of_forward g binding.forward
      have bindingIndex : (g.label binding.binder).index=edge.index := by rw [sameBinder,edge.lamLabel]; rfl
      let newBinding : BindingLoop g loop newMiddle newBodyOutput :=
        { binder := binding.binder, isLam := binding.isLam, body := binding.body, bind := binding.bind,
          body_role := binding.body_role, bind_role := binding.bind_role,
          start := binding.start, finish := binding.finish, proper := newLoop,
          forward := binding.forward, shell := by rw [bindingIndex]; exact newShell }
      rw [tailSplit] at newArgument
      have body : CoherentExpandedCore g root (preApp++edge.principal++loop) requested newBodyOutput := by
        rw [←bodySplit]
        exact .base newBodyLabels preForward preRoot
      have inserted : CoherentExpandedCore g root
          (preApp++edge.principal++loop++edge.reverseRoute++[edge.argEnd]++suffix) requested result :=
        .insert edge preApp loop suffix newArgument body newApp.expanded newArgumentPrefix.expanded
          appEnd loopStart loopEnd newBinding (by exact sameBinder)
      refine ⟨result,?_⟩
      have fullSplit : es=preApp++edge.principal++loop++edge.reverseRoute++[edge.argEnd]++suffix := by
        rw [decomp,bodySplit,tailSplit]
        simp only [List.append_assoc,List.singleton_append]
      rw [fullSplit]
      exact inserted

/-- A nonempty prefix inherits arbitrary root inputs from its supplied
actual typed-terminal stream extension. No extension is invented. -/
theorem BetaDetourBlocks.typed_prefix_inputs_indexed {boundary : B → Bool} (flow : FlowBalance g boundary)
    (rootPolarity : boundary root=true) {heights : B → Int}
    (balance : IndexedLevelBalance g heights) (rootDepth : heights root=0)
    (inputs : RootInputs g root) (nesting : Nesting g root) (transparency : Transparency g root)
    {pre tail : List (Endpoint g)} {input output : Context} {count : Nat}
    (path : BetaDetourBlocks g (pre++tail) input output count)
    (rooted : (pre++tail).head?=some (.inr (.inl root)))
    (terminal : Endpoint g) (role : ProperRole) (level : Nat)
    (finish : (pre++tail).getLast?=some (g.wire terminal))
    (atTerminal : AtProperRole g root terminal role level) (incoming : role.incoming)
    (nonempty : pre≠[]) :
    ∀ requested : Context,CoherentExpandedPrefix g root pre requested := by
  intro requested
  obtain ⟨result,core⟩ := path.typed_root_inputs_indexed flow rootPolarity balance rootDepth inputs nesting transparency rooted
    terminal role level finish atTerminal incoming requested
  exact (core.prefix g).takePrefix g nonempty
end
end Lamping.AG


