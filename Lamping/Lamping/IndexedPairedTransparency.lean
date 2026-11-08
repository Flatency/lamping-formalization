import Lamping.Lamping.IndexedDetourTransparency
import Lamping.Lamping.IndexedBetaCoherence
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
  cases point : tail.getLast? with
  | none => exact False.elim (nonempty (List.getLast?_eq_none_iff.mp point))
  | some e => simp only [List.getLast?_append,point,Option.some_or]

/-- Same-assignment transparency for actual finite paired streams. Strong
induction removes the first backward block, where the preceding path is still
ordinary. Old T supplies that actual assignment's loop shell; structural indexed balance relabels
only its genuine proper app prefix. The smaller argument stream's binder is
transported by transparency_splice, including the earlier-binder case.
No full Independence, arbitrary erased grammar, completion, new-graph T or nesting is assumed. -/
theorem BetaDetourBlocks.transparency_indexed {boundary : B → Bool} (flow : FlowBalance g boundary)
    (rootPolarity : boundary root=true) {heights : B → Int}
    (balance : IndexedLevelBalance g heights) (rootDepth : heights root=0)
    (transparency : Transparency g root) {es : List (Endpoint g)} {input output : Context} {count : Nat}
    (path : BetaDetourBlocks g es input output count)
    (node : N) (ctx body bind : Port (g.label node).sort)
    (sort : (g.label node).sort=.op .lam)
    (ctxRole : HEq ctx (Sum.inl () : Port (.op .lam)))
    (bodyRole : HEq body AG.lamBody) (bindRole : HEq bind AG.lamBind)
    (rooted : es.head?=some (.inr (.inl root)))
    (finish : es.getLast?=some (g.wire (.inl ⟨node,bind⟩))) :
    ∃ (pre loop : List (Endpoint g)) (middle : Context) (binding : ExpandedBindingLoop g loop middle output),
      es=pre++loop ∧ binding.binder=node ∧
      pre.getLast?=some (g.wire (.inl ⟨node,ctx⟩)) ∧ ExpandedLabelling g pre input middle := by
  induction count using Nat.strongRecOn generalizing es input output with
  | ind count ih =>
    by_cases zero : count=0
    · subst count
      have labels := path.zero_ordinary g
      have forward := labels.root_forward_of_flow flow root rooted rootPolarity
      obtain ⟨pre,loop,middle,binding,split,binderEq,prefixEnd,prefixLabels⟩ :=
        transparency es input output node ctx body bind sort ctxRole bodyRole bindRole rooted finish forward labels
      exact ⟨pre,loop,middle,binding.expanded,split,binderEq,prefixEnd,prefixLabels.expanded⟩
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
      obtain ⟨argumentInput,argumentPrefix⟩ := balance.relabel_app_prefix rootDepth edge appLabels appForward appRoot appEnd shell
      have argument := rest.splice_ordinary g argumentPrefix appEnd tailHead (by
        simpa only [Pairing.involutive] using edge.app_arg_turn seam)
      obtain ⟨suffix,tailSplit⟩ := List.head?_eq_some_iff.mp tailHead
      have tailNonempty : tail≠[] := by rw [tailSplit]; simp
      have argumentRoot : (preApp++tail).head?=some (.inr (.inl root)) := by
        cases preApp with
        | nil => cases appRoot
        | cons x xs => exact appRoot
      have argumentFinish : (preApp++tail).getLast?=some (g.wire (.inl ⟨node,bind⟩)) := by
        rw [last_suffix _ _ tailNonempty]
        rw [decomp,last_suffix _ _ tailNonempty] at finish
        exact finish
      obtain ⟨candidate,candidateLoop,candidateMiddle,candidateBinding,argumentSplit,candidateBinder,candidateEnd,candidateLabels⟩ :=
        ih remaining (by omega) argument argumentRoot argumentFinish
      have bodySplit : pre=preApp++edge.principal++loop := by rw [prefixSplit,principalSplit]
      have fullSplit : es=preApp++edge.principal++loop++edge.reverseRoute++[edge.argEnd]++suffix := by
        rw [decomp,bodySplit,tailSplit]
        simp only [List.append_assoc,List.singleton_append]
      have fullForward := (path.coherent_indexed flow rootPolarity balance rootDepth transparency rooted).erase g
      have result := edge.transparency_splice_indexed balance rootDepth preApp loop suffix input argumentInput middle seam output
        appLabels argumentPrefix appForward appEnd shell
        (by rw [←bodySplit]; exact preLabels) loopEnd node ctx body bind sort ctxRole bodyRole bindRole
        (by rw [←fullSplit]; exact path.labelling g)
        (by rw [←fullSplit]; exact fullForward.forward)
        (by rw [←fullSplit]; exact finish)
        candidate candidateLoop candidateMiddle candidateBinding candidateBinder
        (by simpa only [tailSplit] using argumentSplit) candidateLabels candidateEnd
      rw [←fullSplit] at result
      exact result
end
end Lamping.AG

