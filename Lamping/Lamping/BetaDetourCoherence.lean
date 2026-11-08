import Lamping.Lamping.BetaDetourBlocks
import Lamping.Lamping.CoherentExpandedPaths
import Lamping.Lamping.PrincipalPrefixReflection
import Lamping.Lamping.ExpandedLabelSurgery
namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}

/-- Only an already labelled ordinary rooted context-prefix is relabelled.
The terminal shell is the actual same-assignment shell, and the new input is
constructed by ordinary Independence.sync. No arbitrary partial path is used. -/
theorem Independence.relabel_app_prefix (independence : Independence g root) (edge : BetaEdge g)
    {pre : List (Endpoint g)} {input seam target : Context}
    (labels : Labelling g pre input seam) (forward : Forward g pre)
    (rooted : pre.head?=some (.inr (.inl root)))
    (finish : pre.getLast?=some (g.wire (.inl ⟨edge.app,edge.appCtx⟩)))
    (shell : Context.SameShell edge.index seam target) :
    ∃ newInput, Labelling g pre newInput target := by
  obtain ⟨_,width,_,_,_,sync⟩ := independence pre (.inr (.inl root)) (.inl ⟨edge.app,edge.appCtx⟩)
    .root .appCtx 0 edge.index input seam rooted finish (.root) trivial
    (.appCtx edge.app edge.appCtx edge.index edge.appLabel edge.appCtx_role) trivial forward labels
  refine ⟨input.replace width (target.tail edge.index),?_⟩
  have changed := sync (target.tail edge.index)
  change Labelling g pre (input.replace width (target.tail edge.index))
    (seam.replace edge.index (target.tail edge.index)) at changed
  rw [Context.replace_of_sameShell seam target edge.index shell] at changed
  exact changed

private theorem same_lambda_port (left right : N) (same : left=right)
    (p : Port (g.label left).sort) (q : Port (g.label right).sort)
    (canonical : Port (.op .lam)) (hp : HEq p canonical) (hq : HEq q canonical) :
    (.inl ⟨left,p⟩ : Endpoint g) = .inl ⟨right,q⟩ := by
  subst right
  have equal : p=q := eq_of_heq (hp.trans hq.symm)
  subst q
  rfl

/-- A transparency-selected binding loop retains the very same physical body
and binding ports as the selected beta edge. The binder equality comes from
that given root-path decomposition, rather than an independent loop witness. -/
theorem BindingLoop.beta_ports {loop : List (Endpoint g)} {seam output : Context}
    (binding : BindingLoop g loop seam output) (edge : BetaEdge g) (same : binding.binder=edge.lam) :
    loop.head?=some (.inl ⟨edge.lam,edge.lamBody⟩) ∧
    loop.getLast?=some (g.wire (.inl ⟨edge.lam,edge.lamBind⟩)) ∧
    Context.SameShell edge.index seam output := by
  have body := same_lambda_port binding.binder edge.lam same binding.body edge.lamBody
    AG.lamBody binding.body_role edge.lamBody_role
  have bind := same_lambda_port binding.binder edge.lam same binding.bind edge.lamBind
    AG.lamBind binding.bind_role edge.lamBind_role
  have index : (g.label binding.binder).index=edge.index := by rw [same,edge.lamLabel]; rfl
  refine ⟨?_,?_,?_⟩
  · exact binding.start.trans (congrArg some body)
  · exact binding.finish.trans (congrArg (fun e => some (g.wire e)) bind)
  · rw [←index]
    exact binding.shell

private theorem head_of_nonempty_append {T : Type} {pre tail : List T} {e : T}
    (nonempty : pre≠[]) (head : (pre++tail).head?=some e) : pre.head?=some e := by
  cases pre with
  | nil => exact False.elim (nonempty rfl)
  | cons x xs => exact head

/-- Every actual paired-block root stream has a coherent generated derivation
in an ordinary invariant graph. The strong induction removes the FIRST
backward block: its preceding root prefix is still genuinely ordinary, so
Transparency supplies its shell in the original assignment. -/
theorem BetaDetourBlocks.coherent {boundary : B → Bool} (flow : FlowBalance g boundary)
    (rootPolarity : boundary root=true) (independence : Independence g root)
    (transparency : Transparency g root) {es : List (Endpoint g)} {input output : Context} {count : Nat}
    (path : BetaDetourBlocks g es input output count) (rooted : es.head?=some (.inr (.inl root))) :
    CoherentExpandedCore g root es input output := by
  induction count using Nat.strongRecOn generalizing es input output with
  | ind count ih =>
    by_cases zero : count=0
    · subst count
      have labels := path.zero_ordinary g
      exact .base labels (labels.root_forward_of_flow flow root rooted rootPolarity) rooted
    · obtain ⟨edge,pre,tail,seam,remaining,countEq,decomp,preLabels,preEnd,tailHead,rest⟩ :=
        path.first_backward g (by omega)
      have preRoot : pre.head?=some (.inr (.inl root)) :=
        head_of_nonempty_append preLabels.nonempty (by simpa only [List.append_assoc,decomp] using rooted)
      have preForward := preLabels.root_forward_of_flow flow root preRoot rootPolarity
      obtain ⟨stem,loop,middle,binding,prefixSplit,sameBinder,stemEnd,stemLabels⟩ :=
        transparency pre input seam edge.lam edge.lamCtx edge.lamBody edge.lamBind
          (congrArg Label.sort edge.lamLabel) edge.lamCtx_role edge.lamBody_role edge.lamBind_role
          preRoot preEnd preForward preLabels
      have stemNonempty : stem≠[] := by intro empty; rw [empty] at stemEnd; cases stemEnd
      have stemRoot : stem.head?=some (.inr (.inl root)) :=
        head_of_nonempty_append stemNonempty (by rw [←prefixSplit]; exact preRoot)
      have stemForward := stemLabels.root_forward_of_flow flow root stemRoot rootPolarity
      obtain ⟨preApp,principalSplit,appEnd,appRoot,appForward,appLabels⟩ :=
        edge.principal_prefix_reflection stemForward stemRoot stemLabels stemEnd
      obtain ⟨loopStart,loopEnd,shell⟩ := binding.beta_ports edge sameBinder
      obtain ⟨newInput,newPrefix⟩ := independence.relabel_app_prefix edge appLabels appForward appRoot appEnd shell
      have newArgument := rest.splice_ordinary g newPrefix appEnd tailHead (by
        simpa only [Pairing.involutive] using edge.app_arg_turn seam)
      obtain ⟨suffix,tailSplit⟩ := List.head?_eq_some_iff.mp tailHead
      rw [tailSplit] at newArgument
      have argumentRoot : (preApp++edge.argEnd::suffix).head?=some (.inr (.inl root)) := by
        cases preApp with
        | nil => cases appRoot
        | cons x xs => exact appRoot
      have argument := ih remaining (by omega) newArgument argumentRoot
      have bodySplit : pre=preApp++edge.principal++loop := by rw [prefixSplit,principalSplit]
      have body : CoherentExpandedCore g root (preApp++edge.principal++loop) input seam := by
        rw [←bodySplit]
        exact .base preLabels preForward preRoot
      have inserted : CoherentExpandedCore g root
          (preApp++edge.principal++loop++edge.reverseRoute++[edge.argEnd]++suffix) input output :=
        .insert edge preApp loop suffix argument body appLabels.expanded newPrefix.expanded
          appEnd loopStart loopEnd binding sameBinder
      have fullSplit : es=preApp++edge.principal++loop++edge.reverseRoute++[edge.argEnd]++suffix := by
        rw [decomp,bodySplit,tailSplit]
        simp only [List.append_assoc,List.singleton_append]
      rw [fullSplit]
      exact inserted
end
end Lamping.AG
