import Lamping.Lamping.FixedBetaDetourBlocks
import Lamping.Lamping.RootPathInputs
import Lamping.Lamping.CoherentExpandedPaths
import Lamping.Lamping.BetaDetourCoherence
namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}

/-- A finite expansion at ONE physical beta. Each newly selected body is
ordinary; only the argument spine recurses. Assignments are the actual given
ones, and the index counts these fixed-edge insertions. -/
inductive FixedCoherentCore (root : B) (edge : BetaEdge g) :
    List (Endpoint g) → Context → Context → Nat → Prop where
  | base {es input output}
      (labels : Labelling g es input output) (forward : Forward g es)
      (rooted : es.head?=some (.inr (.inl root))) : FixedCoherentCore root edge es input output 0
  | insert (pre loop suffix : List (Endpoint g))
      {input argumentInput seam endBody output : Context} {count : Nat}
      (argument : FixedCoherentCore root edge (pre++edge.argEnd::suffix) argumentInput output count)
      (body : Labelling g (pre++edge.principal++loop) input endBody)
      (bodyForward : Forward g (pre++edge.principal++loop))
      (bodyRoot : (pre++edge.principal++loop).head?=some (.inr (.inl root)))
      (bodyPrefix : ExpandedLabelling g pre input seam)
      (argumentPrefix : ExpandedLabelling g pre argumentInput endBody)
      (preEnd : pre.getLast?=some (g.wire (.inl ⟨edge.app,edge.appCtx⟩)))
      (loopStart : loop.head?=some (.inl ⟨edge.lam,edge.lamBody⟩))
      (loopEnd : loop.getLast?=some (g.wire (.inl ⟨edge.lam,edge.lamBind⟩)))
      (binding : BindingLoop g loop seam endBody) (sameBinder : binding.binder=edge.lam) :
      FixedCoherentCore root edge
        (pre++edge.principal++loop++edge.reverseRoute++[edge.argEnd]++suffix) input output (count+1)

theorem FixedCoherentCore.erase {edge : BetaEdge g} {es a b count}
    (core : FixedCoherentCore root edge es a b count) : CoherentExpandedCore g root es a b := by
  induction core with
  | base labels forward rooted => exact .base labels forward rooted
  | insert pre loop suffix argument body bodyForward bodyRoot bodyPrefix argumentPrefix
      preEnd loopStart loopEnd binding sameBinder ih =>
    exact .insert _ pre loop suffix ih (.base body bodyForward bodyRoot) bodyPrefix argumentPrefix
      preEnd loopStart loopEnd binding sameBinder

private theorem head_prefix {T : Type} {pre tail : List T} {e : T}
    (nonempty : pre≠[]) (head : (pre++tail).head?=some e) : pre.head?=some e := by
  cases pre with
  | nil => exact False.elim (nonempty rfl)
  | cons x xs => exact head

/-- A supplied rooted fixed stream has a finite same-edge coherent tree at
the SAME original assignment. No path, input assignment or continuation is
completed. RootInputs, full Independence and Nesting are unnecessary here. -/
theorem FixedBetaDetourBlocks.fixed_coherent
    {edge : BetaEdge g} {boundary : B → Bool} (flow : FlowBalance g boundary)
    (positive : boundary root=true) {heights : B → Int}
    (balance : IndexedLevelBalance g heights) (rootDepth : heights root=0)
    (transparency : Transparency g root)
    {es : List (Endpoint g)} {input output : Context} {count : Nat}
    (path : FixedBetaDetourBlocks edge es input output count)
    (rooted : es.head?=some (.inr (.inl root))) : FixedCoherentCore root edge es input output count := by
  induction count using Nat.strongRecOn generalizing es input output with
  | ind count ih =>
    by_cases zero : count=0
    · subst count
      have labels := path.erase.zero_ordinary g
      exact .base labels (labels.root_forward_of_flow flow root rooted positive) rooted
    · obtain ⟨pre,tail,seam,remaining,countEq,decomp,preLabels,preEnd,tailHead,rest⟩ :=
        path.first_backward (by omega)
      have preRoot : pre.head?=some (.inr (.inl root)) :=
        head_prefix preLabels.nonempty (by simpa only [List.append_assoc,decomp] using rooted)
      have preForward := preLabels.root_forward_of_flow flow root preRoot positive
      obtain ⟨stem,loop,middle,binding,prefixSplit,sameBinder,stemEnd,stemLabels⟩ :=
        transparency pre input seam edge.lam edge.lamCtx edge.lamBody edge.lamBind
          (congrArg Label.sort edge.lamLabel) edge.lamCtx_role edge.lamBody_role edge.lamBind_role
          preRoot preEnd preForward preLabels
      have stemNonempty : stem≠[] := by intro empty; rw [empty] at stemEnd; cases stemEnd
      have stemRoot := head_prefix stemNonempty (by rw [←prefixSplit]; exact preRoot)
      have stemForward := stemLabels.root_forward_of_flow flow root stemRoot positive
      obtain ⟨preApp,principalSplit,appEnd,appRoot,appForward,appLabels⟩ :=
        edge.principal_prefix_reflection stemForward stemRoot stemLabels stemEnd
      obtain ⟨loopStart,loopEnd,shell⟩ := binding.beta_ports edge sameBinder
      obtain ⟨argumentInput,argumentPrefix⟩ := balance.relabel_app_prefix rootDepth
        edge appLabels appForward appRoot appEnd shell
      have argumentStream := rest.splice_ordinary argumentPrefix appEnd tailHead (by
        simpa only [Pairing.involutive] using edge.app_arg_turn seam)
      have argumentRoot : (preApp++tail).head?=some (.inr (.inl root)) := by
        rw [List.head?_append,appRoot]
        rfl
      have smaller := ih remaining (by omega) argumentStream argumentRoot
      obtain ⟨suffix,tailSplit⟩ := List.head?_eq_some_iff.mp tailHead
      have bodySplit : pre=preApp++edge.principal++loop := by rw [prefixSplit,principalSplit]
      have body : Labelling g (preApp++edge.principal++loop) input seam := by rw [←bodySplit]; exact preLabels
      have bodyForward : Forward g (preApp++edge.principal++loop) := by rw [←bodySplit]; exact preForward
      have bodyRoot : (preApp++edge.principal++loop).head?=some (.inr (.inl root)) := by rw [←bodySplit]; exact preRoot
      have argument : FixedCoherentCore root edge (preApp++edge.argEnd::suffix) argumentInput output remaining := by
        simpa only [tailSplit] using smaller
      have inserted := FixedCoherentCore.insert preApp loop suffix argument body bodyForward bodyRoot
        appLabels.expanded argumentPrefix.expanded appEnd loopStart loopEnd binding sameBinder
      rw [decomp,bodySplit,tailSplit,countEq]
      simpa only [List.append_assoc,List.singleton_append] using inserted
end
end Lamping.AG
