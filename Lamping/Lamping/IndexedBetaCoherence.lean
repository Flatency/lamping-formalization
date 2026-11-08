import Lamping.Lamping.RootPathInputs
import Lamping.Lamping.BetaDetourCoherence
namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}
private theorem indexed_head_prefix {T : Type} {pre tail : List T} {e : T}
    (nonempty : pre≠[]) (head : (pre++tail).head?=some e) : pre.head?=some e := by
  cases pre with
  | nil => exact False.elim (nonempty rfl)
  | cons x xs => exact head

/-- The actual paired-stream derivation only needs structural indexed tail
synchronization at the real root-to-app prefix. No full Independence or root
input existence is assumed. The first-block count induction and ordinary
Transparency still construct the coherent insertion witness. -/theorem BetaDetourBlocks.coherent_indexed {boundary : B → Bool} (flow : FlowBalance g boundary)
    (rootPolarity : boundary root=true) {heights : B → Int}
    (balance : IndexedLevelBalance g heights) (rootDepth : heights root=0)
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
        indexed_head_prefix preLabels.nonempty (by simpa only [List.append_assoc,decomp] using rooted)
      have preForward := preLabels.root_forward_of_flow flow root preRoot rootPolarity
      obtain ⟨stem,loop,middle,binding,prefixSplit,sameBinder,stemEnd,stemLabels⟩ :=
        transparency pre input seam edge.lam edge.lamCtx edge.lamBody edge.lamBind
          (congrArg Label.sort edge.lamLabel) edge.lamCtx_role edge.lamBody_role edge.lamBind_role
          preRoot preEnd preForward preLabels
      have stemNonempty : stem≠[] := by intro empty; rw [empty] at stemEnd; cases stemEnd
      have stemRoot : stem.head?=some (.inr (.inl root)) :=
        indexed_head_prefix stemNonempty (by rw [←prefixSplit]; exact preRoot)
      have stemForward := stemLabels.root_forward_of_flow flow root stemRoot rootPolarity
      obtain ⟨preApp,principalSplit,appEnd,appRoot,appForward,appLabels⟩ :=
        edge.principal_prefix_reflection stemForward stemRoot stemLabels stemEnd
      obtain ⟨loopStart,loopEnd,shell⟩ := binding.beta_ports edge sameBinder
      obtain ⟨newInput,newPrefix⟩ := balance.relabel_app_prefix rootDepth edge appLabels appForward appRoot appEnd shell
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

