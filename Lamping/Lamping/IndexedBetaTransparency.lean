import Lamping.Lamping.IndexedPairedTransparency
import Lamping.Lamping.BetaBindingLoopContraction
namespace Lamping.AG
open Graph
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))

/-- Actual beta preserves ordinary Transparency. The original reduced
assignment lifts to a finite paired stream; its same-assignment expanded
binder decomposition is proved by count induction, then contracted at that
specific retained binder occurrence. No expanded transparency or generated
loop certificate is supplied by the caller. Full Independence is not needed:
actual source indexed balance supplies all tail resets and shell reflections. -/
theorem PathSite.beta_transparency_indexed {boundary : B → Bool}
    (flow : FlowBalance site.net boundary) (root : B) (positive : boundary root=true)
    {heights : B → Int} (balance : IndexedLevelBalance site.net heights)
    (rootDepth : heights root=0) (oldT : Transparency site.net root) :
    Transparency site.reduce root := by
  intro es a b node ctx body bind isLam ctxRole bodyRole bindRole rooted finish forward labels
  cases node with
  | inr node => exact nomatch node
  | inl node =>
    let c := cutFragment site.net (pathPartition (.beta i) V) site.closed
    let r := (Schema.beta i).right.net
    let last : Endpoint c := c.wire (.inl ⟨node,bind⟩)
    have newFinish : es.getLast?=some (AG.plugLeft c r last) := by
      rw [finish]
      exact congrArg some (plugLeft_wire c r (.inl ⟨node,bind⟩))
    obtain ⟨edge,old,geometry,relation,_oldLabels,oldRoot,oldLast⟩ :=
      site.beta_root_ancestor flow root positive labels rooted last newFinish
    have oldFinish : old.getLast?=some (site.net.wire (.inl ⟨.inl node,bind⟩)) := by
      rw [←site.outsideEnd_wire] at oldLast
      exact oldLast
    obtain ⟨count,stream⟩ := relation.detour_blocks site geometry (labels.plug_decomposition c r)
    obtain ⟨pre,loop,middle,binding,split,binderEq,preEnd,preLabels⟩ := stream.transparency_indexed
      flow positive balance rootDepth oldT (.inl node) ctx body bind isLam ctxRole bodyRole bindRole oldRoot oldFinish
    obtain ⟨newPre,newLoop,newSplit,newPreLabels,newPreEnd,newBinding,newBinder⟩ :=
      relation.contract_binding_prefix_actual site geometry labels root rooted forward
        pre loop split binding node binderEq ctx ctxRole preEnd preLabels
    exact ⟨newPre,newLoop,middle,newBinding,newSplit,newBinder,newPreEnd,newPreLabels⟩
end
end Lamping.AG

