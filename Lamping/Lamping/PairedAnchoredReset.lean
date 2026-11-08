import Lamping.Lamping.PairedStreamCuts
import Lamping.Lamping.PairedStreamAppend
namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {boundary : B → Bool} {heights : B → Int} {root : B}

/-- Reset a supplied finite rooted stream while preserving the low shell
at a specified positive cut. Both new pieces retain their actual physical
occurrences and counts. The cut height need not be below the final height. -/
theorem BetaDetourBlocks.relabel_anchored_indexed
    (flow : FlowBalance g boundary) (positive : boundary root=true)
    (balance : IndexedLevelBalance g heights) (rootDepth : heights root=0)
    {es pre post : List (Endpoint g)} {cut : Endpoint g}
    {input output oldCut target : Context} {count m i : Nat}
    (whole : BetaDetourBlocks g es input output count)
    (rooted : es.head?=some (.inr (.inl root)))
    (split : es=pre++cut::post)
    (cutPositive : flowEndpoint g flow.nodes boundary flow.vertices cut=true)
    (cutDepth : endpointDepth g balance.nodes heights balance.vertices cut=(m : Int))
    (lastDepth : ∀ e,es.getLast?=some e →
      endpointDepth g balance.nodes heights balance.vertices e=(i : Int))
    (reference : ExpandedLabelling g (pre++[cut]) input oldCut)
    (shell : Context.SameShell i output target) :
    ∃ newInput newCut leftCount,
      BetaDetourBlocks g es newInput target count ∧
      BetaDetourBlocks g (pre++[cut]) newInput newCut leftCount ∧
      Context.SameShell m oldCut newCut := by
  obtain ⟨actual,leftCount,rightCount,before,after,counts⟩ :=
    whole.split_at_positive flow positive pre cut post split cutPositive
  have actualEq : actual=oldCut := (before.labelling g).output_unique reference
  subst actual
  have leftRoot : (pre++[cut]).head?=some (.inr (.inl root)) := by
    cases pre with
    | nil => simpa only [split,List.nil_append,List.head?_cons] using rooted
    | cons first rest => simpa only [split,List.cons_append,List.head?_cons] using rooted
  have leftLast : (pre++[cut]).getLast?=some cut := by simp
  have rightLast : ∀ e,(cut::post).getLast?=some e →
      endpointDepth g balance.nodes heights balance.vertices e=(i : Int) := by
    intro e last
    apply lastDepth e
    rw [split,List.getLast?_append,last,Option.some_or]
  obtain ⟨rightWidth,lower,_rightTails,rightSync⟩ :=
    after.high_tail_sync_indexed flow positive balance rootDepth m i
      (by intro e first; have equal := Option.some.inj first; subst e; exact cutPositive)
      (by intro e first; have equal := Option.some.inj first; subst e; exact cutDepth)
      rightLast
  let newCut := oldCut.replace rightWidth (target.tail i)
  have rightChanged : BetaDetourBlocks g (cut::post) newCut target rightCount := by
    have changed := rightSync (target.tail i)
    rw [Context.replace_of_sameShell output target i shell] at changed
    exact changed
  have sameShell : Context.SameShell m oldCut newCut := by
    intro k low
    dsimp only [newCut]
    rw [Context.replace_low oldCut (target.tail i) (by omega : k<rightWidth)]
  obtain ⟨leftWidth,_leftLower,_leftTails,leftSync⟩ :=
    before.high_tail_sync_indexed flow positive balance rootDepth 0 m
      (by intro e first; have equal := Option.some.inj (first.symm.trans leftRoot); rw [equal]; exact positive)
      (by intro e first; have equal := Option.some.inj (first.symm.trans leftRoot); rw [equal]; exact rootDepth)
      (by intro e last; have equal := Option.some.inj (last.symm.trans leftLast); rw [equal]; exact cutDepth)
  let newInput := input.replace leftWidth (newCut.tail m)
  have leftChanged : BetaDetourBlocks g (pre++[cut]) newInput newCut leftCount := by
    have changed := leftSync (newCut.tail m)
    rw [Context.replace_of_sameShell oldCut newCut m sameShell] at changed
    exact changed
  have combined := leftChanged.append_at_last rightChanged leftLast
  refine ⟨newInput,newCut,leftCount,?_,leftChanged,sameShell⟩
  simpa only [split,List.append_assoc,List.singleton_append,←counts] using combined
end
end Lamping.AG
