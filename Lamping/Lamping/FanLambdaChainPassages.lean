import Lamping.Lamping.ActionPendingLambdaBranches
import Lamping.Lambda.PrerequisitePrefixes
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {current : LTerm} {g : Net signature N B W} {root : B}

/-- Actual chain membership puts THIS occurrence-indexed block in its
canonical image, without treating an arbitrary auxiliary edge as a read. -/
theorem canonical_chain_member (selection : OccurrenceFragmentSelection current g root)
    (chain : PrerequisiteChain current start edges) (position : Position current.erase)
    (member : position.val∈edges) :
    (selection position).fragment.segments∈canonicalChainImage selection chain := by
  apply List.mem_map.mpr
  refine ⟨⟨position.val,member⟩,List.mem_attach _ _,?_⟩
  rfl
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.fanAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))

/-- A real successful-chain slot terminating at an actual copied lambda
contains the SAME supplied principal suffix and the real incoming fan branch.
All assignments below come from the one supplied source whole labelling.
This does not assert synchronization of two chains or any Joint truth. -/
theorem PathSite.fan_lambda_chain_writer_passage
    {current : LTerm} {root : B} {boundary : B→Bool}
    (matching : Matches site.net root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (principal : SiteActionPrincipal site)
    (selection : OccurrenceFragmentSelection current site.net root)
    (chain : PrerequisiteChain current start edges) (position : Position current.erase)
    (member : position.val∈edges)
    (target : RootAccess site.reduce root)
    (word : accessWord site.reduce target.val=position.val) (branch : Bool)
    (finish : target.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),.inl ()⟩)))
    {a b : Context} (whole : Labelling site.net (selection position).fragment.access.val a b) :
    ∃ before after middle pre input seam,
      edges=before++(position.val::after) ∧
      PrerequisitePrefix current start before middle ∧
      PrerequisiteChain current middle (position.val::after) ∧
      PrerequisiteReads current middle position.val ∧
      (selection position).fragment.segments∈canonicalChainImage selection chain ∧
      (selection position).fragment.segments=pre++principal.edges ∧
      pre.head?=some (selection position).fragment.fromEndpoint ∧
      pre.getLast?=some (site.net.wire (.inl ⟨.inr (.inl ()),.inr branch⟩)) ∧
      Labelling site.net (selection position).fragment.segments input b ∧
      Labelling site.net pre input seam ∧
      Traversal i (.op .fan) (.inr branch) (.inl ()) seam b ∧
      ((selection position).fragment.before=[] ∧input=a ∨
        Labelling site.net (selection position).fragment.before a input) ∧
      reverseEdges (selection position).fragment.segments=reverseEdges principal.edges++reverseEdges pre ∧
      Labelling site.net (reverseEdges (selection position).fragment.segments) b input ∧
      Traversal i (.op .fan) (.inl ()) (.inr branch) b seam := by
  obtain ⟨before,after,middle,split,segment,remainder,reads⟩ := chain.split_at_member member
  obtain ⟨actualPre,actualSplit,actualLast⟩ := (selection position).fragment.target_lambda_writer
    site matching flow positive principal target word.symm branch finish
  have terminal : (selection position).fragment.toEndpoint=.inl ⟨.inr (.inr ()),.inl ()⟩ := by
    have sameLast : (selection position).fragment.segments.getLast?=
        some (site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)) := by
      rw [actualSplit,List.getLast?_append,principal.last,Option.some_or]
    have same := Option.some.inj ((selection position).fragment.finish.symm.trans sameLast)
    have restored := congrArg site.net.wire.mate same
    simpa only [Pairing.involutive] using restored
  obtain ⟨pre,q,input,seam,pieceSplit,head,last,pieceLabels,prefixLabels,writer⟩ :=
    (selection position).fragment.lambda_writer_suffix site (Or.inl rfl) rfl principal whole terminal
  have branchEq := site.writer_suffix_aux_unique principal
    (pieceSplit.symm.trans actualSplit) last actualLast
  subst q
  obtain ⟨actualInput,beforeLabels,sourcePieceLabels⟩ := (selection position).fragment.assignments a b whole
  have inputEq : actualInput=input := sourcePieceLabels.reverse.output_unique pieceLabels.reverse
  rw [inputEq] at beforeLabels
  have reversed : reverseEdges (selection position).fragment.segments=
      reverseEdges principal.edges++reverseEdges pre := by
    rw [pieceSplit]
    simp only [reverseEdges,List.reverse_append,List.map_append]
  exact ⟨before,after,middle,pre,input,seam,split,segment,remainder,reads,
    canonical_chain_member selection chain position member,pieceSplit,head,last,pieceLabels,prefixLabels,
    writer,beforeLabels,reversed,pieceLabels.reverse,writer.reverse⟩
end
end Lamping.AG
#print axioms Lamping.AG.canonical_chain_member
#print axioms Lamping.AG.PathSite.fan_lambda_chain_writer_passage