import Lamping.Lamping.ActionWholeWords
namespace Lamping.AG
open Graph Lambda
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))

/-- Every supplied reduced root access ending at a kept node reflects to an
actual old root access with exactly the same word and kind. New passive-copy
endpoints require separate pending-path reflection and are not covered here. -/
theorem PathSite.action_kept_access_backward (action : IsAction s)
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) (target : RootAccess site.reduce root)
    (node : K) (p : Port (kept node).sort)
    (finish : target.val.getLast?=some (site.reduce.wire (.inl ⟨.inl node,p⟩))) :
    ∃ source : RootAccess site.net root,
      accessWord site.net source.val=accessWord site.reduce target.val ∧
      accessKind site.net source.val=accessKind site.reduce target.val := by
  let c := cutFragment site.net (pathPartition s V) site.closed
  let r := s.right.net
  let first : Endpoint c := .inr (.inl (.inl root))
  let last : Endpoint c := c.wire (.inl ⟨node,p⟩)
  have represented : site.reduce.wire (.inl ⟨.inl node,p⟩)=AG.plugLeft c r last :=
    plugLeft_wire c r (.inl ⟨node,p⟩)
  obtain ⟨a,b,labels⟩ := target.property.1.1
  obtain ⟨old,oldLabels,oldHead,oldLast,word⟩ := site.action_canonical_ancestor_word action labels
    first last target.property.2.1 (finish.trans (congrArg some represented))
  have oldRoot : old.head?=some (.inr (.inl root)) := oldHead
  have oldEnd : old.getLast?=some (site.net.wire (.inl ⟨.inl node,p⟩)) := by
    rw [←site.outsideEnd_wire] at oldLast
    exact oldLast
  have kind : accessKind site.net old=accessKind site.reduce target.val := by
    simp only [accessKind,oldEnd,finish,Option.bind_some,Pairing.involutive]
    rfl
  have oldTyped : ∃ k,accessKind site.net old=some k := by
    rw [kind]
    exact target.property.2.2
  have forward := oldLabels.root_forward_of_flow flow root oldRoot positive
  exact ⟨⟨old,⟨⟨⟨a,b,oldLabels⟩,forward⟩,oldRoot,oldTyped⟩⟩,word.symm,kind⟩
end
end Lamping.AG
