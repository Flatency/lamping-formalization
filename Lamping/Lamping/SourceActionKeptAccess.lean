import Lamping.Lamping.RootSourcePrefixExpansion
import Lamping.Lamping.ActionWholeWords
namespace Lamping.AG
open Graph Lambda
section
variable {s : Schema} {K B W V : Type}
variable [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed

theorem PathSite.action_source_outside_word (action : IsAction s)
    {root : B} {t : Term} {boundary : B → Bool}
    (matching : Matches site.net root t) (inputs : RootInputs site.net root)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {old : List (Endpoint site.net)} {a b : Context}
    (labels : Labelling site.net old a b) (rooted : old.head?=some (.inr (.inl root)))
    (last : Endpoint cut) (finish : old.getLast?=some (site.outsideEnd last)) :
    ∃ es : List (Endpoint site.reduce),Labelling site.reduce es a b ∧
      es.head?=some (.inr (.inl root)) ∧es.getLast?=some (AG.plugLeft cut s.right.net last) ∧
      accessWord site.reduce es=accessWord site.net old := by
  obtain ⟨principal,es,targetLabels,residual,head,lastEq⟩ :=
    site.action_labelled_source_outside_expansion action matching inputs flow positive labels rooted last finish
  have shape := targetLabels.local_excursions cut s.right.net (.inr (.inl (.inl root))) last head lastEq
  have word := residual.word site shape
  rw [plug_decomposition_flatten] at word
  exact ⟨es,targetLabels,head,lastEq,word⟩

/-- Retained proper source accesses have constructed actual target accesses
with the same word and observation kind. No desired target access is given. -/
theorem PathSite.action_kept_access_forward (action : IsAction s)
    {root : B} {t : Term} {boundary : B → Bool}
    (matching : Matches site.net root t) (inputs : RootInputs site.net root)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (source : RootAccess site.net root) (node : K) (p : Port (kept node).sort)
    (finish : source.val.getLast?=some (site.net.wire (.inl ⟨.inl node,p⟩))) :
    ∃ target : RootAccess site.reduce root,
      accessWord site.reduce target.val=accessWord site.net source.val ∧
      accessKind site.reduce target.val=accessKind site.net source.val := by
  let last : Endpoint cut := (cut).wire (.inl ⟨node,p⟩)
  have represented : site.outsideEnd last=site.net.wire (.inl ⟨.inl node,p⟩) :=
    (site.outsideEnd_wire (.inl ⟨node,p⟩)).symm
  have oldLast : source.val.getLast?=some (site.outsideEnd last) := finish.trans (congrArg some represented.symm)
  obtain ⟨a,b,labels⟩ := source.property.1.1
  obtain ⟨es,targetLabels,targetHead,targetLast,word⟩ := site.action_source_outside_word action matching inputs flow positive
    labels source.property.2.1 last oldLast
  have physicalLast : es.getLast?=some (site.reduce.wire (.inl ⟨.inl node,p⟩)) :=
    targetLast.trans (congrArg some (plugLeft_wire cut s.right.net (.inl ⟨node,p⟩)).symm)
  have kind : accessKind site.reduce es=accessKind site.net source.val := by
    simp only [accessKind,physicalLast,finish,Option.bind_some,Pairing.involutive]
    rfl
  obtain ⟨newFlow⟩ := site.reduce_flowBalance flow
  have forward := targetLabels.root_forward_of_flow newFlow root targetHead positive
  have typed : ∃ k,accessKind site.reduce es=some k := by rw [kind]; exact source.property.2.2
  exact ⟨⟨es,⟨⟨⟨_,_,targetLabels⟩,forward⟩,targetHead,typed⟩⟩,word,kind⟩
end
end Lamping.AG
