import Lamping.Lamping.SourceActionKeptAccess

namespace Lamping.AG
open Graph Lambda
section
variable {s : Schema} {K B W V : Type}
variable [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed

/-- Keep the supplied whole assignment and actual retained-node finish,
rather than erasing them from the constructed access. -/
theorem PathSite.action_kept_assigned_access (action : IsAction s)
    {root : B} {term : Term} {directions : B → Bool}
    (matching : Matches site.net root term) (inputs : RootInputs site.net root)
    (flow : FlowBalance site.net directions) (positive : directions root=true)
    (source : RootAccess site.net root) (node : K) (port : Port (kept node).sort)
    (sourceFinish : source.val.getLast?=some
      (site.net.wire (Sum.inl ⟨Sum.inl node,port⟩)))
    {a b : Context} (sourceLabels : Labelling site.net source.val a b) :
    ∃ copied : RootAccess site.reduce root,
      accessWord site.reduce copied.val=accessWord site.net source.val ∧
      copied.val.getLast?=some (site.reduce.wire (Sum.inl ⟨Sum.inl node,port⟩)) ∧
      Labelling site.reduce copied.val a b := by
  let last : Endpoint cut := (cut).wire (Sum.inl ⟨node,port⟩)
  have oldLast : source.val.getLast?=some (site.outsideEnd last) :=
    sourceFinish.trans (congrArg some (site.outsideEnd_wire (Sum.inl ⟨node,port⟩)))
  obtain ⟨actual,labels,rooted,finish,word⟩ := site.action_source_outside_word
    action matching inputs flow positive sourceLabels source.property.2.1 last oldLast
  have keptFinish : actual.getLast?=some
      (site.reduce.wire (Sum.inl ⟨Sum.inl node,port⟩)) :=
    finish.trans (congrArg some (plugLeft_wire cut s.right.net (Sum.inl ⟨node,port⟩)).symm)
  have kind : accessKind site.reduce actual=accessKind site.net source.val := by
    simp only [accessKind,keptFinish,sourceFinish,Option.bind_some,Pairing.involutive]
    rfl
  obtain ⟨newFlow⟩ := site.reduce_flowBalance flow
  have forward := labels.root_forward_of_flow newFlow root rooted positive
  have typed : ∃ k,accessKind site.reduce actual=some k := by
    rw [kind]
    exact source.property.2.2
  exact ⟨⟨actual,⟨⟨⟨a,b,labels⟩,forward⟩,rooted,typed⟩⟩,word,keptFinish,labels⟩
end
end Lamping.AG
