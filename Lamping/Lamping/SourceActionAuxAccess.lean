import Lamping.Lamping.SourceActionPendingExpansion
import Lamping.Lamping.SourceControlWriterSuffix
import Lamping.Lamping.ControlConstructorTransport
namespace Lamping.AG
open Graph Lambda
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {f : Op} {i j : Nat} {lt : i<j}
variable {root : B} {t : Term} {boundary : B → Bool}

theorem PathSite.fan_source_aux_access
    (site : PathSite (.fanAction f i j lt) kept (B:=B) (W:=W) (V:=V))
    (matching : Matches site.net root t) (inputs : RootInputs site.net root)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (source : RootAccess site.net root) (q : Aux f)
    (finish : source.val.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inr q⟩)))
    {a b middle : Context} (labels : Labelling site.net source.val a b) (branch : Bool)
    (inverse : Traversal i (.op .fan) (.inl ()) (.inr branch) b middle) :
    ∃ target : RootAccess site.reduce root,
      accessWord site.reduce target.val=accessWord site.net source.val ∧
      accessKind site.reduce target.val=accessKind site.net source.val := by
  let c := cutFragment site.net (pathPartition (.fanAction f i j lt) V) site.closed
  let r := fanRight f i j
  let inside : List (Endpoint r) := [.inr (.inl (.inr q)),.inl ⟨.inr q,.inr branch⟩]
  have localLabels : Labelling r inside b middle := .cons (.node _ _ _ inverse) (.single _ _)
  obtain ⟨es,targetLabels,targetHead,targetLast,word⟩ := site.source_pending_expansion (.fan f i j lt)
    matching inputs flow positive labels source.property.2.1 (.inr q) finish inside localLabels rfl
  have kind : accessKind site.reduce es=accessKind site.net source.val := by
    simp only [accessKind,targetLast,finish]
    change (some (AG.plugRight c r (r.wire (.inl ⟨.inl branch,.inr q⟩)))).bind _ = _
    rw [←plugRight_wire]
    simp only [Option.bind_some,Pairing.involutive]
    rfl
  obtain ⟨newFlow⟩ := site.reduce_flowBalance flow
  have forward := targetLabels.root_forward_of_flow newFlow root targetHead positive
  have typed : ∃ k,accessKind site.reduce es=some k := by rw [kind]; exact source.property.2.2
  refine ⟨⟨es,⟨⟨⟨_,_,targetLabels⟩,forward⟩,targetHead,typed⟩⟩,?_,kind⟩
  have noTokens : accessTokens (Schema.fanAction f i j lt).right.net inside=[] := rfl
  rw [noTokens,List.append_nil] at word
  exact word
theorem PathSite.cro_source_aux_access
    (site : PathSite (.croAction f i j lt) kept (B:=B) (W:=W) (V:=V))
    (matching : Matches site.net root t) (inputs : RootInputs site.net root)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (source : RootAccess site.net root) (q : Aux f)
    (finish : source.val.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inr q⟩)))
    {a b middle : Context} (labels : Labelling site.net source.val a b)
    (inverse : Traversal i (.op .cro) (.inl ()) (.inr ()) b middle) :
    ∃ target : RootAccess site.reduce root,
      accessWord site.reduce target.val=accessWord site.net source.val ∧
      accessKind site.reduce target.val=accessKind site.net source.val := by
  let c := cutFragment site.net (pathPartition (.croAction f i j lt) V) site.closed
  let r := unaryRightCore .cro f (Bij.refl _) i (j-1)
  let inside : List (Endpoint r) := [.inr (.inl (.inr q)),.inl ⟨.inr q,.inr ()⟩]
  have localLabels : Labelling r inside b middle := .cons (.node _ _ _ inverse) (.single _ _)
  obtain ⟨es,targetLabels,targetHead,targetLast,word⟩ := site.source_pending_expansion (.cro f i j lt)
    matching inputs flow positive labels source.property.2.1 (.inr q) finish inside localLabels rfl
  have kind : accessKind site.reduce es=accessKind site.net source.val := by
    simp only [accessKind,targetLast,finish]
    change (some (AG.plugRight c r (r.wire (.inl ⟨.inl (),.inr q⟩)))).bind _ = _
    rw [←plugRight_wire]
    simp only [Option.bind_some,Pairing.involutive]
    rfl
  obtain ⟨newFlow⟩ := site.reduce_flowBalance flow
  have forward := targetLabels.root_forward_of_flow newFlow root targetHead positive
  have typed : ∃ k,accessKind site.reduce es=some k := by rw [kind]; exact source.property.2.2
  refine ⟨⟨es,⟨⟨⟨_,_,targetLabels⟩,forward⟩,targetHead,typed⟩⟩,?_,kind⟩
  have noTokens : accessTokens (Schema.croAction f i j lt).right.net inside=[] := rfl
  rw [noTokens,List.append_nil] at word
  exact word

theorem PathSite.bra_source_aux_access
    (site : PathSite (.braAction f i j lt) kept (B:=B) (W:=W) (V:=V))
    (matching : Matches site.net root t) (inputs : RootInputs site.net root)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (source : RootAccess site.net root) (q : Aux f)
    (finish : source.val.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inr q⟩)))
    {a b middle : Context} (labels : Labelling site.net source.val a b)
    (inverse : Traversal i (.op .bra) (.inl ()) (.inr ()) b middle) :
    ∃ target : RootAccess site.reduce root,
      accessWord site.reduce target.val=accessWord site.net source.val ∧
      accessKind site.reduce target.val=accessKind site.net source.val := by
  let c := cutFragment site.net (pathPartition (.braAction f i j lt) V) site.closed
  let r := unaryRightCore .bra f (Bij.refl _) i (j+1)
  let inside : List (Endpoint r) := [.inr (.inl (.inr q)),.inl ⟨.inr q,.inr ()⟩]
  have localLabels : Labelling r inside b middle := .cons (.node _ _ _ inverse) (.single _ _)
  obtain ⟨es,targetLabels,targetHead,targetLast,word⟩ := site.source_pending_expansion (.bra f i j lt)
    matching inputs flow positive labels source.property.2.1 (.inr q) finish inside localLabels rfl
  have kind : accessKind site.reduce es=accessKind site.net source.val := by
    simp only [accessKind,targetLast,finish]
    change (some (AG.plugRight c r (r.wire (.inl ⟨.inl (),.inr q⟩)))).bind _ = _
    rw [←plugRight_wire]
    simp only [Option.bind_some,Pairing.involutive]
    rfl
  obtain ⟨newFlow⟩ := site.reduce_flowBalance flow
  have forward := targetLabels.root_forward_of_flow newFlow root targetHead positive
  have typed : ∃ k,accessKind site.reduce es=some k := by rw [kind]; exact source.property.2.2
  refine ⟨⟨es,⟨⟨⟨_,_,targetLabels⟩,forward⟩,targetHead,typed⟩⟩,?_,kind⟩
  have noTokens : accessTokens (Schema.braAction f i j lt).right.net inside=[] := rfl
  rw [noTokens,List.append_nil] at word
  exact word

end
end Lamping.AG

