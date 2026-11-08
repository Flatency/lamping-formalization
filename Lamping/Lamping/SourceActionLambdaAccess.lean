import Lamping.Lamping.SourceActionAuxAccess
namespace Lamping.AG
open Graph Lambda
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable {root : B} {t : Term} {boundary : B → Bool}

theorem PathSite.fan_source_lam_access
    (site : PathSite (.fanAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
    (matching : Matches site.net root t) (inputs : RootInputs site.net root)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (source : RootAccess site.net root)
    (finish : source.val.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩))) :
    ∃ target : RootAccess site.reduce root,
      accessWord site.reduce target.val=accessWord site.net source.val ∧
      accessKind site.reduce target.val=accessKind site.net source.val := by
  obtain ⟨a,b,labels⟩ := source.property.1.1
  obtain ⟨principal⟩ := site.actionPrincipal_exists
  obtain ⟨pre,q,middle,split,preRoot,preLast,preLabels,writer⟩ :=
    site.rooted_control_writer_suffix principal labels root source.property.2.1 finish
  
  let c := cutFragment site.net (pathPartition (.fanAction .lam i j lt) V) site.closed
  let r := fanRight .lam i j
  let inside : List (Endpoint r) := [.inr (.inl (.inl q))]
  obtain ⟨es,targetLabels,targetHead,targetLast,word⟩ := site.source_pending_expansion (.fan .lam i j lt)
    matching inputs flow positive preLabels preRoot (.inl q) preLast inside (.single _ middle) rfl
  have kind : accessKind site.reduce es=accessKind site.net source.val := by
    simp only [accessKind,targetLast,finish]
    change (some (AG.plugRight c r (r.wire (.inl ⟨.inl q,.inl ()⟩)))).bind _ = _
    rw [←plugRight_wire]
    simp only [Option.bind_some,Pairing.involutive]
    rfl
  obtain ⟨newFlow⟩ := site.reduce_flowBalance flow
  have forward := targetLabels.root_forward_of_flow newFlow root targetHead positive
  have typed : ∃ k,accessKind site.reduce es=some k := by rw [kind]; exact source.property.2.2
  refine ⟨⟨es,⟨⟨⟨_,_,targetLabels⟩,forward⟩,targetHead,typed⟩⟩,?_,kind⟩
  have noTokens : accessTokens (Schema.fanAction .lam i j lt).right.net inside=[] := rfl
  rw [noTokens,List.append_nil] at word
  have routeTokens := principal.tokens_empty site (.fan .lam i j lt)
  change principal.edges.flatMap (arrivalWord site.net)=[] at routeTokens
  have sourceWord : accessWord site.net source.val=accessWord site.net pre := by
    rw [split,accessWord_append site.net pre principal.edges preLabels.nonempty,routeTokens,List.append_nil]
  exact word.trans sourceWord.symm

theorem PathSite.cro_source_lam_access
    (site : PathSite (.croAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
    (matching : Matches site.net root t) (inputs : RootInputs site.net root)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (source : RootAccess site.net root)
    (finish : source.val.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩))) :
    ∃ target : RootAccess site.reduce root,
      accessWord site.reduce target.val=accessWord site.net source.val ∧
      accessKind site.reduce target.val=accessKind site.net source.val := by
  obtain ⟨a,b,labels⟩ := source.property.1.1
  obtain ⟨principal⟩ := site.actionPrincipal_exists
  obtain ⟨pre,q,middle,split,preRoot,preLast,preLabels,writer⟩ :=
    site.rooted_control_writer_suffix principal labels root source.property.2.1 finish
  cases q
  let c := cutFragment site.net (pathPartition (.croAction .lam i j lt) V) site.closed
  let r := unaryRightCore .cro .lam (Bij.refl _) i (j-1)
  let inside : List (Endpoint r) := [.inr (.inl (.inl ()))]
  obtain ⟨es,targetLabels,targetHead,targetLast,word⟩ := site.source_pending_expansion (.cro .lam i j lt)
    matching inputs flow positive preLabels preRoot (.inl ()) preLast inside (.single _ middle) rfl
  have kind : accessKind site.reduce es=accessKind site.net source.val := by
    simp only [accessKind,targetLast,finish]
    change (some (AG.plugRight c r (r.wire (.inl ⟨.inl (),.inl ()⟩)))).bind _ = _
    rw [←plugRight_wire]
    simp only [Option.bind_some,Pairing.involutive]
    rfl
  obtain ⟨newFlow⟩ := site.reduce_flowBalance flow
  have forward := targetLabels.root_forward_of_flow newFlow root targetHead positive
  have typed : ∃ k,accessKind site.reduce es=some k := by rw [kind]; exact source.property.2.2
  refine ⟨⟨es,⟨⟨⟨_,_,targetLabels⟩,forward⟩,targetHead,typed⟩⟩,?_,kind⟩
  have noTokens : accessTokens (Schema.croAction .lam i j lt).right.net inside=[] := rfl
  rw [noTokens,List.append_nil] at word
  have routeTokens := principal.tokens_empty site (.cro .lam i j lt)
  change principal.edges.flatMap (arrivalWord site.net)=[] at routeTokens
  have sourceWord : accessWord site.net source.val=accessWord site.net pre := by
    rw [split,accessWord_append site.net pre principal.edges preLabels.nonempty,routeTokens,List.append_nil]
  exact word.trans sourceWord.symm

theorem PathSite.bra_source_lam_access
    (site : PathSite (.braAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
    (matching : Matches site.net root t) (inputs : RootInputs site.net root)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (source : RootAccess site.net root)
    (finish : source.val.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩))) :
    ∃ target : RootAccess site.reduce root,
      accessWord site.reduce target.val=accessWord site.net source.val ∧
      accessKind site.reduce target.val=accessKind site.net source.val := by
  obtain ⟨a,b,labels⟩ := source.property.1.1
  obtain ⟨principal⟩ := site.actionPrincipal_exists
  obtain ⟨pre,q,middle,split,preRoot,preLast,preLabels,writer⟩ :=
    site.rooted_control_writer_suffix principal labels root source.property.2.1 finish
  cases q
  let c := cutFragment site.net (pathPartition (.braAction .lam i j lt) V) site.closed
  let r := unaryRightCore .bra .lam (Bij.refl _) i (j+1)
  let inside : List (Endpoint r) := [.inr (.inl (.inl ()))]
  obtain ⟨es,targetLabels,targetHead,targetLast,word⟩ := site.source_pending_expansion (.bra .lam i j lt)
    matching inputs flow positive preLabels preRoot (.inl ()) preLast inside (.single _ middle) rfl
  have kind : accessKind site.reduce es=accessKind site.net source.val := by
    simp only [accessKind,targetLast,finish]
    change (some (AG.plugRight c r (r.wire (.inl ⟨.inl (),.inl ()⟩)))).bind _ = _
    rw [←plugRight_wire]
    simp only [Option.bind_some,Pairing.involutive]
    rfl
  obtain ⟨newFlow⟩ := site.reduce_flowBalance flow
  have forward := targetLabels.root_forward_of_flow newFlow root targetHead positive
  have typed : ∃ k,accessKind site.reduce es=some k := by rw [kind]; exact source.property.2.2
  refine ⟨⟨es,⟨⟨⟨_,_,targetLabels⟩,forward⟩,targetHead,typed⟩⟩,?_,kind⟩
  have noTokens : accessTokens (Schema.braAction .lam i j lt).right.net inside=[] := rfl
  rw [noTokens,List.append_nil] at word
  have routeTokens := principal.tokens_empty site (.bra .lam i j lt)
  change principal.edges.flatMap (arrivalWord site.net)=[] at routeTokens
  have sourceWord : accessWord site.net source.val=accessWord site.net pre := by
    rw [split,accessWord_append site.net pre principal.edges preLabels.nonempty,routeTokens,List.append_nil]
  exact word.trans sourceWord.symm
end
end Lamping.AG
