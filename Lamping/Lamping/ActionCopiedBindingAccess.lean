import Lamping.Lamping.ActionCopiedBindingWords
import Lamping.Lamping.ActionPendingAccess
namespace Lamping.AG
open Graph Lambda
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}

/-- The actual two-control binding prefix discharges the local token
condition internally. Both BindingSuffix witnesses retain the same index. -/
theorem PathSite.fan_copied_binding_access
    (site : PathSite (Schema.fanAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) (oldT : Transparency site.net root)
    (target : RootAccess site.reduce root) (branch : Bool)
    (finish : target.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),lamBind⟩))) :
    ∃ source : RootAccess site.net root,
      accessWord site.net source.val=accessWord site.reduce target.val ∧
      accessKind site.net source.val=accessKind site.reduce target.val ∧
      ∃ index,BindingSuffix site.net source.val index ∧BindingSuffix site.reduce target.val index := by
  let c := cutFragment site.net (pathPartition (Schema.fanAction .lam i j lt) V) site.closed
  let r := fanRight .lam i j
  let first : Endpoint c := .inr (.inl (.inl root))
  obtain ⟨a,b,labels⟩ := target.property.1.1
  have actualHead : target.val.head?=some (AG.plugLeft c r first) := target.property.2.1
  obtain ⟨pending,insideFinish⟩ := labels.pending_new_node c r first actualHead (.inl branch) lamBind finish
  obtain ⟨entry,shape,inverse⟩ := fanRight_copied_aux_prefix .lam i j branch false pending.enter pending.inside
    pending.middle b pending.insideLabels pending.insideHead insideFinish
  have tokens : accessTokens r pending.inside=[] := congrArg (accessTokens r) shape
  have rawHead : (target.val.map (plugEnd c.label r.label).invFun).head?=some (.inl first) := by
    rw [List.head?_map,actualHead]
    exact congrArg some ((plugEnd c.label r.label).left_inv (.inl first))
  obtain ⟨old,oldLabels,oldHead,oldLast,word,index,oldSuffix,newSuffix⟩ :=
    site.pending_copied_lambda_binding_words (.fan .lam i j lt) rfl flow positive oldT
      true false HEq.rfl HEq.rfl pending rawHead tokens entry branch (.inl branch) (.fan site branch) lamBind HEq.rfl inverse
      (by change ((target.val.map (plugEnd c.label r.label).invFun).map (plugEnd c.label r.label)).getLast?=_
          rw [plug_decomposition_flatten]; exact finish)
  change accessWord site.reduce ((target.val.map (plugEnd c.label r.label).invFun).map (plugEnd c.label r.label))=
    accessWord site.net old at word
  change BindingSuffix site.reduce
    ((target.val.map (plugEnd c.label r.label).invFun).map (plugEnd c.label r.label)) index at newSuffix
  rw [plug_decomposition_flatten] at word newSuffix
  have kind : accessKind site.net old=accessKind site.reduce target.val := by
    simp only [accessKind,oldLast,finish,Option.bind_some,Pairing.involutive]
    rfl
  have typed : ∃ observation,accessKind site.net old=some observation := by
    rw [kind]; exact target.property.2.2
  have forward := oldLabels.root_forward_of_flow flow root oldHead positive
  exact ⟨⟨old,⟨⟨⟨_,_,oldLabels⟩,forward⟩,oldHead,typed⟩⟩,word.symm,kind,index,oldSuffix,newSuffix⟩

/-- The actual two-control binding prefix discharges the local token
condition internally. Both BindingSuffix witnesses retain the same index. -/
theorem PathSite.cro_copied_binding_access
    (site : PathSite (Schema.croAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) (oldT : Transparency site.net root)
    (target : RootAccess site.reduce root)
    (finish : target.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),lamBind⟩))) :
    ∃ source : RootAccess site.net root,
      accessWord site.net source.val=accessWord site.reduce target.val ∧
      accessKind site.net source.val=accessKind site.reduce target.val ∧
      ∃ index,BindingSuffix site.net source.val index ∧BindingSuffix site.reduce target.val index := by
  let c := cutFragment site.net (pathPartition (Schema.croAction .lam i j lt) V) site.closed
  let r := unaryRightCore .cro .lam (Bij.refl _) i (j-1)
  let first : Endpoint c := .inr (.inl (.inl root))
  obtain ⟨a,b,labels⟩ := target.property.1.1
  have actualHead : target.val.head?=some (AG.plugLeft c r first) := target.property.2.1
  obtain ⟨pending,insideFinish⟩ := labels.pending_new_node c r first actualHead (.inl ()) lamBind finish
  obtain ⟨entry,shape,inverse⟩ := unaryRight_copied_aux_prefix .cro .lam (Bij.refl _) (Or.inr (Or.inl rfl)) i (j-1) false pending.enter pending.inside
    pending.middle b pending.insideLabels pending.insideHead insideFinish
  have tokens : accessTokens r pending.inside=[] := congrArg (accessTokens r) shape
  have rawHead : (target.val.map (plugEnd c.label r.label).invFun).head?=some (.inl first) := by
    rw [List.head?_map,actualHead]
    exact congrArg some ((plugEnd c.label r.label).left_inv (.inl first))
  obtain ⟨old,oldLabels,oldHead,oldLast,word,index,oldSuffix,newSuffix⟩ :=
    site.pending_copied_lambda_binding_words (.cro .lam i j lt) rfl flow positive oldT
      true false HEq.rfl HEq.rfl pending rawHead tokens entry () (.inl ()) (.cro site) lamBind HEq.rfl inverse
      (by change ((target.val.map (plugEnd c.label r.label).invFun).map (plugEnd c.label r.label)).getLast?=_
          rw [plug_decomposition_flatten]; exact finish)
  change accessWord site.reduce ((target.val.map (plugEnd c.label r.label).invFun).map (plugEnd c.label r.label))=
    accessWord site.net old at word
  change BindingSuffix site.reduce
    ((target.val.map (plugEnd c.label r.label).invFun).map (plugEnd c.label r.label)) index at newSuffix
  rw [plug_decomposition_flatten] at word newSuffix
  have kind : accessKind site.net old=accessKind site.reduce target.val := by
    simp only [accessKind,oldLast,finish,Option.bind_some,Pairing.involutive]
    rfl
  have typed : ∃ observation,accessKind site.net old=some observation := by
    rw [kind]; exact target.property.2.2
  have forward := oldLabels.root_forward_of_flow flow root oldHead positive
  exact ⟨⟨old,⟨⟨⟨_,_,oldLabels⟩,forward⟩,oldHead,typed⟩⟩,word.symm,kind,index,oldSuffix,newSuffix⟩

/-- The actual two-control binding prefix discharges the local token
condition internally. Both BindingSuffix witnesses retain the same index. -/
theorem PathSite.bra_copied_binding_access
    (site : PathSite (Schema.braAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) (oldT : Transparency site.net root)
    (target : RootAccess site.reduce root)
    (finish : target.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),lamBind⟩))) :
    ∃ source : RootAccess site.net root,
      accessWord site.net source.val=accessWord site.reduce target.val ∧
      accessKind site.net source.val=accessKind site.reduce target.val ∧
      ∃ index,BindingSuffix site.net source.val index ∧BindingSuffix site.reduce target.val index := by
  let c := cutFragment site.net (pathPartition (Schema.braAction .lam i j lt) V) site.closed
  let r := unaryRightCore .bra .lam (Bij.refl _) i (j+1)
  let first : Endpoint c := .inr (.inl (.inl root))
  obtain ⟨a,b,labels⟩ := target.property.1.1
  have actualHead : target.val.head?=some (AG.plugLeft c r first) := target.property.2.1
  obtain ⟨pending,insideFinish⟩ := labels.pending_new_node c r first actualHead (.inl ()) lamBind finish
  obtain ⟨entry,shape,inverse⟩ := unaryRight_copied_aux_prefix .bra .lam (Bij.refl _) (Or.inr (Or.inr rfl)) i (j+1) false pending.enter pending.inside
    pending.middle b pending.insideLabels pending.insideHead insideFinish
  have tokens : accessTokens r pending.inside=[] := congrArg (accessTokens r) shape
  have rawHead : (target.val.map (plugEnd c.label r.label).invFun).head?=some (.inl first) := by
    rw [List.head?_map,actualHead]
    exact congrArg some ((plugEnd c.label r.label).left_inv (.inl first))
  obtain ⟨old,oldLabels,oldHead,oldLast,word,index,oldSuffix,newSuffix⟩ :=
    site.pending_copied_lambda_binding_words (.bra .lam i j lt) rfl flow positive oldT
      true false HEq.rfl HEq.rfl pending rawHead tokens entry () (.inl ()) (.bra site) lamBind HEq.rfl inverse
      (by change ((target.val.map (plugEnd c.label r.label).invFun).map (plugEnd c.label r.label)).getLast?=_
          rw [plug_decomposition_flatten]; exact finish)
  change accessWord site.reduce ((target.val.map (plugEnd c.label r.label).invFun).map (plugEnd c.label r.label))=
    accessWord site.net old at word
  change BindingSuffix site.reduce
    ((target.val.map (plugEnd c.label r.label).invFun).map (plugEnd c.label r.label)) index at newSuffix
  rw [plug_decomposition_flatten] at word newSuffix
  have kind : accessKind site.net old=accessKind site.reduce target.val := by
    simp only [accessKind,oldLast,finish,Option.bind_some,Pairing.involutive]
    rfl
  have typed : ∃ observation,accessKind site.net old=some observation := by
    rw [kind]; exact target.property.2.2
  have forward := oldLabels.root_forward_of_flow flow root oldHead positive
  exact ⟨⟨old,⟨⟨⟨_,_,oldLabels⟩,forward⟩,oldHead,typed⟩⟩,word.symm,kind,index,oldSuffix,newSuffix⟩
end
end Lamping.AG
