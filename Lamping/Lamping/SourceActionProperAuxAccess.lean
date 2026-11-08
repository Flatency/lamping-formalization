import Lamping.Lamping.SourceActionLambdaAccess
import Lamping.Lamping.SourceBindingControlBranch
namespace Lamping.AG
open Graph Lambda
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable {root : B} {t : Term} {boundary : B → Bool}

theorem PathSite.fan_source_app_access
    (site : PathSite (.fanAction .app i j lt) kept (B:=B) (W:=W) (V:=V))
    (matching : Matches site.net root t) (inputs : RootInputs site.net root)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (source : RootAccess site.net root)
    (finish : source.val.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),appCtx⟩))) :
    ∃ target : RootAccess site.reduce root,
      accessWord site.reduce target.val=accessWord site.net source.val ∧
      accessKind site.reduce target.val=accessKind site.net source.val := by
  obtain ⟨a,b,labels⟩ := source.property.1.1
  obtain ⟨q,uniform⟩ := site.source_control_branch matching inputs flow positive (Or.inl rfl) rfl
    source.val appCtx HEq.rfl labels source.property.2.1 finish
  obtain ⟨middle,inverse⟩ := uniform a b labels
  
  exact site.fan_source_aux_access matching inputs flow positive source false finish labels q inverse

theorem PathSite.fan_source_binding_access
    (site : PathSite (.fanAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
    (matching : Matches site.net root t) (inputs : RootInputs site.net root)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (transparency : Transparency site.net root) (source : RootAccess site.net root)
    (finish : source.val.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),lamBind⟩))) :
    ∃ target : RootAccess site.reduce root,
      accessWord site.reduce target.val=accessWord site.net source.val ∧
      accessKind site.reduce target.val=accessKind site.net source.val := by
  obtain ⟨a,b,labels⟩ := source.property.1.1
  obtain ⟨q,middle,inverse⟩ := site.source_binding_control_branch transparency (Or.inl rfl) rfl lt
    lamBody lamBind HEq.rfl HEq.rfl labels source.property.1.2 source.property.2.1 finish
  
  exact site.fan_source_aux_access matching inputs flow positive source false finish labels q inverse

theorem PathSite.cro_source_app_access
    (site : PathSite (.croAction .app i j lt) kept (B:=B) (W:=W) (V:=V))
    (matching : Matches site.net root t) (inputs : RootInputs site.net root)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (source : RootAccess site.net root)
    (finish : source.val.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),appCtx⟩))) :
    ∃ target : RootAccess site.reduce root,
      accessWord site.reduce target.val=accessWord site.net source.val ∧
      accessKind site.reduce target.val=accessKind site.net source.val := by
  obtain ⟨a,b,labels⟩ := source.property.1.1
  obtain ⟨q,uniform⟩ := site.source_control_branch matching inputs flow positive (Or.inr (Or.inl rfl)) rfl
    source.val appCtx HEq.rfl labels source.property.2.1 finish
  obtain ⟨middle,inverse⟩ := uniform a b labels
  cases q
  exact site.cro_source_aux_access matching inputs flow positive source false finish labels  inverse

theorem PathSite.cro_source_binding_access
    (site : PathSite (.croAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
    (matching : Matches site.net root t) (inputs : RootInputs site.net root)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (transparency : Transparency site.net root) (source : RootAccess site.net root)
    (finish : source.val.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),lamBind⟩))) :
    ∃ target : RootAccess site.reduce root,
      accessWord site.reduce target.val=accessWord site.net source.val ∧
      accessKind site.reduce target.val=accessKind site.net source.val := by
  obtain ⟨a,b,labels⟩ := source.property.1.1
  obtain ⟨q,middle,inverse⟩ := site.source_binding_control_branch transparency (Or.inr (Or.inl rfl)) rfl lt
    lamBody lamBind HEq.rfl HEq.rfl labels source.property.1.2 source.property.2.1 finish
  cases q
  exact site.cro_source_aux_access matching inputs flow positive source false finish labels  inverse

theorem PathSite.bra_source_app_access
    (site : PathSite (.braAction .app i j lt) kept (B:=B) (W:=W) (V:=V))
    (matching : Matches site.net root t) (inputs : RootInputs site.net root)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (source : RootAccess site.net root)
    (finish : source.val.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),appCtx⟩))) :
    ∃ target : RootAccess site.reduce root,
      accessWord site.reduce target.val=accessWord site.net source.val ∧
      accessKind site.reduce target.val=accessKind site.net source.val := by
  obtain ⟨a,b,labels⟩ := source.property.1.1
  obtain ⟨q,uniform⟩ := site.source_control_branch matching inputs flow positive (Or.inr (Or.inr rfl)) rfl
    source.val appCtx HEq.rfl labels source.property.2.1 finish
  obtain ⟨middle,inverse⟩ := uniform a b labels
  cases q
  exact site.bra_source_aux_access matching inputs flow positive source false finish labels  inverse

theorem PathSite.bra_source_binding_access
    (site : PathSite (.braAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
    (matching : Matches site.net root t) (inputs : RootInputs site.net root)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (transparency : Transparency site.net root) (source : RootAccess site.net root)
    (finish : source.val.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),lamBind⟩))) :
    ∃ target : RootAccess site.reduce root,
      accessWord site.reduce target.val=accessWord site.net source.val ∧
      accessKind site.reduce target.val=accessKind site.net source.val := by
  obtain ⟨a,b,labels⟩ := source.property.1.1
  obtain ⟨q,middle,inverse⟩ := site.source_binding_control_branch transparency (Or.inr (Or.inr rfl)) rfl lt
    lamBody lamBind HEq.rfl HEq.rfl labels source.property.1.2 source.property.2.1 finish
  cases q
  exact site.bra_source_aux_access matching inputs flow positive source false finish labels  inverse
end
end Lamping.AG
