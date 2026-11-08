import Lamping.Lamping.SourceActionProperAuxAccess
import Lamping.Lamping.SourceActionKeptAccess
namespace Lamping.AG
open Graph Lambda
section
variable {s : Schema} {K B W V : Type}
variable [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))

/-- Every actual proper-ended source root access has a CONSTRUCTED target
root access with the same syntax word and kind. All retained and copied
proper endpoints are classified from their actual labels and ports. -/
theorem PathSite.action_access_forward (action : IsAction s)
    {root : B} {t : Term} {boundary : B → Bool}
    (matching : Matches site.net root t) (inputs : RootInputs site.net root)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (transparency : Transparency site.net root) (source : RootAccess site.net root) :
    ∃ target : RootAccess site.reduce root,
      accessWord site.reduce target.val=accessWord site.net source.val ∧
      accessKind site.reduce target.val=accessKind site.net source.val := by
  obtain ⟨terminal,role,level,finish,atTerminal,incoming⟩ := source.incoming_endpoint
  cases atTerminal with
  | root => exact False.elim incoming
  | appFun => exact False.elim incoming
  | appArg => exact False.elim incoming
  | lamBody => exact False.elim incoming
  | appCtx node p level lab port =>
    cases node with
    | inl node => exact site.action_kept_access_forward action matching inputs flow positive source node p finish
    | inr node =>
      cases action with
      | fan f i j lt =>
        cases node with
        | inl u =>
          have impossible : Op.fan=.app := Kind.op.inj (congrArg Label.sort lab)
          cases impossible
        | inr u =>
          cases u
          have same : f=.app := Kind.op.inj (congrArg Label.sort lab)
          subst f
          have ports : p=appCtx := eq_of_heq port
          subst p
          exact site.fan_source_app_access matching inputs flow positive source finish
      | cro f i j lt =>
        cases node with
        | inl u =>
          have impossible : Op.cro=.app := Kind.op.inj (congrArg Label.sort lab)
          cases impossible
        | inr u =>
          cases u
          have same : f=.app := Kind.op.inj (congrArg Label.sort lab)
          subst f
          have ports : p=appCtx := eq_of_heq port
          subst p
          exact site.cro_source_app_access matching inputs flow positive source finish
      | bra f i j lt =>
        cases node with
        | inl u =>
          have impossible : Op.bra=.app := Kind.op.inj (congrArg Label.sort lab)
          cases impossible
        | inr u =>
          cases u
          have same : f=.app := Kind.op.inj (congrArg Label.sort lab)
          subst f
          have ports : p=appCtx := eq_of_heq port
          subst p
          exact site.bra_source_app_access matching inputs flow positive source finish
  | lamCtx node p level lab port =>
    cases node with
    | inl node => exact site.action_kept_access_forward action matching inputs flow positive source node p finish
    | inr node =>
      cases action with
      | fan f i j lt =>
        cases node with
        | inl u =>
          have impossible : Op.fan=.lam := Kind.op.inj (congrArg Label.sort lab)
          cases impossible
        | inr u =>
          cases u
          have same : f=.lam := Kind.op.inj (congrArg Label.sort lab)
          subst f
          have ports : p=(.inl () : Port (.op .lam)) := eq_of_heq port
          subst p
          exact site.fan_source_lam_access matching inputs flow positive source finish
      | cro f i j lt =>
        cases node with
        | inl u =>
          have impossible : Op.cro=.lam := Kind.op.inj (congrArg Label.sort lab)
          cases impossible
        | inr u =>
          cases u
          have same : f=.lam := Kind.op.inj (congrArg Label.sort lab)
          subst f
          have ports : p=(.inl () : Port (.op .lam)) := eq_of_heq port
          subst p
          exact site.cro_source_lam_access matching inputs flow positive source finish
      | bra f i j lt =>
        cases node with
        | inl u =>
          have impossible : Op.bra=.lam := Kind.op.inj (congrArg Label.sort lab)
          cases impossible
        | inr u =>
          cases u
          have same : f=.lam := Kind.op.inj (congrArg Label.sort lab)
          subst f
          have ports : p=(.inl () : Port (.op .lam)) := eq_of_heq port
          subst p
          exact site.bra_source_lam_access matching inputs flow positive source finish
  | lamBind node p level lab port =>
    cases node with
    | inl node => exact site.action_kept_access_forward action matching inputs flow positive source node p finish
    | inr node =>
      cases action with
      | fan f i j lt =>
        cases node with
        | inl u =>
          have impossible : Op.fan=.lam := Kind.op.inj (congrArg Label.sort lab)
          cases impossible
        | inr u =>
          cases u
          have same : f=.lam := Kind.op.inj (congrArg Label.sort lab)
          subst f
          have ports : p=lamBind := eq_of_heq port
          subst p
          exact site.fan_source_binding_access matching inputs flow positive transparency source finish
      | cro f i j lt =>
        cases node with
        | inl u =>
          have impossible : Op.cro=.lam := Kind.op.inj (congrArg Label.sort lab)
          cases impossible
        | inr u =>
          cases u
          have same : f=.lam := Kind.op.inj (congrArg Label.sort lab)
          subst f
          have ports : p=lamBind := eq_of_heq port
          subst p
          exact site.cro_source_binding_access matching inputs flow positive transparency source finish
      | bra f i j lt =>
        cases node with
        | inl u =>
          have impossible : Op.bra=.lam := Kind.op.inj (congrArg Label.sort lab)
          cases impossible
        | inr u =>
          cases u
          have same : f=.lam := Kind.op.inj (congrArg Label.sort lab)
          subst f
          have ports : p=lamBind := eq_of_heq port
          subst p
          exact site.bra_source_binding_access matching inputs flow positive transparency source finish
end
end Lamping.AG
