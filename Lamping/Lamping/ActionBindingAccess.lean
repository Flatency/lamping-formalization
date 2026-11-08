import Lamping.Lamping.ActionCopiedBindingAccess
import Lamping.Lamping.ActionKeptBindingWords
namespace Lamping.AG
open Graph Lambda

private theorem lam_ports (actual : Label signature) (n : Nat) (lab : actual=label .lam n) :
    ∃ ctx body : Port actual.sort,HEq ctx (Sum.inl () : Port (.op .lam)) ∧HEq body lamBody := by
  subst actual
  exact ⟨.inl (),lamBody,HEq.rfl,HEq.rfl⟩

private theorem port_kind_of_label (actual : Label signature) (op : Op) (level : Nat)
    (p : Port actual.sort) (q : Port (.op op)) (lab : actual=label op level) (port : HEq p q) :
    portKind actual.sort p=portKind (.op op) q := by
  subst actual
  have eqs : p=q := eq_of_heq port
  subst p
  rfl
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))

/-- Every actual variable access, retained or copied, has source and target
binding witnesses with the same index. Endpoint roles are derived from the
actual access; no target binder or local token certificate is supplied. -/
theorem PathSite.action_variable_binding_access (action : IsAction s)
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) (oldT : Transparency site.net root)
    (target : RootAccess site.reduce root) (kind : accessKind site.reduce target.val=some .var) :
    ∃ source : RootAccess site.net root,
      accessWord site.net source.val=accessWord site.reduce target.val ∧
      accessKind site.net source.val=accessKind site.reduce target.val ∧
      ∃ index,BindingSuffix site.net source.val index ∧BindingSuffix site.reduce target.val index := by
  obtain ⟨terminal,role,level,finish,atTerminal,incoming⟩ := target.incoming_endpoint
  cases atTerminal with
  | root => exact False.elim incoming
  | appFun => exact False.elim incoming
  | appArg => exact False.elim incoming
  | lamBody => exact False.elim incoming
  | appCtx node p level lab port =>
    have actual : portKind (site.reduce.label node).sort p=some .var := by
      simpa only [accessKind,finish,Option.bind_some,Pairing.involutive] using kind
    rw [port_kind_of_label _ .app level p appCtx lab port] at actual
    cases actual
  | lamCtx node p level lab port =>
    have actual : portKind (site.reduce.label node).sort p=some .var := by
      simpa only [accessKind,finish,Option.bind_some,Pairing.involutive] using kind
    rw [port_kind_of_label _ .lam level p (.inl ()) lab port] at actual
    cases actual
  | lamBind node p level lab port =>
    cases node with
    | inl node =>
      obtain ⟨ctx,body,ctxRole,bodyRole⟩ := lam_ports (kept node) level lab
      exact site.action_kept_binding_suffix_word action flow root positive oldT target node ctx body p
        (congrArg Label.sort lab) ctxRole bodyRole port finish
    | inr node =>
      cases action with
      | fan f i j lt =>
        cases node with
        | inl branch =>
          have same : f=.lam := Kind.op.inj (congrArg Label.sort lab)
          subst f
          have ports : p=lamBind := eq_of_heq port
          subst p
          exact site.fan_copied_binding_access flow root positive oldT target branch finish
        | inr q =>
          have impossible : Op.fan=.lam := Kind.op.inj (congrArg Label.sort lab)
          cases impossible
      | cro f i j lt =>
        cases node with
        | inl u =>
          cases u
          have same : f=.lam := Kind.op.inj (congrArg Label.sort lab)
          subst f
          have ports : p=lamBind := eq_of_heq port
          subst p
          exact site.cro_copied_binding_access flow root positive oldT target finish
        | inr q =>
          have impossible : Op.cro=.lam := Kind.op.inj (congrArg Label.sort lab)
          cases impossible
      | bra f i j lt =>
        cases node with
        | inl u =>
          cases u
          have same : f=.lam := Kind.op.inj (congrArg Label.sort lab)
          subst f
          have ports : p=lamBind := eq_of_heq port
          subst p
          exact site.bra_copied_binding_access flow root positive oldT target finish
        | inr q =>
          have impossible : Op.bra=.lam := Kind.op.inj (congrArg Label.sort lab)
          cases impossible
end
end Lamping.AG
