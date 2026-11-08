import Lamping.Lamping.ActionCopiedTransparency
import Lamping.Lamping.ActionKeptTransparency
namespace Lamping.AG
open Graph
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))

/-- All three actual action schemas preserve ordinary Transparency. Kept
and copied lambdas are classified from the actual RHS node/port metadata;
fresh controls cannot masquerade as lambda binders. The source premise is
only ordinary T and structural root flow, with no I/N/Matches oracle. -/
theorem PathSite.action_transparency (action : IsAction s)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary) (root : B) (positive : boundary root=true)
    (oldT : Transparency site.net root) : Transparency site.reduce root := by
  intro es a b node ctx body bind isLam ctxRole bodyRole bindRole rooted finish forward labels
  cases node with
  | inl node =>
    exact site.action_kept_transparency action flow root positive oldT es a b node ctx body bind
      isLam ctxRole bodyRole bindRole rooted finish forward labels
  | inr node =>
    cases action with
    | fan f i j lt => cases node with
      | inr q => cases isLam
      | inl branch =>
        have same : f=.lam := by change Kind.op f=Kind.op .lam at isLam; exact Kind.op.inj isLam
        subst f
        have hc : ctx=.inl () := eq_of_heq ctxRole
        have hb : body=lamBody := eq_of_heq bodyRole
        have hv : bind=lamBind := eq_of_heq bindRole
        subst ctx
        subst body
        subst bind
        exact site.fan_copied_lambda_transparency flow root positive oldT labels rooted branch finish
    | cro f i j lt => cases node with
      | inr q => cases isLam
      | inl u =>
        cases u
        have same : f=.lam := by change Kind.op f=Kind.op .lam at isLam; exact Kind.op.inj isLam
        subst f
        have hc : ctx=.inl () := eq_of_heq ctxRole
        have hb : body=lamBody := eq_of_heq bodyRole
        have hv : bind=lamBind := eq_of_heq bindRole
        subst ctx
        subst body
        subst bind
        exact site.cro_copied_lambda_transparency flow root positive oldT labels rooted finish
    | bra f i j lt => cases node with
      | inr q => cases isLam
      | inl u =>
        cases u
        have same : f=.lam := by change Kind.op f=Kind.op .lam at isLam; exact Kind.op.inj isLam
        subst f
        have hc : ctx=.inl () := eq_of_heq ctxRole
        have hb : body=lamBody := eq_of_heq bodyRole
        have hv : bind=lamBind := eq_of_heq bindRole
        subst ctx
        subst body
        subst bind
        exact site.bra_copied_lambda_transparency flow root positive oldT labels rooted finish
end
end Lamping.AG
