import Lamping.Lamping.ExpandedInvariantDefinitions
namespace Lamping.AG
open Graph Lambda

private theorem no_lambda_binding_forward (k : Kind) (p q : Port k)
    (kind : k=.op .lam) (bind : HEq p lamBind) : ¬ForwardPorts k p q := by
  subst k
  have hp : p=lamBind := eq_of_heq bind
  subst p
  intro hd
  cases hd.1

private theorem no_application_principal_forward (k : Kind) (p q : Port k)
    (kind : k=.op .app) (funPort : HEq p (Sum.inl () : Port (.op .app))) :
    ¬ForwardPorts k p q := by
  subst k
  have hp : p=.inl () := eq_of_heq funPort
  subst p
  intro hd
  cases hd.1

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable (g : Net signature N B W)

/-- A truly forward ordinary port turn cannot use either extra reversed-beta
constructor, even if its context happens to admit both sorts of labels. -/
theorem ExpandedTurn.ordinary_of_ports (n : N) (p q : Port (g.label n).sort)
    (hd : ForwardPorts (g.label n).sort p q)
    (h : ExpandedTurn g (.inl ⟨n,p⟩) (.inl ⟨n,q⟩) a b) :
    LabelledTurn g (.inl ⟨n,p⟩) (.inl ⟨n,q⟩) a b := by
  cases h with
  | ordinary labels => exact labels
  | bindToCtx r a =>
    exact False.elim ((no_lambda_binding_forward _ _ _
      (congrArg Label.sort r.lamLabel) r.lamBind_role) hd)
  | funToArg r a =>
    exact False.elim ((no_application_principal_forward _ _ _
      (congrArg Label.sort r.appLabel) r.appFun_role) hd)

/-- Reflection preserves the complete supplied context assignment. It uses
actual Forward incidence, rather than silently choosing a different labelling. -/
theorem ExpandedContextTrace.ordinary_of_forward {es : List (Endpoint g)} {cs : List Context}
    (trace : ExpandedContextTrace g es cs) (fw : Forward g es) : ContextTrace g es cs := by
  induction trace with
  | single e a => exact .single e a
  | cons turn tail ih =>
    cases fw with
    | node n p q ha hl hd hs =>
      apply ContextTrace.cons
      · rw [ha,hl] at turn ⊢
        exact turn.ordinary_of_ports g n p q hd
      · exact ih hs
    | transparent w d ha hl hs =>
      apply ContextTrace.cons
      · rw [ha,hl] at turn ⊢
        cases turn with
        | ordinary labels => exact labels
      · exact ih hs

 theorem ExpandedLabelling.ordinary_of_forward {es : List (Endpoint g)}
    (labels : ExpandedLabelling g es a b) (fw : Forward g es) : Labelling g es a b := by
  obtain ⟨cs,trace,first,last⟩ := labels.contextTrace g
  exact (trace.ordinary_of_forward g fw).labelling g first last

/-- The nesting base of Lemma3.5.17 applies to every expanded assignment on
an ordinary forward path, not merely the one used by its generator. -/
theorem Nesting.expanded_base {root : B} (nest : Nesting g root)
    {es : List (Endpoint g)} {cs : List Context}
    (rooted : es.head?=some (.inr (.inl root))) (fw : Forward g es)
    (labels : ExpandedContextTrace g es cs)
    (i j : Nat) (e : Endpoint g) (a b : Context) (n : Nat) (role : ProperRole)
    (lt : i<j) (atI : es[i]?=some e) (atJ : es[j]?=some e)
    (contextI : cs[i]?=some a) (contextJ : cs[j]?=some b)
    (contextRole : role=.appCtx ∨ role=.lamCtx) (atRole : AtProperRole g root (g.wire e) role n) :
    ¬Context.SameShell n a b :=
  nest es cs (labels.ordinary_of_forward g fw) rooted fw
    i j e a b n role lt atI atJ contextI contextJ contextRole atRole

/-- The transparency base retains the same binder, seam and terminal labels. -/
theorem Transparency.expanded_base {root : B} (trans : Transparency g root)
    (es : List (Endpoint g)) (a b : Context) (n : N)
    (ctx body bind : Port (g.label n).sort)
    (isLam : (g.label n).sort=.op .lam)
    (ctxRole : HEq ctx (Sum.inl () : Port (.op .lam)))
    (bodyRole : HEq body lamBody) (bindRole : HEq bind lamBind)
    (rooted : es.head?=some (.inr (.inl root)))
    (finish : es.getLast?=some (g.wire (.inl ⟨n,bind⟩)))
    (fw : Forward g es) (labels : ExpandedLabelling g es a b) :
    ∃ (pre loop : List (Endpoint g)) (middle : Context)
      (binding : ExpandedBindingLoop g loop middle b),
      es=pre++loop ∧ binding.binder=n ∧
      pre.getLast?=some (g.wire (.inl ⟨n,ctx⟩)) ∧ ExpandedLabelling g pre a middle := by
  obtain ⟨pre,loop,middle,binding,eq,same,last,preLabels⟩ :=
    trans es a b n ctx body bind isLam ctxRole bodyRole bindRole rooted finish fw
      (labels.ordinary_of_forward g fw)
  exact ⟨pre,loop,middle,binding.expanded,eq,same,last,preLabels.expanded⟩
end
end Lamping.AG
