import Lamping.Lamping.ExpandedIndependence
namespace Lamping.AG
open Graph Lambda

private def CroImage (i : Nat) : (k : Kind) → Port k → Port k → Context → Context → Prop
  | .op .cro,.inr _,.inl _,a,b =>
    ∀ t, b.get t = if t<i then a.get t else if t=i then .empty else a.get (t-1)
  | _,_,_,_,_ => True
private theorem cro_image {i k p q a b} (h : Traversal i k p q a b) : CroImage i k p q a b := by
  cases h with
  | direct hp =>
    cases hp <;> try trivial
    case cro s c =>
      intro t
      by_cases low : t<i
      · simp [Context.replace,low]
      · by_cases eq : t=i
        · subst t; simp [Context.replace,Context.cons]
        · have ht : ¬t-1<i := by omega
          have hd : t-i=(t-1-i)+1 := by omega
          simp [Context.replace,Context.cons,low,eq,ht,hd]
  | inverse hp => cases hp <;> trivial

private def BraImage (i : Nat) : (k : Kind) → Port k → Port k → Context → Context → Prop
  | .op .bra,.inr _,.inl _,a,b =>
    ∀ t, b.get t = if t<i then a.get t else if t=i then .pair (a.get (i+1)) (a.get i)
      else a.get (t+1)
  | _,_,_,_,_ => True
private theorem bra_image {i k p q a b} (h : Traversal i k p q a b) : BraImage i k p q a b := by
  cases h with
  | direct hp =>
    cases hp <;> try trivial
    case bra s c x y =>
      intro t
      by_cases low : t<i
      · simp [Context.replace,low]
      · by_cases eq : t=i
        · subst t
          simp [Context.replace,Context.cons,show ¬i+1<i by omega,
            show i+1-i=1 by omega]
        · have ht : ¬t+1<i := by omega
          have hd : t-i=(t-i-1)+1 := by omega
          have h2 : t+1-i=(t-i-1)+1+1 := by omega
          simp only [if_neg low,if_neg eq]
          rw [Context.replace_high _ _ (by omega : i≤t),
            Context.replace_high _ _ (by omega : i≤t+1),hd,h2]
          rfl
  | inverse hp => cases hp <;> trivial

/-- A fixed directed proper turn is a partial function on contexts. The
inverses of controls retain their side constraints; no total inverse is assumed. -/
theorem Traversal.output_unique {i : Nat} {kind : Kind} {p q : Port kind} {a b c : Context}
    (h : Traversal i kind p q a b) (k : Traversal i kind p q a c) : b=c := by
  cases kind with
  | garbage => cases h with | direct hp => cases hp | inverse hp => cases hp <;> trivial
  | op op =>
    cases op with
    | app => exact h.proper_context.symm.trans k.proper_context
    | lam => exact h.proper_context.symm.trans k.proper_context
    | fan =>
      cases p with
      | inl u =>
        cases u
        cases q with
        | inl v => cases v; exact False.elim (h.distinct rfl)
        | inr branch =>
          ext t
          by_cases eq : t=i
          · subst t
            have hh := h.fan_marker
            have hk := k.fan_marker
            cases branch <;> simp_all [FanEdgeMarker]
          · exact (h.fan_other_levels t eq).symm.trans (k.fan_other_levels t eq)
      | inr branch =>
        cases q with
        | inl u =>
          cases u
          ext t
          by_cases eq : t=i
          · subst t
            have hh := h.fan_marker
            have hk := k.fan_marker
            cases branch <;> simp_all [FanEdgeMarker]
          · exact (h.fan_other_levels t eq).symm.trans (k.fan_other_levels t eq)
        | inr branch' => exact False.elim h.aux_aux
    | cro =>
      cases p with
      | inl u =>
        cases u
        cases q with
        | inl v => cases v; exact False.elim (h.distinct rfl)
        | inr v =>
          cases v
          ext t
          exact (h.cro_constraint t).trans (k.cro_constraint t).symm
      | inr u =>
        cases u
        cases q with
        | inl v =>
          cases v
          ext t
          exact (cro_image h t).trans (cro_image k t).symm
        | inr v => cases v; exact False.elim (h.distinct rfl)
    | bra =>
      cases p with
      | inl u =>
        cases u
        cases q with
        | inl v => cases v; exact False.elim (h.distinct rfl)
        | inr v =>
          cases v
          ext t
          exact (h.bra_constraint t).trans (k.bra_constraint t).symm
      | inr u =>
        cases u
        cases q with
        | inl v =>
          cases v
          ext t
          exact (bra_image h t).trans (bra_image k t).symm
        | inr v => cases v; exact False.elim (h.distinct rfl)


private theorem no_lambda_binding_traversal {i : Nat} {kind : Kind} {p q : Port kind}
    (sort : kind=.op .lam) (bind : HEq p lamBind)
    (h : Traversal i kind p q a b) : False := by
  subst kind
  have hp : p=lamBind := eq_of_heq bind
  subst p
  exact h.no_binding.1 rfl

private def AppPrincipalConstraint : (kind : Kind) → Port kind → Port kind → Prop
  | .op .app,.inl _,q => q=appCtx
  | _,_,_ => True
private theorem Traversal.app_principal {i kind p q a b} (h : Traversal i kind p q a b) :
    AppPrincipalConstraint kind p q := by
  cases h with
  | direct hp => cases hp <;> trivial
  | inverse hp => cases hp <;> trivial

private theorem no_app_fun_arg_traversal {i : Nat} {kind : Kind} {p q : Port kind}
    (sort : kind=.op .app)
    (funRole : HEq p (Sum.inl () : Port (.op .app))) (argRole : HEq q appArg)
    (h : Traversal i kind p q a b) : False := by
  subst kind
  have hp : p=.inl () := eq_of_heq funRole
  have hq : q=appArg := eq_of_heq argRole
  subst p; subst q
  cases h.app_principal
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

 theorem LabelledTurn.output_unique {e f : Endpoint g} {a b c : Context}
    (h : LabelledTurn g e f a b) (k : LabelledTurn g e f a c) : b=c := by
  cases h with
  | node n p q h => cases k with | node n p q k => exact h.output_unique k
  | transparent w d a => cases k; rfl

 theorem ContextTrace.input_unique {es : List (Endpoint g)} {cs ds : List Context}
    (h : ContextTrace g es cs) (k : ContextTrace g es ds) (first : cs.head?=ds.head?) : cs=ds := by
  induction h generalizing ds with
  | single e a =>
    cases k with
    | single e b =>
      have eq : a=b := Option.some.inj first
      rw [eq]
  | cons turn tail ih =>
    cases k with
    | cons turn' tail' =>
      have eq := Option.some.inj first
      cases eq
      have middle := turn.output_unique turn'
      cases middle
      exact congrArg (_::·) (ih tail' rfl)

 theorem Labelling.output_unique {es : List (Endpoint g)} {a b c : Context}
    (h : Labelling g es a b) (k : Labelling g es a c) : b=c := by
  obtain ⟨cs,ht,hfirst,hlast⟩ := h.contextTrace g
  obtain ⟨ds,kt,kfirst,klast⟩ := k.contextTrace g
  have eq := ht.input_unique kt (hfirst.trans kfirst.symm)
  have last := congrArg List.getLast? eq
  exact Option.some.inj (hlast.symm.trans (last.trans klast))

private def ProperInputContext (e : Endpoint g) (a b : Context) : Prop :=
  match e with
  | .inl ⟨n,_⟩ => ProperContextInvariant (g.label n).sort a b
  | _ => True

private theorem expandedTurn_proper_context {e f : Endpoint g} {a b : Context}
    (h : ExpandedTurn g e f a b) : ProperInputContext e a b := by
  cases h with
  | ordinary labels =>
    cases labels with
    | node n p q rule => exact rule.proper_context
    | transparent => trivial
  | bindToCtx r a =>
    change ProperContextInvariant (g.label r.lam).sort a a
    rw [r.lamLabel]
    rfl
  | funToArg r a =>
    change ProperContextInvariant (g.label r.app).sort a a
    rw [r.appLabel]
    rfl

theorem ExpandedTurn.output_unique {e f : Endpoint g} {a b c : Context}
    (h : ExpandedTurn g e f a b) (k : ExpandedTurn g e f a c) : b=c := by
  cases h with
  | ordinary labels =>
    cases k with
    | ordinary other => exact labels.output_unique other
    | bindToCtx r a =>
      cases labels with
      | node n p q rule =>
        exact False.elim (no_lambda_binding_traversal
          (congrArg Label.sort r.lamLabel) r.lamBind_role rule)
    | funToArg r a =>
      cases labels with
      | node n p q rule =>
        exact False.elim (no_app_fun_arg_traversal
          (congrArg Label.sort r.appLabel) r.appFun_role r.appArg_role rule)
  | bindToCtx r a =>
    have hc := expandedTurn_proper_context k
    change ProperContextInvariant (g.label r.lam).sort a c at hc
    rw [r.lamLabel] at hc
    exact hc
  | funToArg r a =>
    have hc := expandedTurn_proper_context k
    change ProperContextInvariant (g.label r.app).sort a c at hc
    rw [r.appLabel] at hc
    exact hc
 theorem ExpandedContextTrace.input_unique {es : List (Endpoint g)} {cs ds : List Context}
    (h : ExpandedContextTrace g es cs) (k : ExpandedContextTrace g es ds)
    (first : cs.head?=ds.head?) : cs=ds := by
  induction h generalizing ds with
  | single e a =>
    cases k with
    | single e b =>
      have eq : a=b := Option.some.inj first
      rw [eq]
  | cons turn tail ih =>
    cases k with
    | cons turn' tail' =>
      have eq := Option.some.inj first
      cases eq
      have middle := turn.output_unique turn'
      cases middle
      exact congrArg (_::·) (ih tail' rfl)

 theorem ExpandedLabelling.output_unique {es : List (Endpoint g)} {a b c : Context}
    (h : ExpandedLabelling g es a b) (k : ExpandedLabelling g es a c) : b=c := by
  obtain ⟨cs,ht,hfirst,hlast⟩ := h.contextTrace g
  obtain ⟨ds,kt,kfirst,klast⟩ := k.contextTrace g
  have eq := ht.input_unique kt (hfirst.trans kfirst.symm)
  have last := congrArg List.getLast? eq
  exact Option.some.inj (hlast.symm.trans (last.trans klast))

 theorem Labelling.prefix {pre tail : List (Endpoint g)}
    (h : Labelling g (pre++tail) a b) (nonempty : pre≠[]) :
    ∃ c, Labelling g pre a c := by
  induction pre generalizing a with
  | nil => exact False.elim (nonempty rfl)
  | cons e pre ih =>
    cases pre with
    | nil => exact ⟨a,.single _ _⟩
    | cons f pre =>
      cases h with
      | cons turn rest =>
        obtain ⟨c,hc⟩ := ih rest (by simp)
        exact ⟨c,.cons turn hc⟩

 theorem ExpandedLabelling.prefix {pre tail : List (Endpoint g)}
    (h : ExpandedLabelling g (pre++tail) a b) (nonempty : pre≠[]) :
    ∃ c, ExpandedLabelling g pre a c := by
  induction pre generalizing a with
  | nil => exact False.elim (nonempty rfl)
  | cons e pre ih =>
    cases pre with
    | nil => exact ⟨a,.single _ _⟩
    | cons f pre =>
      cases h with
      | cons turn rest =>
        obtain ⟨c,hc⟩ := ih rest (by simp)
        exact ⟨c,.cons turn hc⟩

/-- Same input on a common physical prefix forces the same seam context.
No path matching, invariant or arbitrary-context existence is presupposed. -/
theorem ExpandedLabelling.prefix_context_unique {pre left : List (Endpoint g)}
    (h : ExpandedLabelling g (pre++left) a b)
    (nonempty : pre≠[]) :
    ∃ middle, ExpandedLabelling g pre a middle ∧
      ∀ d, ExpandedLabelling g pre a d → d=middle := by
  obtain ⟨middle,hm⟩ := h.prefix nonempty
  exact ⟨middle,hm,by intro d hd; exact hd.output_unique hm⟩
end
end Lamping.AG

namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

/-- A physical port pair which admits an ordinary turn cannot instead use
either added beta seam. Its old assignment is only a shape witness. -/
theorem ExpandedTurn.ordinary_of_shape {x y : Endpoint g} {a b originalA originalB : Context}
    (shape : LabelledTurn g x y originalA originalB) (turn : ExpandedTurn g x y a b) :
    LabelledTurn g x y a b := by
  cases turn with
  | ordinary actual => exact actual
  | bindToCtx edge a =>
    cases shape with
    | node n p q rule =>
      exact False.elim (no_lambda_binding_traversal
        (congrArg Label.sort edge.lamLabel) edge.lamBind_role rule)
  | funToArg edge a =>
    cases shape with
    | node n p q rule =>
      exact False.elim (no_app_fun_arg_traversal
        (congrArg Label.sort edge.appLabel) edge.appFun_role edge.appArg_role rule)
end
end Lamping.AG






