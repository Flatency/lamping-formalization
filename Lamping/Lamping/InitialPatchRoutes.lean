import Lamping.Lamping.InitialLoopProjection
namespace Lamping.AG
open Graph Lambda
theorem Traversal.not_binding_heq {i k p q a b} (h : Traversal i k p q a b)
    (kind : k=.op .lam) (role : HEq p lamBind) : False := by
  subst k
  have eq : p=lamBind := eq_of_heq role
  subst p
  exact h.no_binding.1 rfl
section Terminal
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}
/-- A segment arriving where no labelled turn exists terminates every labelling. -/
theorem Labelling.terminal {es : List (Endpoint g)} {e : Endpoint g} {a b : Context}
    (h : Labelling g es a b) (start : es.head?=some e)
    (stop : ∀ f c d, LabelledTurn g (g.wire e) f c d → False) :
    es=[e] ∧ a=b := by
  cases h with
  | single x c => simp only [List.head?_cons,Option.some.injEq] at start; subst x; exact ⟨rfl,rfl⟩
  | cons turn tail =>
    simp only [List.head?_cons,Option.some.injEq] at start
    subst e
    exact False.elim (stop _ _ _ turn)
theorem Labelling.boundary_terminal {es : List (Endpoint g)} {e : Endpoint g} {a b : Context}
    (h : Labelling g es a b) (start : es.head?=some e) (z : B)
    (arrival : g.wire e=.inr (.inl z)) : es=[e] ∧ a=b := by
  apply h.terminal start
  intro f c d turn
  exact turn.not_boundary z arrival

theorem Labelling.binding_terminal {es : List (Endpoint g)} {e : Endpoint g} {a b : Context}
    (h : Labelling g es a b) (start : es.head?=some e)
    (v : N) (kind : (g.label v).sort=.op .lam) (p : Port (g.label v).sort)
    (role : HEq p lamBind) (arrival : g.wire e=.inl ⟨v,p⟩) : es=[e] ∧ a=b := by
  apply h.terminal start
  intro f c d turn
  obtain ⟨q,_,rule⟩ := turn.from_node v p arrival
  exact Traversal.not_binding_heq rule kind role
end Terminal

/-- The used lambda body segment goes directly to its unique child root. -/
theorem lambdaUsed_body_to_child (n : Nat) (body : Term) (used : free body 0)
    {es : List (Endpoint (lambdaUsed n body used))} {a b : Context}
    (h : Labelling (lambdaUsed n body used) es a b)
    (start : es.head?=some (.inl ⟨(),lamBody⟩)) (z : Boundary body)
    (finish : es.getLast?=some ((lambdaUsed n body used).wire (.inr (.inl (.inr z))))) :
    es=[.inl ⟨(),lamBody⟩] ∧ z=.inl () ∧ a=b := by
  obtain ⟨eq,contexts⟩ := h.boundary_terminal start (.inr (.inl ())) rfl
  refine ⟨eq,?_,contexts⟩
  rw [eq] at finish
  have mate := congrArg (lambdaUsed n body used).wire.mate (Option.some.inj finish)
  simp only [Pairing.involutive] at mate
  cases z with
  | inl u => cases u; rfl
  | inr x => cases mate

/-- The unused lambda body has the same actual direct child-root segment. -/
theorem lambdaUnused_body_to_child (n : Nat) (body : Term) (unused : ¬free body 0)
    {es : List (Endpoint (lambdaUnused n body unused))} {a b : Context}
    (h : Labelling (lambdaUnused n body unused) es a b)
    (start : es.head?=some (.inl ⟨.inl (),lamBody⟩)) (z : Boundary body)
    (finish : es.getLast?=some ((lambdaUnused n body unused).wire (.inr (.inl (.inr z))))) :
    es=[.inl ⟨.inl (),lamBody⟩] ∧ z=.inl () ∧ a=b := by
  obtain ⟨eq,contexts⟩ := h.boundary_terminal start (.inr (.inl ())) rfl
  refine ⟨eq,?_,contexts⟩
  rw [eq] at finish
  have mate := congrArg (lambdaUnused n body unused).wire.mate (Option.some.inj finish)
  simp only [Pairing.involutive] at mate
  cases z with
  | inl u => cases u; rfl
  | inr x => cases mate

/-- A used lambda binding can only be reached from the child's free variable 0,
and the source patch suffix contains no control action. -/
theorem lambdaUsed_child_to_binding (n : Nat) (body : Term) (used : free body 0)
    (x : FV body) {es : List (Endpoint (lambdaUsed n body used))} {a b : Context}
    (h : Labelling (lambdaUsed n body used) es a b)
    (start : es.head?=some (.inr (.inl (.inr (.inr x)))))
    (finish : es.getLast?=some ((lambdaUsed n body used).wire (.inl ⟨(),lamBind⟩))) :
    es=[.inr (.inl (.inr (.inr x)))] ∧ x.val=0 ∧ a=b := by
  obtain ⟨k,hk⟩ := x
  cases k with
  | zero =>
    obtain ⟨eq,contexts⟩ := h.binding_terminal start () rfl lamBind (HEq.rfl) rfl
    exact ⟨eq,rfl,contexts⟩
  | succ k =>
    obtain ⟨eq,_⟩ := h.boundary_terminal start (.inl (.inr ⟨k,hk⟩)) rfl
    rw [eq] at finish
    cases finish

/-- An unused lambda has no actual child-FV-to-binding labelled path. -/
theorem lambdaUnused_child_not_binding (n : Nat) (body : Term) (unused : ¬free body 0)
    (x : FV body) {es : List (Endpoint (lambdaUnused n body unused))} {a b : Context}
    (h : Labelling (lambdaUnused n body unused) es a b)
    (start : es.head?=some (.inr (.inl (.inr (.inr x)))))
    (finish : es.getLast?=some ((lambdaUnused n body unused).wire (.inl ⟨.inl (),lamBind⟩))) : False := by
  obtain ⟨k,hk⟩ := x
  cases k with
  | zero => exact unused hk
  | succ k =>
    obtain ⟨eq,_⟩ := h.boundary_terminal start (.inl (.inr ⟨k,hk⟩)) rfl
    rw [eq] at finish
    cases finish
end Lamping.AG
namespace Lamping.AG
open Graph Lambda
theorem Traversal.lam_context {i : Nat} {q : Port (.op .lam)} {a b : Context} (h : Traversal i (.op .lam) (.inl ()) q a b) :
    q=lamBody ∧ a=b := by
  refine ⟨?_,h.proper_context⟩
  cases q with
  | inl u => cases u; exact False.elim (h.distinct rfl)
  | inr q => cases q with
    | false => exact False.elim (h.no_binding.2 rfl)
    | true => rfl

theorem lambdaUsed_root_to_child (n : Nat) (body : Term) (used : free body 0)
    {a b : Context} (z : Boundary body)
    (p : LocalPath (lambdaUsed n body used) (.inl (.inl ())) (.inr z) a b) :
    p.edges=[.inr (.inl (.inl (.inl ()))),.inl ⟨(),lamBody⟩] ∧ z=.inl () ∧ a=b := by
  have labels := p.labeling
  have start := p.start
  have finish := p.finish
  generalize eq : p.edges=es at labels start finish ⊢
  cases labels with
  | single e c =>
    simp only [List.head?_cons,Option.some.injEq] at start
    subst e
    cases z with
    | inl u => cases finish
    | inr x => cases x with | mk k hk => cases k <;> cases finish
  | @cons e f es A B C turn tail =>
    simp only [List.head?_cons,Option.some.injEq] at start
    subst e
    obtain ⟨q,atQ,rule⟩ := turn.from_node () (.inl ()) rfl
    obtain ⟨rfl,contexts⟩ := rule.lam_context
    subst f
    obtain ⟨eq,zEq,lastCtx⟩ := lambdaUsed_body_to_child n body used tail rfl z finish
    exact ⟨by rw [eq],zEq,contexts.trans lastCtx⟩

theorem lambdaUnused_root_to_child (n : Nat) (body : Term) (unused : ¬free body 0)
    {a b : Context} (z : Boundary body)
    (p : LocalPath (lambdaUnused n body unused) (.inl (.inl ())) (.inr z) a b) :
    p.edges=[.inr (.inl (.inl (.inl ()))),.inl ⟨.inl (),lamBody⟩] ∧ z=.inl () ∧ a=b := by
  have labels := p.labeling
  have start := p.start
  have finish := p.finish
  generalize eq : p.edges=es at labels start finish ⊢
  cases labels with
  | single e c =>
    simp only [List.head?_cons,Option.some.injEq] at start
    subst e
    cases z with
    | inl u => cases finish
    | inr x => cases x with | mk k hk => cases k with
      | zero => exact False.elim (unused hk)
      | succ k => cases finish
  | @cons e f es A B C turn tail =>
    simp only [List.head?_cons,Option.some.injEq] at start
    subst e
    obtain ⟨q,atQ,rule⟩ := turn.from_node (.inl ()) (.inl ()) rfl
    obtain ⟨rfl,contexts⟩ := rule.lam_context
    subst f
    obtain ⟨eq,zEq,lastCtx⟩ := lambdaUnused_body_to_child n body unused tail rfl z finish
    exact ⟨by rw [eq],zEq,contexts.trans lastCtx⟩
end Lamping.AG
