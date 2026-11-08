import Lamping.Lambda.LabelEndpoints
namespace Lamping.Lambda.Labelled

/-- Original-edge routes with the exact source port constraints of AG6.2.5.
The over/under constructors encode different turns at application and binder. -/
inductive SourceRoute (edges : List SourceEdge) : SourcePort → Label → SourcePort → Prop where
  | atom (member : e∈edges) (atomic : e.atom=Label.atom n) :
      SourceRoute edges e.fromPort (Label.atom n) e.toPort
  | over : SourceRoute edges start a (.appContext appId) →
      SourceRoute edges (.appFn appId) d (.lamContext lamId) →
      SourceRoute edges (.lamBody lamId) b finish →
      SourceRoute edges start ((a.concat d.over).concat b) finish
  | under : SourceRoute edges start a (.lamBind lamId) →
      SourceRoute edges (.appFn appId) d (.lamContext lamId) →
      SourceRoute edges (.appArg appId) b finish →
      SourceRoute edges start ((a.concat d.under).concat b) finish

/-- Current node identities and binder identities are original source labels;
the compound label describes the route to that original principal port. -/
inductive TermRoutes (edges : List SourceEdge) : List Label → SourcePort → LTerm → Prop where
  | var : SourceRoute edges ctx l (sourceBinder env i) → TermRoutes edges env ctx (.var l i)
  | lam : SourceRoute edges ctx l (.lamContext origin) →
      TermRoutes edges (origin::env) (.lamBody origin) b → TermRoutes edges env ctx (.lam l b)
  | app : SourceRoute edges ctx l (.appContext origin) →
      TermRoutes edges env (.appFn origin) f → TermRoutes edges env (.appArg origin) a →
      TermRoutes edges env ctx (.app l f a)

private theorem sourceEdge_member (t : LTerm) : sourceEdge env ctx t∈sourceEdges env ctx t := by
  cases t <;> exact List.mem_cons_self

private theorem sourceEdge_route (t : LTerm) (atomic : IsAtomic t.label)
    (member : sourceEdge env ctx t∈edges) :
    SourceRoute edges ctx t.label (sourceEdge env ctx t).toPort := by
  obtain ⟨n,hn⟩ := atomic
  have h := SourceRoute.atom member (show (sourceEdge env ctx t).atom=Label.atom n by cases t <;> exact hn)
  cases t <;> simpa only [LTerm.label,sourceEdge,← hn] using h

theorem TermRoutes.from_source (t : LTerm) (atoms : ∀ l∈t.labels,IsAtomic l)
    (included : ∀ e∈sourceEdges env ctx t,e∈edges) : TermRoutes edges env ctx t := by
  induction t generalizing env ctx with
  | var l i => exact .var (sourceEdge_route _ (atoms _ (label_mem_labels _)) (included _ (sourceEdge_member _)))
  | lam l b hb =>
    apply TermRoutes.lam (sourceEdge_route _ (atoms _ (label_mem_labels _)) (included _ (sourceEdge_member _)))
    apply hb
    · intro x hx; exact atoms x (List.mem_cons_of_mem _ hx)
    · intro e he; exact included e (List.mem_cons_of_mem _ he)
  | app l f a hf ha =>
    apply TermRoutes.app (sourceEdge_route _ (atoms _ (label_mem_labels _)) (included _ (sourceEdge_member _)))
    · apply hf
      · intro x hx; exact atoms x (List.mem_cons_of_mem _ (List.mem_append_left _ hx))
      · intro e he; exact included e (List.mem_cons_of_mem _ (List.mem_append_left _ he))
    · apply ha
      · intro x hx; exact atoms x (List.mem_cons_of_mem _ (List.mem_append_right _ hx))
      · intro e he; exact included e (List.mem_cons_of_mem _ (List.mem_append_right _ he))

theorem INIT.source_routes (hi : INIT t) : TermRoutes (sourceEdges [] .external t) [] .external t :=
  TermRoutes.from_source t hi.1 (fun _ he => he)

namespace TermRoutes
theorem rename (h : TermRoutes edges env ctx t) (rho : Nat → Nat)
    (binders : ∀ i, sourceBinder env i=sourceBinder env' (rho i)) :
    TermRoutes edges env' ctx (t.rename rho) := by
  induction h generalizing env' rho with
  | var route => exact .var (by simpa only [binders] using route)
  | lam route body ih =>
    apply TermRoutes.lam route
    apply ih
    intro i
    cases i with
    | zero => rfl
    | succ i => simpa only [Lambda.liftRen,sourceBinder_succ] using binders i
  | app route fn arg hf ha => exact .app route (hf _ binders) (ha _ binders)

theorem prepend_over (h : TermRoutes edges env (.lamBody lamId) t)
    (headRoute : SourceRoute edges ctx beta (.appContext appId))
    (degree : SourceRoute edges (.appFn appId) alpha (.lamContext lamId)) :
    TermRoutes edges env ctx (t.prepend (beta.concat alpha.over)) := by
  cases h with
  | var route => exact .var (.over headRoute degree route)
  | lam route body => exact .lam (.over headRoute degree route) body
  | app route fn arg => exact .app (.over headRoute degree route) fn arg

theorem prepend_under (h : TermRoutes edges env (.appArg appId) t)
    (varRoute : SourceRoute edges ctx epsilon (.lamBind lamId))
    (degree : SourceRoute edges (.appFn appId) alpha (.lamContext lamId)) :
    TermRoutes edges env ctx (t.prepend (epsilon.concat alpha.under)) := by
  cases h with
  | var route => exact .var (.under varRoute degree route)
  | lam route body => exact .lam (.under varRoute degree route) body
  | app route fn arg => exact .app (.under varRoute degree route) fn arg

/-- A variable substitution connects through the actual source binder port.
The underlined degree is a route from its application's function port to that binder. -/
def Value (edges : List SourceEdge) (env' : List Label) (binder : SourcePort) : LTerm.SubValue → Prop
  | .keep j => binder=sourceBinder env' j
  | .put t => ∃ (alpha appId lamId : Label) (a : LTerm),
      binder=.lamBind lamId ∧ SourceRoute edges (.appFn appId) alpha (.lamContext lamId) ∧
      TermRoutes edges env' (.appArg appId) a ∧ t=a.prepend alpha.under

theorem lift_values (h : ∀ i, Value edges env' (sourceBinder env i) (sigma i)) (origin : Label) :
    ∀ i, Value edges (origin::env') (sourceBinder (origin::env) i) (LTerm.lift sigma i) := by
  intro i
  cases i with
  | zero => rfl
  | succ i =>
    cases hs : sigma i with
    | keep j => simpa only [LTerm.lift,hs,Value,sourceBinder_succ] using h i
    | put t =>
      have hv : Value edges env' (sourceBinder env i) (.put t) := by simpa only [hs] using h i
      obtain ⟨alpha,appId,lamId,a,binder,degree,arg,he⟩ := hv
      simp only [LTerm.lift,hs,Value,sourceBinder_succ]
      refine ⟨alpha,appId,lamId,a.rename Nat.succ,binder,degree,?_,?_⟩
      · apply arg.rename
        intro j; exact (sourceBinder_succ env' origin j).symm
      · rw [he,LTerm.rename_prepend]

theorem subst (h : TermRoutes edges env ctx t)
    (hs : ∀ i, Value edges env' (sourceBinder env i) (sigma i)) :
    TermRoutes edges env' ctx (t.subst sigma) := by
  induction h generalizing env' sigma with
  | @var ctx l env i route =>
    cases hv : sigma i with
    | keep j =>
      have binder : sourceBinder env i=sourceBinder env' j := by simpa only [Value,hv] using hs i
      simpa only [LTerm.subst,hv] using TermRoutes.var (by simpa only [binder] using route)
    | put u =>
      have value : Value edges env' (sourceBinder env i) (.put u) := by simpa only [hv] using hs i
      obtain ⟨alpha,appId,lamId,a,binder,degree,arg,he⟩ := value
      have crossed := arg.prepend_under (by simpa only [binder] using route) degree
      simpa only [LTerm.subst,hv,he,LTerm.prepend_assoc] using crossed
  | lam route body ih => exact .lam route (ih (lift_values hs _))
  | app route fn arg hf ha => exact .app route (hf hs) (ha hs)

theorem contract (source : TermRoutes edges env ctx (.app beta (.lam alpha b) a)) :
    TermRoutes edges env ctx (LTerm.contract beta alpha b a) := by
  cases source with
  | app outer fn arg =>
    cases fn with
    | lam degree body =>
      apply TermRoutes.prepend_over (headRoute := outer) (degree := degree)
      apply body.subst
      intro i
      cases i with
      | zero => exact ⟨_,_,_,a,rfl,degree,arg,rfl⟩
      | succ i => exact sourceBinder_succ _ _ _
end TermRoutes

theorem StepAt.source_routes (h : StepAt p t u) (ht : TermRoutes edges env ctx t) :
    TermRoutes edges env ctx u := by
  induction h generalizing env ctx with
  | root => exact ht.contract
  | fn _ ih => cases ht with | app route fn arg => exact .app route (ih fn) arg
  | arg _ ih => cases ht with | app route fn arg => exact .app route fn (ih arg)
  | body _ ih => cases ht with | lam route body => exact .lam route (ih body)

theorem History.source_routes (h : History ps t u) (ht : TermRoutes edges env ctx t) :
    TermRoutes edges env ctx u := by
  induction h with
  | nil => exact ht
  | cons h _ ih => exact ih (h.source_routes ht)

/-- Full actual beta transport preserves original edge/binder endpoint
geometry; the original source edge list is fixed once at INIT. -/
theorem History.generated_source_routes (h : History ps t u) (hi : INIT t) :
    TermRoutes (sourceEdges [] .external t) [] .external u := h.source_routes hi.source_routes
end Lamping.Lambda.Labelled

