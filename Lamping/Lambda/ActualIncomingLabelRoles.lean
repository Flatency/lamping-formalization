import Lamping.Lambda.LabelBoundaryAtoms
namespace Lamping.Lambda.Labelled

/-- The incoming syntax role, forgetting original node identity. Only the
external/function/argument/body ports arise as TermRoutes input contexts. -/
def SourcePort.incomingStep : SourcePort →Option Step
  | .appFn _ => some .fn
  | .appArg _ => some .arg
  | .lamBody _ => some .body
  | _ => none

private theorem TermRoutes.lookup_incoming_role
    {edges : List SourceEdge} {env : List Label} {ctx : SourcePort} {t current : LTerm} {p : Path}
    (routes : TermRoutes edges env ctx t) (lookup : t.subterm p=some current) :
    ∃innerEnv innerCtx,TermRoutes edges innerEnv innerCtx current ∧
      innerCtx.incomingStep=(if p=[] then ctx.incomingStep else p.getLast?) := by
  induction p generalizing env ctx t with
  | nil =>
    have same : t=current := by simpa only [LTerm.subterm,Option.some.injEq] using lookup
    subst current
    exact ⟨env,ctx,routes,rfl⟩
  | cons s rest ih =>
    cases routes with
    | var route => cases s <;> cases lookup
    | @lam ctx stamp origin innerEnv b route body =>
      cases s with
      | fn => cases lookup
      | arg => cases lookup
      | body =>
        obtain ⟨env',ctx',inside,role⟩ := ih body lookup
        refine ⟨env',ctx',inside,?_⟩
        rw [role]
        cases rest <;> rfl
    | @app ctx stamp origin innerEnv fn arg route fRoutes aRoutes =>
      cases s with
      | body => cases lookup
      | fn =>
        obtain ⟨env',ctx',inside,role⟩ := ih fRoutes lookup
        refine ⟨env',ctx',inside,?_⟩
        rw [role]
        cases rest <;> rfl
      | arg =>
        obtain ⟨env',ctx',inside,role⟩ := ih aRoutes lookup
        refine ⟨env',ctx',inside,?_⟩
        rw [role]
        cases rest <;> rfl

private theorem TermRoutes.incoming_route
    (routes : TermRoutes edges env ctx current) : ∃finish,SourceRoute edges ctx current.label finish := by
  cases routes with
  | var route => exact ⟨_,route⟩
  | lam route body => exact ⟨_,route⟩
  | app route fn arg => exact ⟨_,route⟩

/-- A real current incoming edge is a route over the SAME original edge
list, and its input port carries its literal current final-step role. -/
theorem History.node_incoming_route
    {ps : List Path} {source target current : LTerm} {p : Path}
    (labels : History ps source target) (initial : INIT source)
    (lookup : target.subterm p=some current) :
    ∃ctx finish,SourceRoute (sourceEdges [] .external source) ctx current.label finish ∧
      ctx.incomingStep=p.getLast? := by
  obtain ⟨env,ctx,routes,role⟩ := (labels.generated_source_routes initial).lookup_incoming_role lookup
  obtain ⟨finish,route⟩ := routes.incoming_route
  refine ⟨ctx,finish,route,?_⟩
  rw [role]
  cases p <;> rfl

/-- Equal first atoms force the same ORIGINAL incoming SourcePort, because
initial atomic edges are unique. This never identifies current positions. -/
theorem SourceRoute.start_eq_of_firstAtom
    {source : LTerm} (initial : INIT source)
    (left : SourceRoute (sourceEdges [] .external source) a l finishA)
    (right : SourceRoute (sourceEdges [] .external source) b r finishB)
    (same : l.firstAtom=r.firstAtom) : a=b := by
  obtain ⟨n,e,firstE,memberE,atomE,fromE⟩ := left.first_atom
  obtain ⟨m,f,firstF,memberF,atomF,fromF⟩ := right.first_atom
  have atoms : n=m := Option.some.inj (firstE.symm.trans (same.trans firstF))
  have equal : e=f := sourceEdges_unique initial memberE memberF
    (atomE.trans ((congrArg Label.atom atoms).trans atomF.symm))
  exact fromE.symm.trans ((congrArg SourceEdge.fromPort equal).trans fromF)

/-- Full generated histories retain the current incoming edge role in the
first atomic letter. No uniform OLD or safety premise is required. -/
theorem History.incoming_role_eq_of_firstAtom
    {ps : List Path} {source target left right : LTerm} {p q : Path}
    (labels : History ps source target) (initial : INIT source)
    (atLeft : target.subterm p=some left) (atRight : target.subterm q=some right)
    (same : left.label.firstAtom=right.label.firstAtom) : p.getLast?=q.getLast? := by
  obtain ⟨ctxA,finishA,routeA,roleA⟩ := labels.node_incoming_route initial atLeft
  obtain ⟨ctxB,finishB,routeB,roleB⟩ := labels.node_incoming_route initial atRight
  exact roleA.symm.trans ((congrArg SourcePort.incomingStep
    (routeA.start_eq_of_firstAtom initial routeB same)).trans roleB)

theorem History.incoming_role_eq_of_label
    {ps : List Path} {source target left right : LTerm} {p q : Path}
    (labels : History ps source target) (initial : INIT source)
    (atLeft : target.subterm p=some left) (atRight : target.subterm q=some right)
    (same : left.label=right.label) : p.getLast?=q.getLast? :=
  labels.incoming_role_eq_of_firstAtom initial atLeft atRight (congrArg Label.firstAtom same)

#print axioms History.node_incoming_route
#print axioms SourceRoute.start_eq_of_firstAtom
#print axioms History.incoming_role_eq_of_firstAtom
#print axioms History.incoming_role_eq_of_label
end Lamping.Lambda.Labelled
