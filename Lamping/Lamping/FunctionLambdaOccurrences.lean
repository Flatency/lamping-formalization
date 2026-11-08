import Lamping.Lamping.LambdaFunctionSink
import Lamping.Lamping.CompleteDegreeExhaustion
import Lamping.Lambda.LabelArgumentBinderScope

namespace Lamping.Lambda.Labelled

private theorem atomic_function_start
    {original : LTerm} (initial : INIT original) {appId alpha : Label}
    (functionEdge : (⟨alpha,.appFn appId,.lamContext alpha⟩ : SourceEdge)∈sourceEdges [] .external original)
    {ctx finish} (route : SourceRoute (sourceEdges [] .external original) ctx alpha finish) :
    ctx=.appFn appId := by
  obtain ⟨n,atomic⟩ := sourceEdges_atomic initial functionEdge
  have alphaAtomic : alpha=Label.atom n := atomic
  have route' : SourceRoute (sourceEdges [] .external original) ctx (Label.atom n) finish := by
    rw [←alphaAtomic]
    exact route
  obtain ⟨e,member,atom,source,_to⟩ := route'.initial_atom_edge initial
  have same := sourceEdges_unique initial member functionEdge (atom.trans alphaAtomic.symm)
  simpa only [same] using source.symm

/-- An occurrence of the original function-lambda label must still be an
actual function child, unless it is the entire term entered at that old
function port. In particular, body and argument children cannot be mistaken
for that occurrence. The source is INIT; the current term need not be. -/
theorem TermRoutes.function_lambda_occurrence
    {original : LTerm} (initial : INIT original) {appId alpha : Label}
    (functionEdge : (⟨alpha,.appFn appId,.lamContext alpha⟩ : SourceEdge)∈sourceEdges [] .external original)
    {env ctx current} (routes : TermRoutes (sourceEdges [] .external original) env ctx current)
    {p : Path} {body : LTerm} (lookup : current.subterm p=some (.lam alpha body)) :
    (p=[] ∧ctx=.appFn appId) ∨∃ parent,p=parent++[.fn] ∧current.degreeAt parent=some alpha := by
  induction routes generalizing p with
  | var route =>
    cases p with
    | nil => cases lookup
    | cons step rest => cases step <;> simp [LTerm.subterm] at lookup
  | lam route bodyRoutes ih =>
    cases p with
    | nil =>
      cases lookup
      exact .inl ⟨rfl,atomic_function_start initial functionEdge route⟩
    | cons step rest =>
      cases step with
      | fn | arg => simp [LTerm.subterm] at lookup
      | body =>
        rcases ih lookup with ⟨_,impossible⟩ | ⟨parent,same,degree⟩
        · cases impossible
        · exact .inr ⟨.body::parent,congrArg (List.cons .body) same,degree⟩
  | app route fnRoutes argRoutes fnIH argIH =>
    cases p with
    | nil => cases lookup
    | cons step rest =>
      cases step with
      | body => simp [LTerm.subterm] at lookup
      | fn =>
        rcases fnIH lookup with ⟨empty,_ctx⟩ | ⟨parent,same,degree⟩
        · subst rest
          simp only [LTerm.subterm,Option.some.injEq] at lookup
          cases lookup
          exact .inr ⟨[],rfl,rfl⟩
        · exact .inr ⟨.fn::parent,congrArg (List.cons .fn) same,degree⟩
      | arg =>
        rcases argIH lookup with ⟨_,impossible⟩ | ⟨parent,same,degree⟩
        · cases impossible
        · exact .inr ⟨.arg::parent,congrArg (List.cons .arg) same,degree⟩

/-- Completion removes every occurrence of a selected original function
lambda. The exact original edge and selected old degree are retained;
this does not assert that the completed term is beta-normal. -/
theorem relative_complete_no_function_lambda
    {original target : LTerm} {old : List Path} {ps : List Path} {marked : Marked}
    (initial : INIT original)
    (relative : Marked.RelativeHistory ps (Marked.mark old original.erase) marked)
    (normal : Marked.Normal marked) (labels : History ps original target)
    {appId alpha : Label}
    (functionEdge : (⟨alpha,.appFn appId,.lamContext alpha⟩ : SourceEdge)∈sourceEdges [] .external original)
    (selected : SelectedDegree original old alpha)
    {p : Path} {body : LTerm} (lookup : target.subterm p=some (.lam alpha body)) : False := by
  have routes := (relative_development_selected_routes initial relative labels).forget
  rcases routes.function_lambda_occurrence initial functionEdge lookup with ⟨_,impossible⟩ | ⟨parent,_,degree⟩
  · cases impossible
  · exact relative_complete_no_selected_degree initial relative normal labels degree selected

end Lamping.Lambda.Labelled
