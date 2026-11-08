import Lamping.Lamping.FunctionLambdaOccurrences
import Lamping.Lambda.LabelHeadPorts

namespace Lamping.Lambda.Labelled

/-- No over/under route can start at the function port of an original
redex: its first constituent would have to end at an app context or binder,
whereas the unique outgoing original edge ends at this lambda context. -/
theorem SourceRoute.head_function_destination
    {original : LTerm} {p : Path} {env ctx : _} {beta alpha : Label} {body argument : LTerm}
    (atHead : SourceSubterm [] .external original p env ctx (.app beta (.lam alpha body) argument))
    (initial : INIT original)
    {start stamp finish} (route : SourceRoute (sourceEdges [] .external original) start stamp finish)
    (atFunction : start=.appFn beta) : stamp=alpha ∧finish=.lamContext alpha := by
  induction route with
  | atom member atomic =>
    have same := atHead.head_function_edge_unique initial member atFunction
    exact ⟨by simpa only [same] using atomic.symm,by simp only [same]⟩
  | over _left _middle _right leftIH _middleIH _rightIH =>
    have impossible := (leftIH atFunction).2
    cases impossible
  | under _left _middle _right leftIH _middleIH _rightIH =>
    have impossible := (leftIH atFunction).2
    cases impossible

/-- A genuine current function subtree entered from that original function
port is still a lambda with the exact old degree. Current labels elsewhere
may be compound; no INIT is imposed on the current term. -/
theorem TermRoutes.head_function_lambda
    {original : LTerm} {p : Path} {sourceEnv sourceCtx : _} {beta alpha : Label} {body argument : LTerm}
    (atHead : SourceSubterm [] .external original p sourceEnv sourceCtx (.app beta (.lam alpha body) argument))
    (initial : INIT original) {env current}
    (routes : TermRoutes (sourceEdges [] .external original) env (.appFn beta) current) :
    ∃ currentBody,current=.lam alpha currentBody := by
  cases routes with
  | var route =>
    have impossible := (route.head_function_destination atHead initial rfl).2
    unfold sourceBinder at impossible
    split at impossible <;> cases impossible
  | lam route bodyRoutes =>
    have same := (route.head_function_destination atHead initial rfl).1
    exact ⟨_,by rw [same]⟩
  | app route fnRoutes argRoutes =>
    have impossible := (route.head_function_destination atHead initial rfl).2
    cases impossible

/-- The original application's current function child forces exactly the
selected old degree. This supplies the finite direct-argument obstruction
once a real syntax trail has identified that application's original origin. -/
theorem TermRoutes.head_function_degree
    {original : LTerm} {p : Path} {sourceEnv sourceCtx : _} {beta alpha : Label} {body argument : LTerm}
    (atHead : SourceSubterm [] .external original p sourceEnv sourceCtx (.app beta (.lam alpha body) argument))
    (initial : INIT original) {env currentFn stamp currentArg}
    (routes : TermRoutes (sourceEdges [] .external original) env (.appFn beta) currentFn) :
    (LTerm.app stamp currentFn currentArg).degreeAt []=some alpha := by
  obtain ⟨currentBody,shape⟩ := routes.head_function_lambda atHead initial
  rw [shape]
  rfl

/-- Actual current application lookup plus its final original atom identify
the old application ORIGIN. Source routes then force its function lambda,
so the degree at this very occurrence is the original selected alpha. -/
theorem TermRoutes.application_last_atom_degree
    {original : LTerm} {oldPosition : Path} {sourceEnv sourceCtx : _}
    {beta alpha : Label} {body argument : LTerm}
    (atHead : SourceSubterm [] .external original oldPosition sourceEnv sourceCtx
      (.app beta (.lam alpha body) argument)) (initial : INIT original)
    {n : Nat} (betaAtom : beta=Label.atom n)
    {env ctx current} (routes : TermRoutes (sourceEdges [] .external original) env ctx current)
    {p : Path} {stamp fn arg} (lookup : current.subterm p=some (.app stamp fn arg))
    (lastAtom : stamp.lastAtom=some n) : current.degreeAt p=some alpha := by
  induction routes generalizing p with
  | var route =>
    cases p with
    | nil => cases lookup
    | cons step rest => cases step <;> simp [LTerm.subterm] at lookup
  | lam route bodyRoutes ih =>
    cases p with
    | nil => cases lookup
    | cons step rest => cases step with
      | fn | arg => simp [LTerm.subterm] at lookup
      | body => exact ih lookup
  | app route fnRoutes argRoutes fnIH argIH =>
    cases p with
    | nil =>
      cases lookup
      obtain ⟨m,last,origin⟩ := route.app_last_atom
      have same : m=n := Option.some.inj (last.symm.trans lastAtom)
      have originEq := origin.trans ((congrArg Label.atom same).trans betaAtom.symm)
      rw [originEq] at fnRoutes
      exact fnRoutes.head_function_degree atHead initial
    | cons step rest => cases step with
      | body => simp [LTerm.subterm] at lookup
      | fn => exact fnIH lookup
      | arg => exact argIH lookup

/-- A complete old-name development has no current application with the
selected original application's origin, including compound current labels.
The final-atom premise is used only together with actual syntax routes. -/
theorem relative_complete_no_application_origin
    {original target : LTerm} {old : List Path} {ps : List Path} {marked : Marked}
    (initial : INIT original)
    (relative : Marked.RelativeHistory ps (Marked.mark old original.erase) marked)
    (normal : Marked.Normal marked) (labels : History ps original target)
    {oldPosition : Path} {sourceEnv sourceCtx : _} {beta alpha : Label} {body argument : LTerm}
    (atHead : SourceSubterm [] .external original oldPosition sourceEnv sourceCtx
      (.app beta (.lam alpha body) argument))
    (selected : SelectedDegree original old alpha) {n : Nat} (betaAtom : beta=Label.atom n)
    {p : Path} {stamp fn arg} (lookup : target.subterm p=some (.app stamp fn arg))
    (lastAtom : stamp.lastAtom=some n) : False := by
  have routes := (relative_development_selected_routes initial relative labels).forget
  have degree := routes.application_last_atom_degree atHead initial betaAtom lookup lastAtom
  exact relative_complete_no_selected_degree initial relative normal labels degree selected

end Lamping.Lambda.Labelled
