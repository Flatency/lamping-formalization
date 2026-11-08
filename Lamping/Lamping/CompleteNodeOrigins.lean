import Lamping.Lamping.FunctionPortRoutes

namespace Lamping.Lambda.Labelled

/-- Actual syntax routes identify the origin of this current lambda by
its final atom. For an original function lambda the sink theorem then
forces its WHOLE current label to remain that original atom. -/
theorem TermRoutes.function_lambda_label
    {original : LTerm} (initial : INIT original) {appId alpha : Label}
    (functionEdge : (⟨alpha,.appFn appId,.lamContext alpha⟩ : SourceEdge)∈sourceEdges [] .external original)
    {n : Nat} (alphaAtom : alpha=Label.atom n)
    {env ctx current} (routes : TermRoutes (sourceEdges [] .external original) env ctx current)
    {p : Path} {stamp body} (lookup : current.subterm p=some (.lam stamp body))
    (lastAtom : stamp.lastAtom=some n) : stamp=alpha := by
  induction routes generalizing p with
  | var route =>
    cases p with
    | nil => cases lookup
    | cons step rest => cases step <;> simp [LTerm.subterm] at lookup
  | lam route bodyRoutes ih =>
    cases p with
    | nil =>
      cases lookup
      obtain ⟨m,last,origin⟩ := route.lam_last_atom
      have same : m=n := Option.some.inj (last.symm.trans lastAtom)
      have originEq := origin.trans ((congrArg Label.atom same).trans alphaAtom.symm)
      exact (route.function_lambda_sink initial functionEdge (congrArg SourcePort.lamContext originEq)).2
    | cons step rest => cases step with
      | fn | arg => simp [LTerm.subterm] at lookup
      | body => exact ih lookup
  | app route fnRoutes argRoutes fnIH argIH =>
    cases p with
    | nil => cases lookup
    | cons step rest => cases step with
      | body => simp [LTerm.subterm] at lookup
      | fn => exact fnIH lookup
      | arg => exact argIH lookup

/-- Completion excludes the selected lambda ORIGIN, even when a proposed
current label is compound. The old function edge is an essential premise. -/
theorem relative_complete_no_lambda_origin
    {original target : LTerm} {old : List Path} {ps : List Path} {marked : Marked}
    (initial : INIT original)
    (relative : Marked.RelativeHistory ps (Marked.mark old original.erase) marked)
    (normal : Marked.Normal marked) (labels : History ps original target)
    {appId alpha : Label}
    (functionEdge : (⟨alpha,.appFn appId,.lamContext alpha⟩ : SourceEdge)∈sourceEdges [] .external original)
    (selected : SelectedDegree original old alpha) {n : Nat} (alphaAtom : alpha=Label.atom n)
    {p : Path} {stamp body} (lookup : target.subterm p=some (.lam stamp body))
    (lastAtom : stamp.lastAtom=some n) : False := by
  have routes := (relative_development_selected_routes initial relative labels).forget
  have same := routes.function_lambda_label initial functionEdge alphaAtom lookup lastAtom
  rw [same] at lookup
  exact relative_complete_no_function_lambda initial relative normal labels functionEdge selected lookup

end Lamping.Lambda.Labelled
