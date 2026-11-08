import Lamping.Lambda.MarkedDevelopmentOrigins
namespace Lamping.Lambda.Labelled
/-- A real original-edge route, restricted to EXACT permitted degrees at
each over/under insertion; every original incidence and direction is retained. -/
inductive SelectedSourceRoute (edges : List SourceEdge) (allowed : Label → Prop) :
    SourcePort → Label → SourcePort → Prop where
  | atom (member : e∈edges) (atomic : e.atom=Label.atom n) :
      SelectedSourceRoute edges allowed e.fromPort (Label.atom n) e.toPort
  | over : SelectedSourceRoute edges allowed start a (.appContext appId) →
      allowed d → SelectedSourceRoute edges allowed (.appFn appId) d (.lamContext lamId) →
      SelectedSourceRoute edges allowed (.lamBody lamId) b finish →
      SelectedSourceRoute edges allowed start ((a.concat d.over).concat b) finish
  | under : SelectedSourceRoute edges allowed start a (.lamBind lamId) →
      allowed d → SelectedSourceRoute edges allowed (.appFn appId) d (.lamContext lamId) →
      SelectedSourceRoute edges allowed (.appArg appId) b finish →
      SelectedSourceRoute edges allowed start ((a.concat d.under).concat b) finish
/-- Original source binder identities are retained independently of compound
current labels. Variable destinations use the real de Bruijn environment. -/
inductive SelectedTermRoutes (edges : List SourceEdge) (allowed : Label → Prop) :
    List Label → SourcePort → LTerm → Prop where
  | var : SelectedSourceRoute edges allowed ctx label (sourceBinder env i) →
      SelectedTermRoutes edges allowed env ctx (.var label i)
  | lam : SelectedSourceRoute edges allowed ctx label (.lamContext origin) →
      SelectedTermRoutes edges allowed (origin::env) (.lamBody origin) body →
      SelectedTermRoutes edges allowed env ctx (.lam label body)
  | app : SelectedSourceRoute edges allowed ctx label (.appContext origin) →
      SelectedTermRoutes edges allowed env (.appFn origin) fn →
      SelectedTermRoutes edges allowed env (.appArg origin) arg →
      SelectedTermRoutes edges allowed env ctx (.app label fn arg)

theorem SelectedSourceRoute.forget (route : SelectedSourceRoute edges allowed start label finish) :
    SourceRoute edges start label finish := by
  induction route with
  | atom member atomic => exact .atom member atomic
  | over _ _ _ _ left middle right => exact .over left middle right
  | under _ _ _ _ left middle right => exact .under left middle right

theorem SelectedTermRoutes.forget (routes : SelectedTermRoutes edges allowed env ctx t) :
    TermRoutes edges env ctx t := by
  induction routes with
  | var route => exact .var route.forget
  | lam route _ ih => exact .lam route.forget ih
  | app route _ _ fn arg => exact .app route.forget fn arg
/-- The source route is actual; exact recursive payload membership supplies
precisely the insertion guards, without changing its ports or selecting edges. -/
theorem SourceRoute.selected (route : SourceRoute edges start label finish)
    (bars : label.BarsFrom allowed) : SelectedSourceRoute edges allowed start label finish := by
  induction route with
  | atom member atomic => exact .atom member atomic
  | over _ _ _ left middle right =>
    obtain ⟨first,rightBars⟩ := (Label.barsFrom_concat _ _ _).mp bars
    obtain ⟨leftBars,degreeBars⟩ := (Label.barsFrom_concat _ _ _).mp first
    exact .over (left leftBars) degreeBars.1 (middle degreeBars.2) (right rightBars)
  | under _ _ _ left middle right =>
    obtain ⟨first,rightBars⟩ := (Label.barsFrom_concat _ _ _).mp bars
    obtain ⟨leftBars,degreeBars⟩ := (Label.barsFrom_concat _ _ _).mp first
    exact .under (left leftBars) degreeBars.1 (middle degreeBars.2) (right rightBars)

theorem TermRoutes.selected (routes : TermRoutes edges env ctx t) (bars : t.BarsFrom allowed) :
    SelectedTermRoutes edges allowed env ctx t := by
  induction routes with
  | var route => exact .var (route.selected bars)
  | lam route _ ih => exact .lam (route.selected bars.1) (ih bars.2)
  | app route _ _ fn arg => exact .app (route.selected bars.1) (fn bars.2.1) (arg bars.2.2)
/-- Restricted syntax-edge ancestors for a real relative development. All
payload guards are derived from original old-name selection and actual labels;
no guarded-history premise, reduct INIT, or graph generatedness is assumed. -/
theorem relative_development_selected_routes (initial : INIT original)
    (relative : Marked.RelativeHistory ps (Marked.mark old original.erase) marked)
    (labels : History ps original target) :
    SelectedTermRoutes (sourceEdges [] .external original) (SelectedDegree original old)
      [] .external target :=
  (labels.generated_source_routes initial).selected
    (relative_development_origin_guards initial relative labels).2
/-- If no insertion degree is permitted, a selected route consists of one
original atomic edge. This is syntax-route geometry, not graph path coverage. -/
theorem SelectedSourceRoute.atomic_of_no_insertions
    (route : SelectedSourceRoute edges allowed start label finish) (none : ∀ degree,¬allowed degree) :
    IsAtomic label := by
  cases route with
  | atom => exact ⟨_,rfl⟩
  | over _ selected _ _ => exact False.elim (none _ selected)
  | under _ selected _ _ => exact False.elim (none _ selected)
/-- Descend the actual current syntax path to expose its redex children,
retaining the exact selected routes and original binder environment. -/
theorem SelectedTermRoutes.redex_children
    (routes : SelectedTermRoutes edges allowed outerEnv outerCtx target)
    (lookup : target.subterm site=some (.app beta (.lam alpha body) argument)) :
    ∃ env ctx appId lamId,
      SelectedSourceRoute edges allowed ctx beta (.appContext appId) ∧
      SelectedSourceRoute edges allowed (.appFn appId) alpha (.lamContext lamId) ∧
      SelectedTermRoutes edges allowed (lamId::env) (.lamBody lamId) body ∧
      SelectedTermRoutes edges allowed env (.appArg appId) argument := by
  induction routes generalizing site with
  | var route => cases site with
    | nil => cases lookup
    | cons step rest => cases step <;> simp [LTerm.subterm] at lookup
  | lam route bodyRoutes ih =>
    cases site with
    | nil => cases lookup
    | cons step rest => cases step with
      | fn | arg => simp [LTerm.subterm] at lookup
      | body => exact ih lookup
  | app route fnRoutes argRoutes fnIH argIH =>
    cases site with
    | nil =>
      cases lookup
      cases fnRoutes with
      | lam functionRoute bodyRoutes => exact ⟨_,_,_,_,route,functionRoute,bodyRoutes,argRoutes⟩
    | cons step rest => cases step with
      | body => simp [LTerm.subterm] at lookup
      | fn => exact fnIH lookup
      | arg => exact argIH lookup
end Lamping.Lambda.Labelled

