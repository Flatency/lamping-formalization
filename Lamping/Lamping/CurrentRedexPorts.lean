import Lamping.Lamping.HistorySelectedPrincipalWord
namespace Lamping.Lambda.Labelled
variable {appStamp degree : Label} {body argument : LTerm}

/-- Actual current syntax locates both routes at the SAME application
origin, including when the current labels are compound. -/
theorem TermRoutes.redex_routes (routes : TermRoutes edges env ctx current)
    (lookup : current.subterm p=some (.app appStamp (.lam degree body) argument)) :
    ∃ localCtx appId lamId,
      SourceRoute edges localCtx appStamp (.appContext appId) ∧
      SourceRoute edges (.appFn appId) degree (.lamContext lamId) := by
  induction p generalizing current env ctx with
  | nil =>
    have here : current.subterm []=some current := by cases current <;> rfl
    have same := Option.some.inj (here.symm.trans lookup)
    cases same
    cases routes with
    | app header fn arg =>
      cases fn with
      | lam function body => exact ⟨_,_,_,header,function⟩
  | cons s p ih =>
    cases routes with
    | var route => cases s <;> simp [LTerm.subterm] at lookup
    | lam route child =>
      cases s with
      | fn | arg => simp [LTerm.subterm] at lookup
      | body => exact ih child lookup
    | app route fn arg =>
      cases s with
      | body => simp [LTerm.subterm] at lookup
      | fn => exact ih fn lookup
      | arg => exact ih arg lookup
end Lamping.Lambda.Labelled
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {original : LTerm} {physical : BetaEdge g}
variable {stamp degree : Labelled.Label} {fn arg body : LTerm}

theorem SyntaxTrailImage.app_finish
    (image : SyntaxTrailImage original root physical env ctx current p (.app stamp fn arg) finish edges) :
    ∃ n,stamp.lastAtom=some n ∧ finish=.appContext (.atom n) := by
  induction p generalizing env ctx current edges with
  | nil =>
    cases image with
    | app route =>
      obtain ⟨n,edge,last,member,atomic,target⟩ := route.last_atom
      exact ⟨n,last,congrArg SourcePort.appContext ((sourceEdges_to_app original member target).symm.trans atomic)⟩
  | cons s p ih =>
    cases image with
    | fn _ child | arg _ child | body _ child => exact ih child

theorem SyntaxTrailImage.lam_finish
    (image : SyntaxTrailImage original root physical env ctx current p (.lam degree body) finish edges) :
    ∃ n,degree.lastAtom=some n ∧ finish=.lamContext (.atom n) := by
  induction p generalizing env ctx current edges with
  | nil =>
    cases image with
    | lam route =>
      obtain ⟨n,last,origin⟩ := route.lambda_origin
      exact ⟨n,last,congrArg SourcePort.lamContext origin⟩
  | cons s p ih =>
    cases image with
    | fn _ child | arg _ child | body _ child => exact ih child

theorem BetaSourcePorts.app_trail_last {beta : BetaEdge g}
    (ports : BetaSourcePorts original root beta appId lamId)
    (initial : INIT original) (matching : Matches g root original.erase)
    (header : SourceRoute (sourceEdges [] .external original) localCtx stamp (.appContext appId))
    (trail : PhysicalSyntaxTrail original root physical env ctx current p (.app stamp fn arg) finish) :
    trail.edges.getLast?=some (g.wire (.inl ⟨beta.app,beta.appCtx⟩)) := by
  obtain ⟨n,last,origin⟩ := header.app_last_atom
  obtain ⟨m,last',finishEq⟩ := trail.image.app_finish
  have same : n=m := Option.some.inj (last.symm.trans last')
  have finishPort : finish=.appContext appId := by rw [finishEq,origin,same]
  have actual := (congrArg (fun port => SourcePortRealizes original g root port trail.toEndpoint) finishPort).mp trail.toRealizes
  have endpoint := actual.unique initial matching ports.appContext
  exact trail.last.trans (congrArg (fun e => some (g.wire e)) endpoint)

theorem BetaSourcePorts.lam_trail_last {beta : BetaEdge g}
    (ports : BetaSourcePorts original root beta appId lamId)
    (initial : INIT original) (matching : Matches g root original.erase)
    (function : SourceRoute (sourceEdges [] .external original) (.appFn appId) degree (.lamContext lamId))
    (trail : PhysicalSyntaxTrail original root physical env ctx current p (.lam degree body) finish) :
    trail.edges.getLast?=some (g.wire beta.ctxEnd) := by
  obtain ⟨n,last,origin⟩ := function.lam_last_atom
  obtain ⟨m,last',finishEq⟩ := trail.image.lam_finish
  have same : n=m := Option.some.inj (last.symm.trans last')
  have finishPort : finish=.lamContext lamId := by rw [finishEq,origin,same]
  have actual := (congrArg (fun port => SourcePortRealizes original g root port trail.toEndpoint) finishPort).mp trail.toRealizes
  have endpoint := actual.unique initial matching ports.lamContext
  exact trail.last.trans (congrArg (fun e => some (g.wire e)) endpoint)
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i : Nat}

/-- One original INIT and the actual development schedules locate each
current redex at the fixed site's six physical ports. Current Matches and
newly initialized labels are not assumed. -/
theorem PathSite.relative_current_redex_ports
    (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
    {root : B} {original : LTerm} (initial : INIT original)
    (matching : Matches site.net root original.erase) :
    ∃ beta : BetaEdge site.net,beta.app=.inr (.inl ()) ∧beta.lam=.inr (.inr ()) ∧
      ∀ {ps p marked current target appStamp degree body argument},
      Marked.RelativeHistory (ps++[p]) (Marked.mark (site.betaSyntaxFiber root original.erase) original.erase) marked →
      History ps original current → StepAt p current target →
      current.subterm p=some (.app appStamp (.lam degree body) argument) →
      ∃ localCtx appId lamId,
        SourceRoute (sourceEdges [] .external original) localCtx appStamp (.appContext appId) ∧
        SourceRoute (sourceEdges [] .external original) (.appFn appId) degree (.lamContext lamId) ∧
        degree=lamId ∧BetaSourcePorts original root beta appId lamId := by
  obtain ⟨beta,app,lam,allPorts⟩ := site.selected_beta_source_ports initial matching
  refine ⟨beta,app,lam,?_⟩
  intro ps p marked current target appStamp degree body argument relative prior next lookup
  obtain ⟨localCtx,appId,lamId,header,function⟩ := (prior.generated_source_routes initial).redex_routes lookup
  have degreeAt : current.degreeAt p=some degree := by
    simp only [LTerm.degreeAt,lookup,Option.bind_some,LTerm.degree]
  have selected := relative_last_selected_degree initial relative prior next degreeAt
  obtain ⟨equal,ports⟩ := allPorts selected function
  exact ⟨localCtx,appId,lamId,header,function,equal,ports⟩
end
end Lamping.AG
