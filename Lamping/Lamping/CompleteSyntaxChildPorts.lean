import Lamping.Lamping.CompleteAppTrailExclusion
import Lamping.Lamping.CompletePhysicalLambdaOrigins

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

/-- Current compound labels and original node origins are kept separate.
This records only the three syntactic child shapes. -/
inductive CurrentSyntaxChild : LTerm → SourcePort → SourcePort → Step → Prop where
  | function : CurrentSyntaxChild (.app stamp fn arg) (.appContext origin) (.appFn origin) .fn
  | argument : CurrentSyntaxChild (.app stamp fn arg) (.appContext origin) (.appArg origin) .arg
  | body : CurrentSyntaxChild (.lam stamp body) (.lamContext origin) (.lamBody origin) .body

private theorem function_context {kind : Kind} {ctx out : Port kind}
    (roles : SyntaxChildPorts kind ctx out .fn) : kind=.op .app ∧HEq ctx appCtx := by
  cases roles
  exact ⟨rfl,HEq.rfl⟩

private theorem argument_context {kind : Kind} {ctx out : Port kind}
    (roles : SyntaxChildPorts kind ctx out .arg) : kind=.op .app ∧HEq ctx appCtx := by
  cases roles
  exact ⟨rfl,HEq.rfl⟩

private theorem body_context {kind : Kind} {ctx out : Port kind}
    (roles : SyntaxChildPorts kind ctx out .body) :
    kind=.op .lam ∧HEq ctx (Sum.inl () : Port (.op .lam)) := by
  cases roles
  exact ⟨rfl,HEq.rfl⟩

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {original : LTerm}

theorem SourceSyntaxStep.actual_ports
    (step : SourceSyntaxStep fromPort toPort s) (initial : INIT original)
    (matching : Matches g root original.erase)
    (left : SourcePortRealizes original g root fromPort e)
    (right : SourcePortRealizes original g root toPort f) :
    ∃ (node : N) (ctx out : Port (g.label node).sort),
      SyntaxChildPorts (g.label node).sort ctx out s ∧
      e=.inl ⟨node,ctx⟩ ∧f=.inl ⟨node,out⟩ := by
  cases step with
  | fn =>
    cases right with
    | departure lookup role parent word roles finish =>
      cases role
      have metadata := function_context roles
      exact ⟨_,_,_,roles,left.unique initial matching (.appContext lookup parent word metadata.1 metadata.2 finish),rfl⟩
  | arg =>
    cases right with
    | departure lookup role parent word roles finish =>
      cases role
      have metadata := argument_context roles
      exact ⟨_,_,_,roles,left.unique initial matching (.appContext lookup parent word metadata.1 metadata.2 finish),rfl⟩
  | body =>
    cases right with
    | departure lookup role parent word roles finish =>
      cases role
      have metadata := body_context roles
      exact ⟨_,_,_,roles,left.unique initial matching (.lamContext lookup parent word metadata.1 metadata.2 finish),rfl⟩

private theorem app_metadata {node : N} {ctx : Port (g.label node).sort} {origin}
    (actual : SourcePortRealizes original g root (.appContext origin) (.inl ⟨node,ctx⟩)) :
    (g.label node).sort=.op .app ∧HEq ctx appCtx := by
  cases actual with
  | departure _ role => cases role
  | appContext _ _ _ sort role => exact ⟨sort,role⟩

private theorem lam_metadata {node : N} {ctx : Port (g.label node).sort} {origin}
    (actual : SourcePortRealizes original g root (.lamContext origin) (.inl ⟨node,ctx⟩)) :
    (g.label node).sort=.op .lam ∧HEq ctx (Sum.inl () : Port (.op .lam)) := by
  cases actual with
  | departure _ role => cases role
  | lamContext _ _ _ sort role => exact ⟨sort,role⟩
end

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
variable {root : B} {original target : LTerm} {ps : List Path} {marked : Marked}

/-- An actual current application's occurrence-bearing source context is
retained after completing this physical fiber. -/
theorem PathSite.complete_app_context_kept
    (initial : INIT original) (matching : Matches site.net root original.erase)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (relative : Marked.RelativeHistory ps (Marked.mark (site.betaSyntaxFiber root original.erase) original.erase) marked)
    (normal : Marked.Normal marked) (labels : History ps original target)
    {beta : BetaEdge site.net} {start stamp origin edges p fn arg}
    (image : SourceRouteImage original root beta start stamp (.appContext origin) edges)
    (lookup : target.subterm p=some (.app stamp fn arg))
    {node} {ctx : Port (site.net.label node).sort}
    (actual : SourcePortRealizes original site.net root (.appContext origin) (.inl ⟨node,ctx⟩)) :
    ∃ k : K,node=.inl k := by
  obtain ⟨sort,role⟩ := app_metadata actual
  obtain ⟨n,edge,last,member,atomic,finish⟩ := image.last_atom
  have originAtom := (sourceEdges_to_app original member finish).symm.trans atomic
  have sameOrigin : stamp.lastAtom=origin.lastAtom := by rw [originAtom]; exact last
  cases node with
  | inl k => exact ⟨k,rfl⟩
  | inr active => cases active with
    | inr marker => cases marker; cases sort
    | inl marker =>
      cases marker
      have port : ctx=appCtx := eq_of_heq role
      subst ctx
      obtain ⟨physical,atApp,atLam,_fun,_ctx,_arg,_bind,_body,atContext⟩ := site.betaEdge_identified
      have actual' : SourcePortRealizes original site.net root (.appContext origin)
          (.inl ⟨physical.app,physical.appCtx⟩) := by rw [atContext]; exact actual
      have relative' : Marked.RelativeHistory ps
          (Marked.mark (physicalBetaFiberPaths site.net root original.erase physical.app physical.lam) original.erase) marked := by
        simpa only [atApp,atLam,PathSite.betaSyntaxFiber] using relative
      exact False.elim (physical.complete_no_realized_app_origin initial matching flow positive relative' normal labels actual' lookup sameOrigin)

/-- The corresponding retained-context statement for a current lambda;
compound current labels do not change its original source provenance. -/
theorem PathSite.complete_lambda_context_kept
    (initial : INIT original) (matching : Matches site.net root original.erase)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (relative : Marked.RelativeHistory ps (Marked.mark (site.betaSyntaxFiber root original.erase) original.erase) marked)
    (normal : Marked.Normal marked) (labels : History ps original target)
    {beta : BetaEdge site.net} {start stamp origin edges p body}
    (image : SourceRouteImage original root beta start stamp (.lamContext origin) edges)
    (lookup : target.subterm p=some (.lam stamp body))
    {node} {ctx : Port (site.net.label node).sort}
    (actual : SourcePortRealizes original site.net root (.lamContext origin) (.inl ⟨node,ctx⟩)) :
    ∃ k : K,node=.inl k := by
  obtain ⟨sort,role⟩ := lam_metadata actual
  obtain ⟨n,last,originAtom⟩ := image.lambda_origin
  have sameOrigin : stamp.lastAtom=origin.lastAtom := by rw [originAtom]; exact last
  cases node with
  | inl k => exact ⟨k,rfl⟩
  | inr active => cases active with
    | inl marker => cases marker; cases sort
    | inr marker =>
      cases marker
      have port : ctx=(Sum.inl () : Port (.op .lam)) := eq_of_heq role
      subst ctx
      exact False.elim (site.complete_no_realized_lambda_origin initial matching flow positive relative normal labels actual lookup sameOrigin)

/-- A genuine current syntax child is a turn at a retained proper node.
The selected app and lambda are excluded from ACTUAL source provenance
and completion, not by assuming a kept-node diagram from the caller. -/
theorem CurrentSyntaxChild.complete_kept_ports
    (initial : INIT original) (matching : Matches site.net root original.erase)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (relative : Marked.RelativeHistory ps (Marked.mark (site.betaSyntaxFiber root original.erase) original.erase) marked)
    (normal : Marked.Normal marked) (labels : History ps original target)
    {beta : BetaEdge site.net} {head : LTerm} {fromPort toPort s start edges p e f}
    (shape : CurrentSyntaxChild head fromPort toPort s)
    (lookup : target.subterm p=some head)
    (image : SourceRouteImage original root beta start head.label fromPort edges)
    (left : SourcePortRealizes original site.net root fromPort e)
    (right : SourcePortRealizes original site.net root toPort f) :
    ∃ (node : K) (ctx out : Port (kept node).sort),
      SyntaxChildPorts (kept node).sort ctx out s ∧
      e=.inl ⟨.inl node,ctx⟩ ∧f=.inl ⟨.inl node,out⟩ := by
  have step : SourceSyntaxStep fromPort toPort s := by cases shape <;> constructor
  obtain ⟨node,ctx,out,roles,atLeft,atRight⟩ := step.actual_ports initial matching left right
  have atNode : SourcePortRealizes original site.net root fromPort (.inl ⟨node,ctx⟩) := by rw [←atLeft]; exact left
  have keptNode : ∃ k : K,node=.inl k := by
    cases shape with
    | function | argument => exact site.complete_app_context_kept initial matching flow positive relative normal labels image lookup atNode
    | body => exact site.complete_lambda_context_kept initial matching flow positive relative normal labels image lookup atNode
  obtain ⟨keptNode,same⟩ := keptNode
  subst node
  exact ⟨keptNode,ctx,out,roles,atLeft,atRight⟩
end
end Lamping.AG
