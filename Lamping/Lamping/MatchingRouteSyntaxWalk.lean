import Lamping.Lamping.MatchingSelectedRouteWalk
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
/-- The three real syntax-child transitions between original source ports. -/
inductive SourceSyntaxStep : SourcePort → SourcePort → Step → Prop where
  | fn : SourceSyntaxStep (.appContext origin) (.appFn origin) .fn
  | arg : SourceSyntaxStep (.appContext origin) (.appArg origin) .arg
  | body : SourceSyntaxStep (.lamContext origin) (.lamBody origin) .body
private theorem child_forward {kind : Kind} {ctx out : Port kind}
    (roles : SyntaxChildPorts kind ctx out step) : ForwardPorts kind ctx out := by
  cases roles
  · exact ⟨rfl,Or.inl rfl⟩
  · exact ⟨rfl,Or.inr rfl⟩
  · exact ⟨rfl,rfl⟩
private theorem app_context_role {kind : Kind} {ctx out : Port kind}
    (roles : SyntaxChildPorts kind ctx out step) (app : step=.fn ∨ step=.arg) :
    kind=.op .app ∧ HEq ctx appCtx := by
  cases roles
  · exact ⟨rfl,HEq.rfl⟩
  · exact ⟨rfl,HEq.rfl⟩
  · rcases app with impossible | impossible <;> cases impossible
private theorem lam_context_role {kind : Kind} {ctx out : Port kind}
    (roles : SyntaxChildPorts kind ctx out .body) :
    kind=.op .lam ∧ HEq ctx (Sum.inl () : Port (.op .lam)) := by
  cases roles
  exact ⟨rfl,HEq.rfl⟩
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {original : LTerm}
/-- The adjacent physical ports come from the same original occurrence,
not from choosing two nodes with the same kind or origin label. -/
theorem SourceSyntaxStep.direction (step : SourceSyntaxStep fromPort toPort s)
    (initial : INIT original) (matching : Matches g root original.erase)
    (left : SourcePortRealizes original g root fromPort e)
    (right : SourcePortRealizes original g root toPort f) : ExpandedDirection g e f := by
  cases step with
  | fn =>
    cases right with
    | departure lookup role parent word roles finish =>
      cases role
      obtain ⟨shape,context⟩ := app_context_role roles (Or.inl rfl)
      have same := left.unique initial matching (.appContext lookup parent word shape context finish)
      rw [same]
      exact .node _ _ _ (child_forward roles)
  | arg =>
    cases right with
    | departure lookup role parent word roles finish =>
      cases role
      obtain ⟨shape,context⟩ := app_context_role roles (Or.inr rfl)
      have same := left.unique initial matching (.appContext lookup parent word shape context finish)
      rw [same]
      exact .node _ _ _ (child_forward roles)
  | body =>
    cases right with
    | departure lookup role parent word roles finish =>
      cases role
      obtain ⟨shape,context⟩ := lam_context_role roles
      have same := left.unique initial matching (.lamContext lookup parent word shape context finish)
      rw [same]
      exact .node _ _ _ (child_forward roles)
/-- The final physical atom comes from an actual old edge, retaining its
original terminal port even after nested bar concatenations. -/
theorem SourceRouteImage.last_atom {beta : BetaEdge g}
    (image : SourceRouteImage original root beta start stamp finish edges) :
    ∃ n edge,stamp.lastAtom=some n ∧ edge∈sourceEdges [] .external original ∧
      edge.atom=Labelled.Label.atom n ∧ edge.toPort=finish := by
  induction image with
  | atom fragment atomic => exact ⟨_,_,rfl,fragment.source_member,atomic,rfl⟩
  | over ports left right leftIH rightIH | under ports left right leftIH rightIH =>
    obtain ⟨n,edge,last,member,atomic,target⟩ := rightIH
    exact ⟨n,edge,by simpa only [Labelled.Label.lastAtom_concat] using last,member,atomic,target⟩
theorem SourceRouteImage.lambda_origin {beta : BetaEdge g}
    (image : SourceRouteImage original root beta start stamp (.lamContext origin) edges) :
    ∃ n,stamp.lastAtom=some n ∧ origin=Labelled.Label.atom n := by
  obtain ⟨n,edge,last,member,atomic,target⟩ := image.last_atom
  exact ⟨n,last,(sourceEdges_to_lam original member target).symm.trans atomic⟩
/-- Literal trail through the actual current syntax. The lambda constructor
pushes the ORIGINAL binder identity, so variable destinations use the real
de Bruijn environment even when current labels have become compound. -/
inductive SyntaxTrailImage (original : LTerm) (root : B) (beta : BetaEdge g) :
    List Labelled.Label → SourcePort → LTerm → Path → LTerm → SourcePort → List (Endpoint g) → Prop where
  | var (image : SourceRouteImage original root beta ctx stamp (sourceBinder env index) xs) :
      SyntaxTrailImage original root beta env ctx (.var stamp index) [] (.var stamp index) (sourceBinder env index) xs
  | lam (image : SourceRouteImage original root beta ctx stamp (.lamContext origin) xs) :
      SyntaxTrailImage original root beta env ctx (.lam stamp body) [] (.lam stamp body) (.lamContext origin) xs
  | app (image : SourceRouteImage original root beta ctx stamp (.appContext origin) xs) :
      SyntaxTrailImage original root beta env ctx (.app stamp fn arg) [] (.app stamp fn arg) (.appContext origin) xs
  | fn (first : SourceRouteImage original root beta ctx stamp (.appContext origin) xs)
      (child : SyntaxTrailImage original root beta env (.appFn origin) fn p sub finish ys) :
      SyntaxTrailImage original root beta env ctx (.app stamp fn arg) (.fn::p) sub finish (xs++ys)
  | arg (first : SourceRouteImage original root beta ctx stamp (.appContext origin) xs)
      (child : SyntaxTrailImage original root beta env (.appArg origin) arg p sub finish ys) :
      SyntaxTrailImage original root beta env ctx (.app stamp fn arg) (.arg::p) sub finish (xs++ys)
  | body (first : SourceRouteImage original root beta ctx stamp (.lamContext origin) xs)
      (child : SyntaxTrailImage original root beta (origin::env) (.lamBody origin) body p sub finish ys) :
      SyntaxTrailImage original root beta env ctx (.lam stamp body) (.body::p) sub finish (xs++ys)
/-- Directional physical interpretation of one actual current syntax path.
This is a root access only after labellability is proved separately. -/
structure PhysicalSyntaxTrail (original : LTerm) (root : B) (beta : BetaEdge g)
    (env : List Labelled.Label) (ctx : SourcePort) (target : LTerm) (p : Path) (sub : LTerm) (finish : SourcePort) where
  edges : List (Endpoint g)
  fromEndpoint : Endpoint g
  toEndpoint : Endpoint g
  fromRealizes : SourcePortRealizes original g root ctx fromEndpoint
  toRealizes : SourcePortRealizes original g root finish toEndpoint
  head : edges.head?=some fromEndpoint
  last : edges.getLast?=some (g.wire toEndpoint)
  forward : ExpandedForward g edges
  image : SyntaxTrailImage original root beta env ctx target p sub finish edges

theorem SyntaxTrailImage.lookup {beta : BetaEdge g}
    (image : SyntaxTrailImage original root beta env ctx target p sub finish edges) : target.subterm p=some sub := by
  induction image with
  | var | lam | app => rfl
  | fn _ _ ih | arg _ _ ih | body _ _ ih => exact ih

theorem PhysicalSyntaxTrail.lookup {beta : BetaEdge g}
    (trail : PhysicalSyntaxTrail original root beta env ctx target p sub finish) : target.subterm p=some sub :=
  trail.image.lookup
theorem PhysicalSyntaxTrail.rooted {beta : BetaEdge g}
    (trail : PhysicalSyntaxTrail original root beta env .external target p sub finish) :
    trail.edges.head?=some (.inr (.inl root)) := by
  have realizes := trail.fromRealizes
  generalize equal : trail.fromEndpoint=endpoint
  rw [equal] at realizes
  cases realizes with
  | external => exact trail.head.trans (congrArg some equal)
  | departure _ role => cases role

private theorem prepend_trail {beta : BetaEdge g} {stamp : Labelled.Label}
    (initial : INIT original) (matching : Matches g root original.erase)
    (left : PhysicalSourceWalk original root beta ctx stamp mid)
    (right : PhysicalSyntaxTrail original root beta childEnv childCtx child p sub finish)
    (step : SourceSyntaxStep mid childCtx s)
    (image : SyntaxTrailImage original root beta env ctx target whole sub finish (left.edges++right.edges)) :
    Nonempty (PhysicalSyntaxTrail original root beta env ctx target whole sub finish) := by
  have direction := step.direction initial matching left.toRealizes right.fromRealizes
  have forward := left.forward.splice left.last right.forward right.head (by
    simpa only [g.wire.involutive] using direction)
  exact ⟨{
    edges := left.edges++right.edges,fromEndpoint := left.fromEndpoint,toEndpoint := right.toEndpoint
    fromRealizes := left.fromRealizes,toRealizes := right.toRealizes
    head := by simp only [List.head?_append,left.head,Option.some_or]
    last := by simp only [List.getLast?_append,right.last,Option.some_or]
    forward := forward,image := image }⟩
end
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {original : LTerm} {beta : BetaEdge g}
private theorem here_trail
    (walk : PhysicalSourceWalk original root beta ctx stamp finish)
    (image : SyntaxTrailImage original root beta env ctx target [] target finish walk.edges) :
    Nonempty (PhysicalSyntaxTrail original root beta env ctx target [] target finish) :=
  ⟨{edges := walk.edges,fromEndpoint := walk.fromEndpoint,toEndpoint := walk.toEndpoint
    fromRealizes := walk.fromRealizes,toRealizes := walk.toRealizes,head := walk.head,last := walk.last
    forward := walk.forward,image := image}⟩
private theorem build_syntax_trail
    (initial : INIT original) (matching : Matches g root original.erase)
    (allWalks : ∀ {start stamp finish},SelectedSourceRoute (sourceEdges [] .external original) allowed start stamp finish →
      Nonempty (PhysicalSourceWalk original root beta start stamp finish))
    (routes : SelectedTermRoutes (sourceEdges [] .external original) allowed env ctx target)
    (lookup : target.subterm p=some sub) :
    ∃ finish,Nonempty (PhysicalSyntaxTrail original root beta env ctx target p sub finish) := by
  induction routes generalizing p sub with
  | var route =>
    cases p with
    | nil =>
      cases lookup
      obtain ⟨walk⟩ := allWalks route
      exact ⟨_,here_trail walk (.var walk.image)⟩
    | cons step rest => cases step <;> simp [LTerm.subterm] at lookup
  | lam route body ih =>
    cases p with
    | nil =>
      cases lookup
      obtain ⟨walk⟩ := allWalks route
      exact ⟨_,here_trail walk (.lam walk.image)⟩
    | cons step rest =>
      cases step with
      | fn | arg => simp [LTerm.subterm] at lookup
      | body =>
        obtain ⟨finish,child⟩ := ih lookup
        obtain ⟨child⟩ := child
        obtain ⟨walk⟩ := allWalks route
        exact ⟨finish,prepend_trail initial matching walk child .body (.body walk.image child.image)⟩
  | app route fn arg fnIH argIH =>
    cases p with
    | nil =>
      cases lookup
      obtain ⟨walk⟩ := allWalks route
      exact ⟨_,here_trail walk (.app walk.image)⟩
    | cons step rest =>
      cases step with
      | body => simp [LTerm.subterm] at lookup
      | fn =>
        obtain ⟨finish,child⟩ := fnIH lookup
        obtain ⟨child⟩ := child
        obtain ⟨walk⟩ := allWalks route
        exact ⟨finish,prepend_trail initial matching walk child .fn (.fn walk.image child.image)⟩
      | arg =>
        obtain ⟨finish,child⟩ := argIH lookup
        obtain ⟨child⟩ := child
        obtain ⟨walk⟩ := allWalks route
        exact ⟨finish,prepend_trail initial matching walk child .arg (.arg walk.image child.image)⟩
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i : Nat}
/-- Real current-term occurrence paths are physically concatenated from the
same fixed site's selected edge images. Every syntax step is an actual
proper-node passage; every terminal variable retains its original env. -/
theorem PathSite.selected_term_syntax_trail
    (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
    {root : B} {original target : LTerm} (initial : INIT original) (closed : Closed original.erase)
    (matching : Matches site.net root original.erase)
    (routes : SelectedTermRoutes (sourceEdges [] .external original)
      (SelectedDegree original (site.betaSyntaxFiber root original.erase)) [] .external target) :
    ∃ beta : BetaEdge site.net,beta.app=.inr (.inl ()) ∧ beta.lam=.inr (.inr ()) ∧
      ∀ {p sub},target.subterm p=some sub →
      ∃ finish,Nonempty (PhysicalSyntaxTrail original root beta [] .external target p sub finish) := by
  obtain ⟨beta,app,lam,allWalks⟩ := site.selected_source_route_walk initial closed matching
  exact ⟨beta,app,lam,fun lookup => build_syntax_trail initial matching allWalks routes lookup⟩
/-- The public actual-history interface derives all selected route premises
from P04 relativity and one original INIT labeling. No target graph access,
Generated certificate, or whole-path label assignment is an input. -/
theorem PathSite.relative_development_syntax_trail
    (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
    {root : B} {original target : LTerm} (initial : INIT original) (closed : Closed original.erase)
    (matching : Matches site.net root original.erase)
    (relative : Marked.RelativeHistory ps (Marked.mark (site.betaSyntaxFiber root original.erase) original.erase) marked)
    (labels : History ps original target) :
    ∃ beta : BetaEdge site.net,beta.app=.inr (.inl ()) ∧ beta.lam=.inr (.inr ()) ∧
      ∀ {p sub},target.subterm p=some sub →
      ∃ finish,Nonempty (PhysicalSyntaxTrail original root beta [] .external target p sub finish) :=
  site.selected_term_syntax_trail initial closed matching (relative_development_selected_routes initial relative labels)
end
end Lamping.AG





