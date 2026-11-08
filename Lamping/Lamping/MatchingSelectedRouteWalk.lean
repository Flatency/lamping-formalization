import Lamping.Lamping.MatchingSelectedRoutePorts
import Lamping.Lamping.LocalTransport
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
private theorem ports_function (actual : Graph.Label signature) (ctx out : Port actual.sort)
    (lab : actual=label .app i) (context : HEq ctx appCtx)
    (departure : HEq out (Sum.inl () : Port (.op .app))) : SyntaxChildPorts actual.sort ctx out .fn := by
  subst actual
  cases eq_of_heq context
  cases eq_of_heq departure
  exact .function
private theorem ports_argument (actual : Graph.Label signature) (ctx out : Port actual.sort)
    (lab : actual=label .app i) (context : HEq ctx appCtx)
    (departure : HEq out appArg) : SyntaxChildPorts actual.sort ctx out .arg := by
  subst actual
  cases eq_of_heq context
  cases eq_of_heq departure
  exact .argument
private theorem ports_body (actual : Graph.Label signature) (ctx out : Port actual.sort)
    (lab : actual=label .lam i) (context : HEq ctx (Sum.inl () : Port (.op .lam)))
    (departure : HEq out lamBody) : SyntaxChildPorts actual.sort ctx out .body := by
  subst actual
  cases eq_of_heq context
  cases eq_of_heq departure
  exact .body
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}
private theorem same_role_endpoint {T : Type} {canonical : T} {n m : N}
    {p : Port (g.label n).sort} {q : Port (g.label m).sort}
    (nodes : n=m) (left : HEq p canonical) (right : HEq q canonical) :
    (.inl ⟨n,p⟩ : Endpoint g)=.inl ⟨m,q⟩ := by
  subst m
  cases eq_of_heq (left.trans right.symm)
  rfl
/-- All six ports retain real old occurrence/access provenance. These are
constructed from a selected physical fiber below, not caller map fields. -/
structure BetaSourcePorts (original : LTerm) (root : B) (beta : BetaEdge g) (appId lamId : Labelled.Label) : Prop where
  appContext : SourcePortRealizes original g root (.appContext appId) (.inl ⟨beta.app,beta.appCtx⟩)
  appFunction : SourcePortRealizes original g root (.appFn appId) beta.funEnd
  appArgument : SourcePortRealizes original g root (.appArg appId) beta.argEnd
  lamContext : SourcePortRealizes original g root (.lamContext lamId) beta.ctxEnd
  lamBody : SourcePortRealizes original g root (.lamBody lamId) (.inl ⟨beta.lam,beta.lamBody⟩)
  lamBinding : SourcePortRealizes original g root (.lamBind lamId) (.inl ⟨beta.lam,beta.lamBind⟩)
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i : Nat}
/-- Exact old selection and original INIT identify the six old syntax ports
with the six actual ports of one fixed beta site. -/
theorem PathSite.selected_beta_source_ports
    (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
    {root : B} {original : LTerm} (initial : INIT original)
    (matching : Matches site.net root original.erase) :
    ∃ beta : BetaEdge site.net,beta.app=.inr (.inl ()) ∧ beta.lam=.inr (.inr ()) ∧
      ∀ {degree appId lamId},SelectedDegree original (site.betaSyntaxFiber root original.erase) degree →
      SourceRoute (sourceEdges [] .external original) (.appFn appId) degree (.lamContext lamId) →
      degree=lamId ∧ BetaSourcePorts original root beta appId lamId := by
  obtain ⟨beta,app,lam,allDegrees⟩ := site.selected_degree_principal_fragment matching
  refine ⟨beta,app,lam,?_⟩
  intro degree appId lamId selected route
  obtain ⟨name,oldApp,body,argument,member,lookup,fragment,segments⟩ := allDegrees degree selected
  obtain ⟨n,atomic⟩ := selected.atomic initial
  rw [atomic] at route
  obtain ⟨edge,edgeMember,edgeAtom,edgeFrom,edgeTo⟩ := route.initial_atom_edge initial
  have equal := sourceEdges_unique initial edgeMember fragment.source_member (edgeAtom.trans atomic.symm)
  have appEq : oldApp=appId := SourcePort.appFn.inj ((congrArg SourceEdge.fromPort equal).symm.trans edgeFrom)
  have lamEq : degree=lamId := SourcePort.lamContext.inj ((congrArg SourceEdge.toPort equal).symm.trans edgeTo)
  cases appEq
  cases lamEq
  have eraseLookup : subtermAt original.erase name=some (.app (.lam body.erase) argument.erase) := by
    rw [←LTerm.erase_subterm,lookup]; rfl
  let redex : RedexOcc original.erase := ⟨name,⟨_,eraseLookup,True.intro⟩⟩
  obtain ⟨source⟩ := matching.actual_redex_access redex
  have physical := (source.physical_selection_iff site.net root original.erase
    (.inr (.inl ())) (.inr (.inr ())) matching).mp member
  have appNode := physical.1.trans app.symm
  have lamNode := physical.2.trans lam.symm
  have appCtx := same_role_endpoint appNode source.contextPrincipal beta.appCtx_role
  have lamCtx := same_role_endpoint lamNode source.connection.lamPrincipal beta.lamCtx_role
  have parentFinish : source.parent.val.getLast?=some (site.net.wire (.inl ⟨beta.app,beta.appCtx⟩)) := by
    rw [←appCtx]; exact source.parentFinish
  have childFinish : source.child.val.getLast?=some (site.net.wire beta.ctxEnd) := by
    rw [source.split,List.getLast?_append,source.connection.finish]
    simp only [lamCtx,Option.some_or,BetaEdge.ctxEnd]
  have lambdaLookup : original.subterm (name++[.fn])=some (.lam degree body) := by
    rw [LTerm.subterm_append,lookup]; rfl
  refine ⟨rfl,{
    appContext := .appContext lookup source.parent source.parentWord
      (congrArg Graph.Label.sort beta.appLabel) beta.appCtx_role parentFinish
    appFunction := .departure lookup .fn source.parent source.parentWord
      (ports_function _ _ _ beta.appLabel beta.appCtx_role beta.appFun_role) parentFinish
    appArgument := .departure lookup .arg source.parent source.parentWord
      (ports_argument _ _ _ beta.appLabel beta.appCtx_role beta.appArg_role) parentFinish
    lamContext := .lamContext lambdaLookup source.child source.childWord
      (congrArg Graph.Label.sort beta.lamLabel) beta.lamCtx_role childFinish
    lamBody := .departure lambdaLookup .body source.child source.childWord
      (ports_body _ _ _ beta.lamLabel beta.lamCtx_role beta.lamBody_role) childFinish
    lamBinding := .binding lambdaLookup source.child source.childWord
      (congrArg Graph.Label.sort beta.lamLabel) beta.lamCtx_role beta.lamBind_role childFinish }⟩
end
private theorem syntax_forward {kind : Kind} {ctx out : Port kind}
    (roles : SyntaxChildPorts kind ctx out step) : ForwardPorts kind ctx out := by
  cases roles
  · exact ⟨rfl,Or.inl rfl⟩
  · exact ⟨rfl,Or.inr rfl⟩
  · exact ⟨rfl,rfl⟩
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}
/-- Literal interpretation of a source route. Atom images are actual old
edge fragments; bars use this fixed beta edge's complete principal list,
with reversal only for under. This predicate asserts no root generation. -/
inductive SourceRouteImage (original : LTerm) (root : B) (beta : BetaEdge g) :
    SourcePort → Labelled.Label → SourcePort → List (Endpoint g) → Prop where
  | atom (fragment : SourceEdgeFragment original g root edge p) (atomic : edge.atom=Labelled.Label.atom n) :
      SourceRouteImage original root beta edge.fromPort (Labelled.Label.atom n) edge.toPort fragment.segments
  | over (ports : BetaSourcePorts original root beta appId lamId)
      (left : SourceRouteImage original root beta start a (.appContext appId) xs)
      (right : SourceRouteImage original root beta (.lamBody lamId) b finish ys) :
      SourceRouteImage original root beta start ((a.concat lamId.over).concat b) finish
        ((xs++beta.principal)++ys)
  | under (ports : BetaSourcePorts original root beta appId lamId)
      (left : SourceRouteImage original root beta start a (.lamBind lamId) xs)
      (right : SourceRouteImage original root beta (.appArg appId) b finish ys) :
      SourceRouteImage original root beta start ((a.concat lamId.under).concat b) finish
        ((xs++beta.reverseRoute)++ys)
/-- A genuinely directed physical image, with original occurrence-based
endpoint witnesses and literal atom/bar decomposition. -/
structure PhysicalSourceWalk (original : LTerm) (root : B) (beta : BetaEdge g)
    (start : SourcePort) (label : Labelled.Label) (finish : SourcePort) where
  edges : List (Endpoint g)
  fromEndpoint : Endpoint g
  toEndpoint : Endpoint g
  fromRealizes : SourcePortRealizes original g root start fromEndpoint
  toRealizes : SourcePortRealizes original g root finish toEndpoint
  head : edges.head?=some fromEndpoint
  last : edges.getLast?=some (g.wire toEndpoint)
  forward : ExpandedForward g edges
  image : SourceRouteImage original root beta start label finish edges

theorem PhysicalSourceWalk.nonempty {original : LTerm} {root : B} {beta : BetaEdge g}
    {start finish : SourcePort} {label : Labelled.Label} (walk : PhysicalSourceWalk original root beta start label finish) : walk.edges≠[] := by
  intro empty
  have first := walk.head
  rw [empty] at first
  cases first
def PhysicalSourceWalk.over {original : LTerm} {root : B} {beta : BetaEdge g}
    (initial : INIT original) (matching : Matches g root original.erase)
    (ports : BetaSourcePorts original root beta appId lamId)
    (left : PhysicalSourceWalk original root beta start a (.appContext appId))
    (right : PhysicalSourceWalk original root beta (.lamBody lamId) b finish) :
    PhysicalSourceWalk original root beta start ((a.concat lamId.over).concat b) finish := by
  have leftEnd := left.toRealizes.unique initial matching ports.appContext
  have rightStart := right.fromRealizes.unique initial matching ports.lamBody
  have first := left.forward.splice left.last beta.principal_forward.expanded beta.principalStart (by
    rw [g.wire.involutive,leftEnd]
    exact .node beta.app beta.appCtx beta.appFun
      (syntax_forward (ports_function _ _ _ beta.appLabel beta.appCtx_role beta.appFun_role)))
  have middleLast : (left.edges++beta.principal).getLast?=some (g.wire beta.ctxEnd) := by
    simp only [List.getLast?_append,beta.principalEnd,Option.some_or,BetaEdge.ctxEnd]
  have final := first.splice middleLast right.forward (right.head.trans (congrArg some rightStart)) (by
    rw [g.wire.involutive]
    exact .node beta.lam beta.lamCtx beta.lamBody
      (syntax_forward (ports_body _ _ _ beta.lamLabel beta.lamCtx_role beta.lamBody_role)))
  exact {
    edges := (left.edges++beta.principal)++right.edges
    fromEndpoint := left.fromEndpoint,toEndpoint := right.toEndpoint
    fromRealizes := left.fromRealizes,toRealizes := right.toRealizes
    head := by simp only [List.head?_append,left.head,Option.some_or]
    last := by simp only [List.getLast?_append,right.last,Option.some_or]
    forward := final,image := .over ports left.image right.image }
def PhysicalSourceWalk.under {original : LTerm} {root : B} {beta : BetaEdge g}
    (initial : INIT original) (matching : Matches g root original.erase)
    (ports : BetaSourcePorts original root beta appId lamId)
    (left : PhysicalSourceWalk original root beta start a (.lamBind lamId))
    (right : PhysicalSourceWalk original root beta (.appArg appId) b finish) :
    PhysicalSourceWalk original root beta start ((a.concat lamId.under).concat b) finish := by
  have leftEnd := left.toRealizes.unique initial matching ports.lamBinding
  have rightStart := right.fromRealizes.unique initial matching ports.appArgument
  have first := left.forward.splice left.last beta.reverse_forward.expanded beta.reverse_start (by
    rw [g.wire.involutive,leftEnd]
    exact .bindToCtx beta)
  have middleLast : (left.edges++beta.reverseRoute).getLast?=some (g.wire beta.funEnd) := by
    simp only [List.getLast?_append,beta.reverse_finish,Option.some_or]
  have final := first.splice middleLast right.forward (right.head.trans (congrArg some rightStart)) (by
    rw [g.wire.involutive]
    exact .funToArg beta)
  exact {
    edges := (left.edges++beta.reverseRoute)++right.edges
    fromEndpoint := left.fromEndpoint,toEndpoint := right.toEndpoint
    fromRealizes := left.fromRealizes,toRealizes := right.toRealizes
    head := by simp only [List.head?_append,left.head,Option.some_or]
    last := by simp only [List.getLast?_append,right.last,Option.some_or]
    forward := final,image := .under ports left.image right.image }
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i : Nat}
/-- Every actual selected source route has a physical directed image using
one actual fixed site principal route in every bar. Atom fragments retain
their original assignments; no global splice labelling or generatedness is
assumed or claimed by this directional theorem. -/
theorem PathSite.selected_source_route_walk
    (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
    {root : B} {original : LTerm} (initial : INIT original) (closed : Closed original.erase)
    (matching : Matches site.net root original.erase) :
    ∃ beta : BetaEdge site.net,beta.app=.inr (.inl ()) ∧ beta.lam=.inr (.inr ()) ∧
      ∀ {start label finish},
      SelectedSourceRoute (sourceEdges [] .external original)
        (SelectedDegree original (site.betaSyntaxFiber root original.erase)) start label finish →
      Nonempty (PhysicalSourceWalk original root beta start label finish) := by
  obtain ⟨beta,app,lam,allPorts⟩ := site.selected_beta_source_ports initial matching
  refine ⟨beta,app,lam,?_⟩
  intro start label finish route
  induction route with
  | atom member atomic =>
    obtain ⟨p,fragment⟩ := matching.source_edge_member_fragment closed member
    obtain ⟨fragment⟩ := fragment
    exact ⟨{
      edges := fragment.segments,fromEndpoint := fragment.fromEndpoint,toEndpoint := fragment.toEndpoint
      fromRealizes := fragment.fromRealizes,toRealizes := fragment.toRealizes
      head := fragment.start,last := fragment.finish,forward := fragment.forward.expanded,image := .atom fragment atomic}⟩
  | over left selected middle right leftIH middleIH rightIH =>
    obtain ⟨equal,ports⟩ := allPorts selected middle.forget
    obtain ⟨leftWalk⟩ := leftIH
    obtain ⟨rightWalk⟩ := rightIH
    cases equal
    exact ⟨PhysicalSourceWalk.over initial matching ports leftWalk rightWalk⟩
  | under left selected middle right leftIH middleIH rightIH =>
    obtain ⟨equal,ports⟩ := allPorts selected middle.forget
    obtain ⟨leftWalk⟩ := leftIH
    obtain ⟨rightWalk⟩ := rightIH
    cases equal
    exact ⟨PhysicalSourceWalk.under initial matching ports leftWalk rightWalk⟩
end
end Lamping.AG





