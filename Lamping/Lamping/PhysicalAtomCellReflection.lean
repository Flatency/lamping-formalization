import Lamping.Lamping.CompletePhysicalLambdaOrigins
import Lamping.Lambda.LabelImageTraversal
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
private def endpointKind (g : Net signature N B W) : Endpoint g → Option AccessKind
  | .inl ⟨n,p⟩ => portKind (g.label n).sort p
  | _ => none
private theorem app_kind {k : Kind} {p : Port k} (shape : k=.op .app)
    (role : HEq p appCtx) : portKind k p=some .app := by
  subst k
  cases eq_of_heq role
  rfl
private theorem binding_kind {k : Kind} {p : Port k} (shape : k=.op .lam)
    (role : HEq p lamBind) : portKind k p=some .var := by
  subst k
  cases eq_of_heq role
  rfl
private theorem lambda_kind {k : Kind} {p : Port k} (shape : k=.op .lam)
    (role : HEq p (Sum.inl () : Port (.op .lam))) : portKind k p=some .lam := by
  subst k
  cases eq_of_heq role
  rfl
private theorem departure_kind {k : Kind} {ctx dep : Port k}
    (roles : SyntaxChildPorts k ctx dep step) : portKind k dep=none := by
  cases roles <;> rfl
private theorem realization_lambda_context {g : Net signature N B W} {root : B}
    {original : LTerm} {sourcePort : SourcePort} {e : Endpoint g}
    (realizes : SourcePortRealizes original g root sourcePort e)
    (kind : endpointKind g e=some .lam) : ∃origin,sourcePort=.lamContext origin := by
  cases realizes with
  | external => cases kind
  | departure lookup role parent word roles finish =>
    have typed := departure_kind roles
    simp only [endpointKind,typed] at kind
    cases kind
  | appContext lookup access word shape role finish =>
    have typed := app_kind shape role
    simp only [endpointKind,typed] at kind
    cases kind
  | lamContext lookup access word shape role finish => exact ⟨_,rfl⟩
  | binding lookup parent word shape ctxRole role finish =>
    have typed := binding_kind shape role
    simp only [endpointKind,typed] at kind
    cases kind
private theorem principal_kind {g : Net signature N B W} (edge : BetaEdge g) :
    endpointKind g edge.ctxEnd=some .lam :=
  lambda_kind (congrArg (fun label => label.sort) edge.lamLabel) edge.lamCtx_role
private theorem reverse_start {g : Net signature N B W} (edge : BetaEdge g) :
    edge.reverseRoute.head?=some edge.ctxEnd := by
  simp only [BetaEdge.reverseRoute,List.head?_map,List.head?_reverse,edge.principalEnd,
    Option.map_some,g.wire.involutive,BetaEdge.ctxEnd]
/-- An actual source cell cannot start at a lambda principal context: whole
source edges start at the external root or at genuine syntax departures. -/
theorem SourceEdgeSelection.atom_word_ne_reverse_principal
    {g : Net signature N B W} {root : B} {original : LTerm}
    (selection : SourceEdgeSelection original g root) (edge : BetaEdge g) (n : Nat) :
    selection.atomWord n≠edge.reverseRoute := by
  classical
  intro collision
  unfold SourceEdgeSelection.atomWord at collision
  split at collision
  next member =>
    let cell := Classical.choose member
    let fragment := (selection.chosen cell).2
    have endpoint : fragment.fromEndpoint=edge.ctxEnd :=
      Option.some.inj (fragment.start.symm.trans (collision ▸ reverse_start edge))
    have kind : endpointKind g fragment.fromEndpoint=some .lam := by
      rw [endpoint]; exact principal_kind edge
    obtain ⟨origin,port⟩ := realization_lambda_context fragment.fromRealizes kind
    have impossible := (sourceEdges_from_lambda_port original cell.property).2 port
    cases impossible
  next absent =>
    have impossible := reverse_start edge
    rw [←collision] at impossible
    cases impossible
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
private theorem atomic_lambda_terminal {env : List Label} {ctx : SourcePort} {sub : LTerm}
    (atomic : (sourceEdge env ctx sub).atom=Label.atom n)
    (terminal : (sourceEdge env ctx sub).toPort=.lamContext origin) : origin=Label.atom n := by
  cases sub with
  | app label fn arg => cases terminal
  | lam label body => exact (SourcePort.lamContext.inj terminal).symm.trans atomic
  | var label index =>
    simp only [sourceEdge,sourceBinder] at terminal
    split at terminal <;> cases terminal
/-- Equality of the whole chosen cell with the beta principal path supplies
its real selected FUNCTION occurrence, not an injected current coordinate. -/
theorem PathSite.atom_word_principal_selected_function
    {root : B} {source : LTerm} {n : Nat} {edge : BetaEdge site.net}
    (geometry : SiteBetaGeometry site edge)
    (selection : SourceEdgeSelection (initLabels source.erase) site.net root)
    (matching : Matches site.net root source.erase)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (collision : selection.atomWord n=edge.principal) :
    ∃name appStamp body argument,
      name∈site.betaSyntaxFiber root source.erase ∧
      (initLabels source.erase).subterm name=
        some (.app appStamp (.lam (Label.atom n) body) argument) := by
  classical
  have canonical : edge.ctxEnd=(.inl ⟨.inr (.inr ()),.inl ()⟩ : Endpoint site.net) := by
    have nodeEq : edge.lam=.inr (.inr ()) :=
      congrArg Sigma.fst (Sum.inl.inj geometry.binding)
    apply congrArg Sum.inl
    exact Sigma.ext nodeEq edge.lamCtx_role
  have matching' : Matches site.net root (initLabels source.erase).erase := by
    simpa only [erase_initLabels] using matching
  unfold SourceEdgeSelection.atomWord at collision
  split at collision
  next member =>
    let cell := Classical.choose member
    let fragment := (selection.chosen cell).2
    have wires : site.net.wire fragment.toEndpoint=site.net.wire edge.ctxEnd :=
      Option.some.inj (fragment.finish.symm.trans (collision ▸ edge.principalEnd))
    have endpoint : fragment.toEndpoint=edge.ctxEnd := by
      have twice := congrArg site.net.wire wires
      simpa only [site.net.wire.involutive] using twice
    have kind : endpointKind site.net fragment.toEndpoint=some .lam := by
      rw [endpoint]; exact principal_kind edge
    obtain ⟨origin,port⟩ := realization_lambda_context fragment.toRealizes kind
    obtain ⟨env,ctx,sub,occurrence,sourceEdgeEq⟩ := fragment.occurrence
    have originEq : origin=Label.atom n := atomic_lambda_terminal
      ((congrArg SourceEdge.atom sourceEdgeEq).trans (Classical.choose_spec member))
      ((congrArg SourceEdge.toPort sourceEdgeEq).trans port)
    have realizes : SourcePortRealizes (initLabels source.erase) site.net root
        (.lamContext (Label.atom n)) (.inl ⟨.inr (.inr ()),.inl ()⟩) := by
      rw [←canonical,←endpoint,←originEq,←port]
      exact fragment.toRealizes
    cases realizes with
    | departure lookup role parent word roles finish => cases role
    | lamContext lookup access word shape role finish =>
      obtain ⟨name,stamp,argument,position,atHead,_,selected⟩ :=
        site.source_lambda_selected_origin matching' flow positive lookup access word finish
      obtain ⟨other,member,atDegree⟩ := selected
      have degree : (initLabels source.erase).degreeAt name=some (Label.atom n) := by
        simp only [LTerm.degreeAt,atHead,Option.bind_some,LTerm.degree]
      have equal := LTerm.initial_degree_injective (init_is_INIT source.erase) degree atDegree
      exact ⟨name,stamp,_,argument,by simpa only [←equal,erase_initLabels] using member,atHead⟩
  next absent =>
    have impossible := edge.principalStart
    rw [←collision] at impossible
    cases impossible
end
end Lamping.AG
