import Lamping.Lamping.BetaSyntaxVariableAccess
import Lamping.Lamping.BetaForwardCoverageMatching
import Lamping.Lamping.RelativeHistoryTyped

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

private theorem context_kind {kind : Kind} {ctx : Port kind}
    (sort : kind=.op .app) (role : HEq ctx appCtx) : portKind kind ctx=some .app := by
  subst kind
  cases eq_of_heq role
  rfl
private theorem lambda_kind {kind : Kind} {ctx : Port kind}
    (sort : kind=.op .lam) (role : HEq ctx (Sum.inl () : Port (.op .lam))) : portKind kind ctx=some .lam := by
  subst kind
  cases eq_of_heq role
  rfl

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
variable {root : B} {original target : LTerm} {ps : List Path} {marked : Marked}

/-- All current syntax constructors have genuinely constructed RHS
accesses. Variable indices are supplied by their transported actual binding
loops, rather than by kind coverage alone. -/
theorem PathSite.beta_syntax_access_coverage
    (initial : INIT original) (matching : Matches site.net root original.erase)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (relative : Marked.RelativeHistory ps (Marked.mark (site.betaSyntaxFiber root original.erase) original.erase) marked)
    (normal : Marked.Normal marked) (history : History ps original target) (closed : Closed target.erase)
    {edge : BetaEdge site.net} (geometry : SiteBetaGeometry site edge)
    (selection : SourceEdgeSelection original site.net root)
    (allWalks : ∀ {start stamp finish},SelectedSourceRoute (sourceEdges [] .external original)
      (SelectedDegree original (site.betaSyntaxFiber root original.erase)) start stamp finish →
      ∃ walk : PhysicalSourceWalk original root edge start stamp finish,walk.edges=selection.evalLabel edge stamp)
    (generated : GeneratedSyntaxPaths selection edge target)
    (supported : SupportedSyntaxBinders selection edge target)
    (paths : TypedSyntaxPaths selection edge target) (binders : TypedSyntaxBinders selection edge target)
    {p sub} (lookup : target.subterm p=some sub) :
    ∃ access : RootAccess site.reduce root,accessWord site.reduce access.val=p ∧
      accessKind site.reduce access.val=some (syntaxShape sub.erase).kind ∧
      (match sub with | .var _ k => BindingSuffix site.reduce access.val k | _ => True) := by
  cases sub with
  | var stamp index =>
    exact site.beta_variable_access initial matching flow positive relative normal history closed geometry selection
      allWalks generated supported paths binders lookup
  | app stamp fn arg =>
    have routes := relative_development_selected_routes initial relative history
    obtain ⟨finish,trail,evaluation⟩ := selection.syntax_evaluation initial matching allWalks routes lookup
    obtain ⟨node,ctx,terminal,sort,role⟩ := trail.complete_app_terminal site initial matching flow positive relative normal history
    obtain ⟨output,_count,blocks⟩ := paths.at_word lookup evaluation Context.empty
    obtain ⟨access,_residual,_labels,word,kind,_last⟩ := trail.beta_contract_access site initial matching flow positive
      relative normal history geometry (blocks.labelling _) node ctx .app terminal (context_kind sort role)
    exact ⟨access,word,kind,True.intro⟩
  | lam stamp body =>
    have routes := relative_development_selected_routes initial relative history
    obtain ⟨finish,trail,evaluation⟩ := selection.syntax_evaluation initial matching allWalks routes lookup
    obtain ⟨node,ctx,terminal,sort,role⟩ := trail.complete_lambda_terminal site initial matching flow positive relative normal history
    obtain ⟨output,_count,blocks⟩ := paths.at_word lookup evaluation Context.empty
    obtain ⟨access,_residual,_labels,word,kind,_last⟩ := trail.beta_contract_access site initial matching flow positive
      relative normal history geometry (blocks.labelling _) node ctx .lam terminal (lambda_kind sort role)
    exact ⟨access,word,kind,True.intro⟩

private theorem port_endpoint_eq {n m : K⊕(Unit⊕Unit)}
    {p : Port (site.net.label n).sort} {q : Port (site.net.label m).sort}
    (same : n=m) (role : HEq p q) :
    (.inl ⟨n,p⟩ : Endpoint site.net)=.inl ⟨m,q⟩ := by
  subst m
  cases eq_of_heq role
  rfl

/-- An actual complete development of the OLD physical beta fiber gives
Matches on the actual RHS net. One physical beta and one shared selector
are fixed before the real history induction. The resulting paths are then
contracted with their assignments, literal syntax words and binding loops;
no target coverage or correctness certificate is supplied. -/
theorem PathSite.beta_complete_matches
    (initial : INIT original) (closed : Closed original.erase)
    (matching : Matches site.net root original.erase)
    (inputs : RootInputs site.net root)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {heights : B → Int} (balance : IndexedLevelBalance site.net heights) (rootDepth : heights root=0)
    (transparency : Transparency site.net root)
    (relative : Marked.RelativeHistory ps (Marked.mark (site.betaSyntaxFiber root original.erase) original.erase) marked)
    (normal : Marked.Normal marked) (history : History ps original target) : Matches site.reduce root target.erase := by
  obtain ⟨edge,app,lam,selection,_ports,walks,histories⟩ := site.relative_history_typed_with_walks
    initial closed matching inputs flow positive balance rootDepth transparency
  obtain ⟨generated,supported,paths,binders⟩ := histories relative history
  have geometry : SiteBetaGeometry site edge :=
    ⟨port_endpoint_eq site app edge.appCtx_role,port_endpoint_eq site lam edge.lamBody_role,
      port_endpoint_eq site lam edge.lamBind_role,port_endpoint_eq site app edge.appArg_role⟩
  apply site.beta_matches_of_kind_binding_coverage flow root positive balance rootDepth inputs transparency target.erase
  intro position
  have existsSub : ∃ sub,target.subterm position.val=some sub := by
    have erased := target.erase_subterm position.val
    cases lookup : target.subterm position.val with
    | some sub => exact ⟨sub,rfl⟩
    | none => rw [lookup] at erased; have absent := position.property; rw [←erased] at absent; cases absent
  obtain ⟨sub,lookup⟩ := existsSub
  obtain ⟨access,word,kind,suffix⟩ := site.beta_syntax_access_coverage initial matching flow positive
    relative normal history (history.closed closed) geometry selection walks generated supported paths binders lookup
  refine ⟨access,sub.erase,?_,word,kind,?_⟩
  · rw [←LTerm.erase_subterm,lookup]; rfl
  · cases sub <;> exact suffix
end
end Lamping.AG
