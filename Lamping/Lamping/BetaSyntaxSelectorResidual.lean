import Lamping.Lamping.BetaCompleteMatching
import Lamping.Lamping.MatchingChildAccess

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

private theorem selector_port_kind {sort : Kind} {port : Port sort} {kind : AccessKind}
    (actual : (sort=.op .app ∧HEq port appCtx ∧kind=.app) ∨
      (sort=.op .lam ∧HEq port (Sum.inl () : Port (.op .lam)) ∧kind=.lam) ∨
      (sort=.op .lam ∧HEq port lamBind ∧kind=.var)) : portKind sort port=some kind := by
  rcases actual with ⟨rfl,role,rfl⟩ | ⟨rfl,role,rfl⟩ | ⟨rfl,role,rfl⟩ <;>
    cases eq_of_heq role <;> rfl

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
variable {root : B} {original target : LTerm} {ps : List Path} {marked : Marked}

/-- The actual typed lexical loop fixes the retained variable terminal.
Only finite binder geometry is used; the history inductions are reused. -/
theorem PhysicalSyntaxTrail.complete_variable_terminal
    (initial : INIT original) (matching : Matches site.net root original.erase)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (relative : Marked.RelativeHistory ps (Marked.mark (site.betaSyntaxFiber root original.erase) original.erase) marked)
    (normal : Marked.Normal marked) (history : History ps original target) (closed : Closed target.erase)
    {edge : BetaEdge site.net} (selection : SourceEdgeSelection original site.net root)
    (allWalks : ∀ {start stamp finish},SelectedSourceRoute (sourceEdges [] .external original)
      (SelectedDegree original (site.betaSyntaxFiber root original.erase)) start stamp finish →
      ∃ walk : PhysicalSourceWalk original root edge start stamp finish,walk.edges=selection.evalLabel edge stamp)
    (generated : GeneratedSyntaxPaths selection edge target)
    (supported : SupportedSyntaxBinders selection edge target)
    (paths : TypedSyntaxPaths selection edge target) (binders : TypedSyntaxBinders selection edge target)
    {position stamp index finish}
    (trail : PhysicalSyntaxTrail original root edge [] .external target position (.var stamp index) finish)
    (evaluation : target.sourceTrail selection.atomWord edge.principal edge.reverseRoute position=some trail.edges) :
    ∃ (node : K) (port : Port (kept node).sort),trail.toEndpoint=.inl ⟨.inl node,port⟩ ∧
      portKind (kept node).sort port=some .var := by
  obtain ⟨parent,q,origin,body,positionEq,atLambda,_bodyLookup,atVariable,_indexEq⟩ :=
    target.closed_variable_binder closed trail.lookup
  obtain ⟨ambient,loop,binder,ctx,ambientEval,leafEval,sort,ctxRole,ambientEnd,total⟩ :=
    realize_typed_binder generated supported paths binders atLambda atVariable
  have routes := relative_development_selected_routes initial relative history
  obtain ⟨parentFinish,parentTrail,parentEval⟩ := selection.syntax_evaluation initial matching allWalks routes atLambda
  have parentEdges : parentTrail.edges=ambient := Option.some.inj (parentEval.symm.trans ambientEval)
  obtain ⟨node,parentCtx,parentKept,_parentSort,_parentRole⟩ :=
    parentTrail.complete_lambda_terminal site initial matching flow positive relative normal history
  have parentEnd : parentTrail.toEndpoint=.inl ⟨binder,ctx⟩ := by
    have last := parentTrail.last
    rw [parentEdges] at last
    have wires := congrArg site.net.wire (Option.some.inj (last.symm.trans ambientEnd))
    simpa only [Pairing.involutive] using wires
  have nodeEq : binder=.inl node := by
    exact congrArg Sigma.fst (Sum.inl.inj (parentEnd.symm.trans parentKept))
  subst binder
  obtain ⟨output,seam,_count,_whole,_prefixLabels,binding,binderEq⟩ := total Context.empty
  rcases binding with ⟨actualBinder,isLam,bodyPort,bindPort,bodyRole,bindRole,loopStart,loopEnd,
    loopLabels,loopForward,shell⟩
  dsimp only at binderEq
  subst actualBinder
  have fullEval : target.sourceTrail selection.atomWord edge.principal edge.reverseRoute position=some (ambient++loop) := by
    rw [positionEq];exact leafEval
  have leafEdges : trail.edges=ambient++loop := Option.some.inj (evaluation.symm.trans fullEval)
  have leafEnd : trail.toEndpoint=.inl ⟨.inl node,bindPort⟩ := by
    have fullLast : trail.edges.getLast?=some (site.net.wire (.inl ⟨.inl node,bindPort⟩)) := by
      rw [leafEdges]
      simp only [List.getLast?_append,loopEnd,Option.some_or]
    have wires := congrArg site.net.wire (Option.some.inj (trail.last.symm.trans fullLast))
    simpa only [Pairing.involutive] using wires
  exact ⟨node,bindPort,leafEnd,selector_port_kind (Or.inr (Or.inr ⟨isLam,bindRole,rfl⟩))⟩

/-- Retain the literal ancestor residual discarded by the older coverage
interface. ONE selector and the actual typed history provide the trail. -/
theorem PathSite.beta_syntax_selector_residual
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
    {p sub} (lookup : target.subterm p=some sub) (requested : Context) :
    ∃ finish,∃ trail : PhysicalSyntaxTrail original root edge [] .external target p sub finish,
      ∃ access : RootAccess site.reduce root,∃ output,∃ (node : K) (port : Port (kept node).sort),
        target.sourceTrail selection.atomWord edge.principal edge.reverseRoute p=some trail.edges ∧
        BetaPathResidual site edge (access.val.map (plugEnd _ _).invFun) trail.edges ∧
        Labelling site.reduce access.val requested output ∧accessWord site.reduce access.val=p ∧
        accessKind site.reduce access.val=some (syntaxShape sub.erase).kind ∧
        trail.toEndpoint=.inl ⟨.inl node,port⟩ ∧
        portKind (kept node).sort port=some (syntaxShape sub.erase).kind := by
  have routes := relative_development_selected_routes initial relative history
  obtain ⟨finish,trail,evaluation⟩ := selection.syntax_evaluation initial matching allWalks routes lookup
  have terminal : ∃ (node : K) (port : Port (kept node).sort),
      trail.toEndpoint=.inl ⟨.inl node,port⟩ ∧portKind (kept node).sort port=some (syntaxShape sub.erase).kind := by
    cases sub with
    | var stamp index =>
      exact trail.complete_variable_terminal site initial matching flow positive relative normal history closed
        selection allWalks generated supported paths binders evaluation
    | app stamp fn arg =>
      obtain ⟨node,port,ending,sort,role⟩ :=
        trail.complete_app_terminal site initial matching flow positive relative normal history
      exact ⟨node,port,ending,selector_port_kind (Or.inl ⟨sort,role,rfl⟩)⟩
    | lam stamp body =>
      obtain ⟨node,port,ending,sort,role⟩ :=
        trail.complete_lambda_terminal site initial matching flow positive relative normal history
      exact ⟨node,port,ending,selector_port_kind (Or.inr (Or.inl ⟨sort,role,rfl⟩))⟩
  obtain ⟨node,port,ending,kind⟩ := terminal
  obtain ⟨output,_count,blocks⟩ := paths.at_word lookup evaluation requested
  obtain ⟨access,residual,labels,word,accessKind,_last⟩ := trail.beta_contract_access site initial matching flow positive
    relative normal history geometry (blocks.labelling _) node port _ ending kind
  exact ⟨finish,trail,access,output,node,port,evaluation,residual,labels,word,accessKind,ending,kind⟩

/-- Matches locks the independently chosen actual target access by its
syntax word. The result concerns that access, not an existential substitute. -/
theorem PathSite.beta_actual_selector_residual
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
    (targetMatching : Matches site.reduce root target.erase)
    {p sub} (lookup : target.subterm p=some sub) (access : RootAccess site.reduce root)
    (word : accessWord site.reduce access.val=p) (requested : Context) :
    ∃ finish,∃ trail : PhysicalSyntaxTrail original root edge [] .external target p sub finish,∃ output,
      ∃ (node : K) (port : Port (kept node).sort),
      target.sourceTrail selection.atomWord edge.principal edge.reverseRoute p=some trail.edges ∧
      BetaPathResidual site edge (access.val.map (plugEnd _ _).invFun) trail.edges ∧
      Labelling site.reduce access.val requested output ∧
      trail.toEndpoint=.inl ⟨.inl node,port⟩ ∧
      portKind (kept node).sort port=some (syntaxShape sub.erase).kind := by
  obtain ⟨finish,trail,actual,output,node,port,evaluation,residual,labels,actualWord,_kind,ending,proper⟩ :=
    site.beta_syntax_selector_residual initial matching flow positive relative normal history closed geometry
      selection allWalks generated supported paths binders lookup requested
  have same : actual=access := targetMatching.accessWord_injective (actualWord.trans word.symm)
  subst actual
  exact ⟨finish,trail,output,node,port,evaluation,residual,labels,ending,proper⟩

private theorem selector_endpoint_eq {n m : K⊕(Unit⊕Unit)}
    {p : Port (site.net.label n).sort} {q : Port (site.net.label m).sort}
    (same : n=m) (role : HEq p q) :
    (.inl ⟨n,p⟩ : Endpoint site.net)=.inl ⟨m,q⟩ := by
  subst m
  cases eq_of_heq role
  rfl

/-- The actual complete marked development internally supplies the shared
typed selector and target Matches. This is a geometry interface: original
is the current INIT annotation, not a replacement for any family history. -/
theorem PathSite.beta_complete_selector_residuals
    (initial : INIT original) (closed : Closed original.erase)
    (matching : Matches site.net root original.erase) (inputs : RootInputs site.net root)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {heights : B → Int} (balance : IndexedLevelBalance site.net heights) (rootDepth : heights root=0)
    (transparency : Transparency site.net root)
    (relative : Marked.RelativeHistory ps (Marked.mark (site.betaSyntaxFiber root original.erase) original.erase) marked)
    (normal : Marked.Normal marked) (history : History ps original target) :
    ∃ edge : BetaEdge site.net,∃ selection : SourceEdgeSelection original site.net root,
      SiteBetaGeometry site edge ∧
      ∀ {p sub},target.subterm p=some sub →∀ (access : RootAccess site.reduce root),
        accessWord site.reduce access.val=p →∀ requested : Context,
        ∃ finish,∃ trail : PhysicalSyntaxTrail original root edge [] .external target p sub finish,∃ output,
          ∃ (node : K) (port : Port (kept node).sort),
          target.sourceTrail selection.atomWord edge.principal edge.reverseRoute p=some trail.edges ∧
          BetaPathResidual site edge (access.val.map (plugEnd _ _).invFun) trail.edges ∧
          Labelling site.reduce access.val requested output ∧
          trail.toEndpoint=.inl ⟨.inl node,port⟩ ∧
          portKind (kept node).sort port=some (syntaxShape sub.erase).kind := by
  obtain ⟨edge,app,lam,selection,_ports,walks,histories⟩ := site.relative_history_typed_with_walks
    initial closed matching inputs flow positive balance rootDepth transparency
  obtain ⟨generated,supported,paths,binders⟩ := histories relative history
  have geometry : SiteBetaGeometry site edge :=
    ⟨selector_endpoint_eq site app edge.appCtx_role,selector_endpoint_eq site lam edge.lamBody_role,
      selector_endpoint_eq site lam edge.lamBind_role,selector_endpoint_eq site app edge.appArg_role⟩
  have targetMatching := site.beta_complete_matches initial closed matching inputs flow positive
    balance rootDepth transparency relative normal history
  refine ⟨edge,selection,geometry,?_⟩
  intro p sub lookup access word requested
  exact site.beta_actual_selector_residual initial matching flow positive relative normal history (history.closed closed)
    geometry selection walks generated supported paths binders targetMatching lookup access word requested
end
end Lamping.AG
