import Lamping.Lamping.HistoryTypedInternalAssignments
import Lamping.Lamping.HistoryGeneratedCopyStep
import Lamping.Lamping.SupportedLoopPorts
import Lamping.Lambda.NestedBinderCoordinates
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {original : LTerm}
private theorem realizes_source_eq {fromPort toPort : SourcePort} {endpoint : Endpoint g}
    (same : fromPort=toPort) (realizes : SourcePortRealizes original g root fromPort endpoint) :
    SourcePortRealizes original g root toPort endpoint := same ▸ realizes
private theorem body_roles {kind : Kind} {ctx body : Port kind}
    (roles : SyntaxChildPorts kind ctx body .body) :
    kind=.op .lam ∧HEq ctx (Sum.inl () : Port (.op .lam)) ∧HEq body lamBody := by
  cases roles
  exact ⟨rfl,HEq.rfl,HEq.rfl⟩
private theorem lambda_departure (initial : INIT original) (matching : Matches g root original.erase)
    {origin : Labelled.Label} {binder : N} {ctx : Port (g.label binder).sort} {endpoint : Endpoint g}
    (left : SourcePortRealizes original g root (.lamContext origin) (.inl ⟨binder,ctx⟩))
    (right : SourcePortRealizes original g root (.lamBody origin) endpoint) :
    ∃ body : Port (g.label binder).sort,HEq body lamBody ∧endpoint=.inl ⟨binder,body⟩ := by
  cases right with
  | departure lookup sourceRole parent word roles finish =>
    cases sourceRole
    obtain ⟨shape,role,bodyRole⟩ := body_roles roles
    have same := left.unique initial matching (.lamContext lookup parent word shape role finish)
    have nodes := congrArg Sigma.fst (Sum.inl.inj same)
    dsimp only at nodes
    subst binder
    exact ⟨_,bodyRole,rfl⟩
private theorem labelled_lookup {term : LTerm} {p : Path} {u : Term}
    (lookup : subtermAt term.erase p=some u) : ∃ sub,term.subterm p=some sub := by
  rw [←LTerm.erase_subterm] at lookup
  cases found : term.subterm p with
  | none => rw [found] at lookup; cases lookup
  | some sub => exact ⟨sub,rfl⟩

private theorem redex_function_eval {X : Type} (atoms : Nat → List X) (overWord underWord : List X)
    {current : LTerm} {site : Path} {stamp degree : Labelled.Label} {body argument : LTerm}
    (lookup : current.subterm site=some (.app stamp (.lam degree body) argument)) :
    current.sourceTrail atoms overWord underWord (site++[.fn])=
      (current.sourceTrail atoms overWord underWord site).map
        (fun stem => stem++degree.sourceWord atoms overWord underWord) := by
  have atRoot := LTerm.sourceTrail_split atoms overWord underWord lookup []
  simp only [List.append_nil] at atRoot
  rw [LTerm.sourceTrail_split atoms overWord underWord lookup [.fn],atRoot]
  cases current.sourceStem atoms overWord underWord site <;>
    simp [LTerm.sourceTrail,LTerm.label,List.append_assoc]

private theorem redex_argument_eval {X : Type} (atoms : Nat → List X) (overWord underWord : List X)
    {current : LTerm} {site : Path} {stamp degree : Labelled.Label} {body argument : LTerm}
    (lookup : current.subterm site=some (.app stamp (.lam degree body) argument)) (r : Path) :
    current.sourceTrail atoms overWord underWord (site++(.arg::r))=
      (current.sourceTrail atoms overWord underWord site).bind
        (fun stem => (argument.sourceTrail atoms overWord underWord r).map (fun word => stem++word)) := by
  have atRoot := LTerm.sourceTrail_split atoms overWord underWord lookup []
  simp only [List.append_nil] at atRoot
  rw [LTerm.sourceTrail_split atoms overWord underWord lookup (.arg::r),atRoot]
  cases current.sourceStem atoms overWord underWord site <;>
    cases argEval : argument.sourceTrail atoms overWord underWord r <;> simp [LTerm.sourceTrail,LTerm.label,argEval,List.append_assoc]

private theorem selected_subterm
    (routes : SelectedTermRoutes edges allowed env ctx current)
    (lookup : current.subterm p=some sub) :
    ∃ localEnv localCtx,SelectedTermRoutes edges allowed localEnv localCtx sub := by
  induction p generalizing current env ctx with
  | nil =>
    have here : current.subterm []=some current := by cases current <;> rfl
    cases Option.some.inj (here.symm.trans lookup)
    exact ⟨env,ctx,routes⟩
  | cons s p ih =>
    cases routes with
    | var route => cases s <;> simp [LTerm.subterm] at lookup
    | lam route body =>
      cases s with
      | fn | arg => simp [LTerm.subterm] at lookup
      | body => exact ih body lookup
    | app route fn arg =>
      cases s with
      | body => simp [LTerm.subterm] at lookup
      | fn => exact ih fn lookup
      | arg => exact ih arg lookup

/-- The actual event-inside-lambda copied-leaf TypedL branch. Source routes
and previous L fix the common ambient, inner loop and the selected lambda
body departure; the anchored assignment transport then preserves the given
outer binder's shell. No target labels or previous Generated premise is
used to supply a shell. -/theorem TypedSyntaxBinders.internal_copy_step
    (initial : INIT original) (matching : Matches g root original.erase)
    (selection : SourceEdgeSelection original g root) (beta : BetaEdge g)
    {allowed : Labelled.Label → Prop}
    (allWalks : ∀ {start stamp finish},SelectedSourceRoute (sourceEdges [] .external original) allowed start stamp finish →
      ∃ walk : PhysicalSourceWalk original root beta start stamp finish,walk.edges=selection.evalLabel beta stamp)
    {current target oldOuterBody newOuterBody body argument : LTerm} {outer p q r : Path}
    {outerStamp stamp degree : Labelled.Label}
    (routes : SelectedTermRoutes (sourceEdges [] .external original) allowed [] .external current)
    (step : StepAt (outer++(.body::p)) current target)
    (localStep : StepAt p oldOuterBody newOuterBody)
    (outerLookup : current.subterm outer=some (.lam outerStamp oldOuterBody))
    (lookup : oldOuterBody.subterm p=some (.app stamp (.lam degree body) argument))
    {appId lamId : Labelled.Label} {localCtx : SourcePort}
    (headRoute : SourceRoute (sourceEdges [] .external original) localCtx stamp (.appContext appId))
    (function : SourceRoute (sourceEdges [] .external original) (.appFn appId) degree (.lamContext lamId))
    (ports : BetaSourcePorts original root beta appId lamId)
    (active : selection.evalLabel beta degree=beta.principal)
    (argumentRoutes : SelectedTermRoutes (sourceEdges [] .external original) allowed env (.appArg appId) argument)
    (occurs : ArgumentOccurrence body.erase q)
    (currentLeaf : ArgumentOccurrence newOuterBody.erase (p++(q++r)))
    (binders : SupportedSyntaxBinders selection beta current)
    (typed : TypedSyntaxBinders selection beta current)
    {boundary : B → Bool} (flow : FlowBalance g boundary) (positive : boundary root=true)
    {heights : B → Int} (balance : IndexedLevelBalance g heights) (rootDepth : heights root=0)
    {wantedAmbient wantedLoop : List (Endpoint g)} {wantedBinder : N} {wantedCtx : Port (g.label wantedBinder).sort}
    (wantedAmbientEval : target.sourceTrail selection.atomWord beta.principal beta.reverseRoute outer=some wantedAmbient)
    (wantedBodyEval : target.sourceTrail selection.atomWord beta.principal beta.reverseRoute (outer++(.body::(p++(q++r))))=some (wantedAmbient++wantedLoop))
    (_wantedShape : (g.label wantedBinder).sort=.op .lam) (_wantedRole : HEq wantedCtx (Sum.inl () : Port (.op .lam)))
    (wantedFinish : wantedAmbient.getLast?=some (g.wire (.inl ⟨wantedBinder,wantedCtx⟩)))
    {input output seam : Context} {count : Nat}
    (whole : BetaDetourBlocks g (wantedAmbient++wantedLoop) input output count)
    (before : ExpandedLabelling g wantedAmbient input seam) :
    Context.SameShell (g.label wantedBinder).index seam output := by
  have bareLookup : subtermAt oldOuterBody.erase p=some (.app (.lam body.erase) argument.erase) := by
    rw [←LTerm.erase_subterm,lookup]
    rfl
  have oldArgumentLeaf := (localStep.betaAt.nested_copied_outer_variable_iff bareLookup occurs r).mp currentLeaf
  have oldOuterLeaf : ArgumentOccurrence oldOuterBody.erase (p++(.arg::r)) := by
    simp only [ArgumentOccurrence,subtermAt_append,bareLookup,Option.bind_some,subtermAt,binderDepth_append,binderDepth]
    exact oldArgumentLeaf
  obtain ⟨ambient,outerLoop,binder,ctx,ambientEval,oldOuterEval,outerSupport,shape,role,finish⟩ :=
    binders outerLookup oldOuterLeaf
  obtain ⟨outerEnv,outerCtx,outerRoutes⟩ := selected_subterm routes outerLookup
  cases outerRoutes with
  | lam outerRoute bodyRoutes =>
    obtain ⟨_preFinish,preTrail,preEval⟩ := selection.syntax_evaluation initial matching allWalks bodyRoutes lookup
    let pre := preTrail.edges
    have preEnd : pre.getLast?=some (g.wire (.inl ⟨beta.app,beta.appCtx⟩)) :=
      ports.app_trail_last initial matching headRoute preTrail
    have globalLookup : current.subterm (outer++(.body::p))=some (.app stamp (.lam degree body) argument) := by
      rw [LTerm.subterm_append,outerLookup]
      exact lookup
    have stemEval : current.sourceTrail selection.atomWord beta.principal beta.reverseRoute (outer++(.body::p))=
        some (ambient++pre) := by
      rw [LTerm.sourceTrail_child_descendant selection.atomWord beta.principal beta.reverseRoute (childStep:=.body) (child:=oldOuterBody) outerLookup (by cases oldOuterBody <;> rfl) p,
        ambientEval,Option.bind_some,preEval,Option.map_some]
    obtain ⟨argSub,argLookup⟩ := labelled_lookup oldArgumentLeaf
    obtain ⟨_argFinish,argTrail,argEval⟩ := selection.syntax_evaluation initial matching allWalks argumentRoutes argLookup
    have argEndpoint : argTrail.fromEndpoint=beta.argEnd := argTrail.fromRealizes.unique initial matching ports.appArgument
    obtain ⟨tail,argSplit⟩ := List.head?_eq_some_iff.mp (argTrail.head.trans (congrArg some argEndpoint))
    have localArgEval : argument.sourceTrail selection.atomWord beta.principal beta.reverseRoute r=some (beta.argEnd::tail) := by
      rw [argEval,argSplit]
    have localOldLeafEval := redex_argument_eval selection.atomWord beta.principal beta.reverseRoute lookup r
    rw [preEval,Option.bind_some,localArgEval,Option.map_some] at localOldLeafEval
    have outerLoopEq : outerLoop=pre++beta.argEnd::tail := by
      have fullEval := LTerm.sourceTrail_child_descendant selection.atomWord beta.principal beta.reverseRoute (childStep:=.body) (child:=oldOuterBody) outerLookup (by cases oldOuterBody <;> rfl) (p++(.arg::r))
      rw [ambientEval,Option.bind_some,localOldLeafEval,Option.map_some,oldOuterEval] at fullEval
      exact List.append_cancel_left (Option.some.inj fullEval)
    have innerLambda : current.subterm ((outer++(.body::p))++[.fn])=some (.lam degree body) := by
      rw [LTerm.subterm_append,globalLookup]
      rfl
    obtain ⟨innerAmbient,innerLoop,innerBinder,innerCtx,innerEval,innerBodyEval,innerSupport,_innerShape,_innerRole,innerEnd⟩ :=
      binders innerLambda occurs
    have innerAmbientEq : innerAmbient=(ambient++pre)++beta.principal := by
      have equal := redex_function_eval selection.atomWord beta.principal beta.reverseRoute globalLookup
      rw [stemEval,Option.map_some] at equal
      change _=some ((ambient++pre)++selection.evalLabel beta degree) at equal
      rw [active,innerEval] at equal
      exact Option.some.inj equal
    obtain ⟨_lamFinish,lambdaTrail,lambdaEval⟩ := selection.syntax_evaluation initial matching allWalks routes innerLambda
    have lambdaWord : lambdaTrail.edges=innerAmbient := Option.some.inj (lambdaEval.symm.trans innerEval)
    have innerEnd' : innerAmbient.getLast?=some (g.wire beta.ctxEnd) := by
      rw [←lambdaWord]
      exact ports.lam_trail_last initial matching function lambdaTrail
    have innerBinderEq : innerBinder=beta.lam := by
      have endpoints := congrArg (fun e => g.wire e) (Option.some.inj (innerEnd.symm.trans innerEnd'))
      simp only [Pairing.involutive] at endpoints
      exact congrArg Sigma.fst (Sum.inl.inj endpoints)
    have nestedSupport : SupportedExpandedBindingLoop g root (ambient++pre++beta.principal) beta.lam innerLoop := by
      simpa only [innerAmbientEq,innerBinderEq] using innerSupport
    obtain ⟨start,last⟩ := nestedSupport.beta_endpoints beta rfl
    let newLoop := pre++beta.principal++innerLoop++beta.reverseRoute++[beta.argEnd]++tail
    have beforeSite : ¬∃ suffix,outer=(outer++(.body::p))++suffix := by
      rintro ⟨suffix,equal⟩
      have lengths := congrArg List.length equal
      simp only [List.length_append,List.length_cons] at lengths
      omega
    have currentAmbientEval : target.sourceTrail selection.atomWord beta.principal beta.reverseRoute outer=some ambient :=
      (step.sourceTrail_outside selection.atomWord beta.principal beta.reverseRoute outer beforeSite).trans ambientEval
    have newLeafEval : target.sourceTrail selection.atomWord beta.principal beta.reverseRoute
        (outer++(.body::(p++(q++r))))=some (ambient++newLoop) := by
      have equal := step.sourceTrail_copy_splice selection.atomWord beta.principal beta.reverseRoute globalLookup active occurs r
      have innerBodyEval' : current.sourceTrail selection.atomWord beta.principal beta.reverseRoute
          ((outer++(.body::p))++(.fn::.body::q))=some (innerAmbient++innerLoop) := by
        simpa only [List.append_assoc,List.singleton_append] using innerBodyEval
      rw [innerBodyEval',Option.bind_some,localArgEval,Option.map_some,innerAmbientEq] at equal
      simpa only [newLoop,List.append_assoc,List.cons_append,List.singleton_append] using equal
    have sameAmbient : wantedAmbient=ambient := Option.some.inj (wantedAmbientEval.symm.trans currentAmbientEval)
    have sameLoop : wantedLoop=newLoop := by
      have equal := Option.some.inj (wantedBodyEval.symm.trans newLeafEval)
      rw [sameAmbient] at equal
      exact List.append_cancel_left equal
    have sameBinder : wantedBinder=binder := by
      have equal := Option.some.inj (wantedFinish.symm.trans (sameAmbient ▸ finish))
      have wired := congrArg (fun endpoint => g.wire endpoint) equal
      simp only [Pairing.involutive] at wired
      exact congrArg Sigma.fst (Sum.inl.inj wired)
    obtain ⟨outerWalk,_outerWalkEval⟩ := allWalks outerRoute
    obtain ⟨outerFinish,outerTrail,outerTrailEval⟩ := selection.syntax_evaluation initial matching allWalks routes outerLookup
    obtain ⟨n,outerLast,outerFinishEq⟩ := outerTrail.image.lam_finish
    obtain ⟨m,walkLast,walkOrigin⟩ := outerWalk.image.lambda_origin
    have atoms : n=m := Option.some.inj (outerLast.symm.trans walkLast)
    have sameFinish := outerFinishEq.trans ((congrArg (fun n => SourcePort.lamContext (.atom n)) atoms).trans (congrArg SourcePort.lamContext walkOrigin).symm)
    have outerRealizes := realizes_source_eq sameFinish outerTrail.toRealizes
    have sameEndpoint := outerRealizes.unique initial matching outerWalk.toRealizes
    have outerWord : outerTrail.edges=ambient := Option.some.inj (outerTrailEval.symm.trans ambientEval)
    have outerEndpoint : outerTrail.toEndpoint=.inl ⟨binder,ctx⟩ := by
      have equal := outerTrail.last.symm.trans (outerWord ▸ finish)
      have wired := congrArg (fun endpoint => g.wire endpoint) (Option.some.inj equal)
      simpa only [Pairing.involutive] using wired
    have leftRealizes := outerWalk.toRealizes
    rw [←sameEndpoint,outerEndpoint] at leftRealizes
    obtain ⟨bodyPort,bodyRole,bodyEndpoint⟩ := lambda_departure initial matching leftRealizes preTrail.fromRealizes
    have preHead : pre.head?=some (.inl ⟨binder,bodyPort⟩) := preTrail.head.trans (congrArg some bodyEndpoint)
    obtain ⟨middle,preSplit⟩ := List.head?_eq_some_iff.mp preHead
    have appRoot : (ambient++pre).head?=some (.inr (.inl root)) := by
      have root := outerTrail.rooted
      rw [outerWord] at root
      simp only [List.head?_append,root,Option.some_or]
    have appEnd : (ambient++pre).getLast?=some (g.wire (.inl ⟨beta.app,beta.appCtx⟩)) := by
      simp only [List.getLast?_append,preEnd,Option.some_or]
    have innerEval' : current.sourceTrail selection.atomWord beta.principal beta.reverseRoute
        ((outer++(.body::p))++[.fn])=some ((ambient++pre)++beta.principal) := by
      simpa only [innerAmbientEq] using innerEval
    have innerBodyEval' : current.sourceTrail selection.atomWord beta.principal beta.reverseRoute
        (((outer++(.body::p))++[.fn])++(.body::q))=some ((ambient++pre)++beta.principal++innerLoop) := by
      simpa only [innerAmbientEq] using innerBodyEval
    have oldOuterEval' : current.sourceTrail selection.atomWord beta.principal beta.reverseRoute
        (outer++(.body::(p++(.arg::r))))=some ((ambient++pre)++beta.argEnd::tail) := by
      simpa only [outerLoopEq,List.append_assoc] using oldOuterEval
    have actualWhole : BetaDetourBlocks g
        ((ambient++pre)++beta.principal++innerLoop++beta.reverseRoute++(beta.argEnd::tail)) input output count := by
      simpa only [sameAmbient,sameLoop,newLoop,List.append_assoc,List.singleton_append] using whole
    have actualBefore : ExpandedLabelling g ambient input seam := by simpa only [sameAmbient] using before
    have shell := typed.internal_copied_assignment selection beta innerLambda occurs outerLookup oldOuterLeaf
      (ambient++pre) innerLoop tail ambient middle innerEval' innerBodyEval' ambientEval oldOuterEval'
      shape role bodyRole finish (by rw [preSplit])
      flow positive balance rootDepth appRoot appEnd last actualWhole actualBefore
    simpa only [sameBinder] using shell
end
end Lamping.AG
