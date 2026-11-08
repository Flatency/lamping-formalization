import Lamping.Lamping.HistoryTypedCopyAssignments
import Lamping.Lamping.HistoryGeneratedCopyStep
import Lamping.Lamping.SupportedLoopRebase
import Lamping.Lambda.CopiedLambdaBodies
import Lamping.Lambda.BetaBoundVariableOrigins
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {original : LTerm}
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

private theorem lambda_body_eval {X : Type} (atoms : Nat → List X) (overWord underWord : List X)
    {term body : LTerm} {p : Path} {stamp : Labelled.Label}
    (lookup : term.subterm p=some (.lam stamp body)) (q : Path) :
    term.sourceTrail atoms overWord underWord (p++(.body::q))=
      (term.sourceTrail atoms overWord underWord p).bind
        (fun ambient => (body.sourceTrail atoms overWord underWord q).map (fun word => ambient++word)) := by
  have atRoot := LTerm.sourceTrail_split atoms overWord underWord lookup []
  simp only [List.append_nil] at atRoot
  rw [LTerm.sourceTrail_split atoms overWord underWord lookup (.body::q),atRoot]
  cases term.sourceStem atoms overWord underWord p <;>
    cases bodyEval : body.sourceTrail atoms overWord underWord q <;>
      simp [LTerm.sourceTrail,LTerm.label,bodyEval,List.append_assoc]

/-- The actual argument-copy TypedL branch. Previous generated/support data
supplies the literal occurrences and ports, while previous TypedL supplies
only OLD shells. The caller's NEW assignment is transported back by the
finite detour assignment lemma, never assumed total or reinterpreted as an
ordinary path. -/theorem TypedSyntaxBinders.copied_lambda_step
    (initial : INIT original) (matching : Matches g root original.erase)
    (selection : SourceEdgeSelection original g root) (beta : BetaEdge g)
    {allowed : Labelled.Label → Prop}
    (allWalks : ∀ {start stamp finish},SelectedSourceRoute (sourceEdges [] .external original) allowed start stamp finish →
      ∃ walk : PhysicalSourceWalk original root beta start stamp finish,walk.edges=selection.evalLabel beta stamp)
    {current target body argument oldBody currentBody : LTerm} {site q r z : Path}
    {stamp degree oldStamp currentStamp : Labelled.Label}
    (routes : SelectedTermRoutes (sourceEdges [] .external original) allowed [] .external current)
    (step : StepAt site current target)
    (lookup : current.subterm site=some (.app stamp (.lam degree body) argument))
    {appId lamId : Labelled.Label} {localCtx : SourcePort}
    (headRoute : SourceRoute (sourceEdges [] .external original) localCtx stamp (.appContext appId))
    (function : SourceRoute (sourceEdges [] .external original) (.appFn appId) degree (.lamContext lamId))
    (ports : BetaSourcePorts original root beta appId lamId)
    (active : selection.evalLabel beta degree=beta.principal)
    (argumentRoutes : SelectedTermRoutes (sourceEdges [] .external original) allowed env (.appArg appId) argument)
    (occurs : ArgumentOccurrence body.erase q)
    (oldLambda : argument.subterm r=some (.lam oldStamp oldBody))
    (currentLambda : (LTerm.contract stamp degree body argument).subterm (q++r)=some (.lam currentStamp currentBody))
    (currentLeaf : ArgumentOccurrence currentBody.erase z)
    (paths : GeneratedSyntaxPaths selection beta current)
    (binders : SupportedSyntaxBinders selection beta current)
    (typed : TypedSyntaxBinders selection beta current)
    {boundary : B → Bool} (flow : FlowBalance g boundary) (positive : boundary root=true)
    {heights : B → Int} (balance : IndexedLevelBalance g heights) (rootDepth : heights root=0)
    {wantedAmbient wantedLoop : List (Endpoint g)} {wantedBinder : N} {wantedCtx : Port (g.label wantedBinder).sort}
    (wantedAmbientEval : target.sourceTrail selection.atomWord beta.principal beta.reverseRoute (site++(q++r))=some wantedAmbient)
    (wantedBodyEval : target.sourceTrail selection.atomWord beta.principal beta.reverseRoute ((site++(q++r))++(.body::z))=some (wantedAmbient++wantedLoop))
    (_wantedShape : (g.label wantedBinder).sort=.op .lam) (_wantedRole : HEq wantedCtx (Sum.inl () : Port (.op .lam)))
    (wantedFinish : wantedAmbient.getLast?=some (g.wire (.inl ⟨wantedBinder,wantedCtx⟩)))
    {input output seam : Context} {count : Nat}
    (whole : BetaDetourBlocks g (wantedAmbient++wantedLoop) input output count)
    (before : ExpandedLabelling g wantedAmbient input seam) :
    Context.SameShell (g.label wantedBinder).index seam output := by
  obtain ⟨stem,stemEval,_stemGen⟩ := paths lookup
  obtain ⟨_appFinish,appTrail,appEval⟩ := selection.syntax_evaluation initial matching allWalks routes lookup
  have appWord : appTrail.edges=stem := Option.some.inj (appEval.symm.trans stemEval)
  have stemEnd : stem.getLast?=some (g.wire (.inl ⟨beta.app,beta.appCtx⟩)) := by
    rw [←appWord]
    exact ports.app_trail_last initial matching headRoute appTrail
  have lambdaLookup : current.subterm (site++[.fn])=some (.lam degree body) := by
    rw [LTerm.subterm_append,lookup]
    rfl
  obtain ⟨ambient,outerLoop,outerBinder,outerCtx,ambientEval,bodyEval,outerSupport,_shape,_role,finish⟩ := binders lambdaLookup occurs
  have ambientEq : ambient=stem++beta.principal := by
    have same := redex_function_eval selection.atomWord beta.principal beta.reverseRoute lookup
    rw [stemEval,Option.map_some] at same
    change _=some (stem++selection.evalLabel beta degree) at same
    rw [active,ambientEval] at same
    exact Option.some.inj same
  obtain ⟨_lamFinish,lamTrail,lamEval⟩ := selection.syntax_evaluation initial matching allWalks routes lambdaLookup
  have lamWord : lamTrail.edges=ambient := Option.some.inj (lamEval.symm.trans ambientEval)
  have lamEnd : ambient.getLast?=some (g.wire beta.ctxEnd) := by
    rw [←lamWord]
    exact ports.lam_trail_last initial matching function lamTrail
  have outerBinderEq : outerBinder=beta.lam := by
    have endpoints := congrArg (fun e => g.wire e) (Option.some.inj (finish.symm.trans lamEnd))
    simp only [Pairing.involutive] at endpoints
    exact congrArg Sigma.fst (Sum.inl.inj endpoints)
  obtain ⟨leafSub,leafLookup⟩ := labelled_lookup occurs
  have wholeLeafLookup : current.subterm ((site++[.fn])++(.body::q))=some leafSub := by
    rw [LTerm.subterm_append,lambdaLookup]
    exact leafLookup
  obtain ⟨bodyWord,bodyWordEval,bodyGenerated⟩ := paths wholeLeafLookup
  have bodyWordEq : bodyWord=ambient++outerLoop := Option.some.inj (bodyWordEval.symm.trans bodyEval)
  have outerBodyGenerated : GeneratedExpandedProperPath g root (stem++beta.principal++outerLoop) := by
    simpa only [bodyWordEq,ambientEq] using bodyGenerated
  rw [ambientEq,outerBinderEq] at outerSupport
  obtain ⟨_argFinish,argTrail,argEval⟩ := selection.syntax_evaluation initial matching allWalks argumentRoutes oldLambda
  have argEndpoint : argTrail.fromEndpoint=beta.argEnd := argTrail.fromRealizes.unique initial matching ports.appArgument
  have argHead : argTrail.edges.head?=some beta.argEnd := argTrail.head.trans (congrArg some argEndpoint)
  obtain ⟨pre,argSplit⟩ := List.head?_eq_some_iff.mp argHead
  have localArgEval : argument.sourceTrail selection.atomWord beta.principal beta.reverseRoute r=some (beta.argEnd::pre) := by
    rw [argEval,argSplit]
  have oldWholeLambda : current.subterm (site++(.arg::r))=some (.lam oldStamp oldBody) := by
    rw [LTerm.subterm_append,lookup]
    exact oldLambda
  have oldLambdaBare : subtermAt argument.erase r=some (.lam oldBody.erase) := by
    rw [←LTerm.erase_subterm,oldLambda]
    rfl
  have newLeafBare : subtermAt (Lambda.contract body.erase argument.erase) ((q++r)++(.body::z))=some (.var (binderDepth z)) := by
    rw [←LTerm.erase_contract stamp degree,←LTerm.erase_subterm,LTerm.subterm_append,currentLambda,Option.bind_some]
    simpa only [LTerm.subterm,LTerm.erase_subterm] using currentLeaf
  have oldLeaf := (Lambda.contract_copied_lambda_bound_variable_iff occurs oldLambdaBare z).mp newLeafBare
  obtain ⟨oldAmbient,loop,binder,ctx,oldAmbientEval,oldLeafEval,support,shape,role,oldEnd⟩ := binders oldWholeLambda oldLeaf
  have actualSplit : oldAmbient=stem++beta.argEnd::pre := by
    have equation := redex_argument_eval selection.atomWord beta.principal beta.reverseRoute lookup r
    rw [stemEval,Option.bind_some,localArgEval,Option.map_some,oldAmbientEval] at equation
    exact Option.some.inj equation
  have copied := support
  rw [actualSplit] at copied

  let newAmbient := stem++beta.principal++outerLoop++beta.reverseRoute++[beta.argEnd]++pre
  have newAmbientEval : target.sourceTrail selection.atomWord beta.principal beta.reverseRoute (site++(q++r))=some newAmbient := by
    rw [step.sourceTrail_copy_splice selection.atomWord beta.principal beta.reverseRoute lookup active occurs r]
    have bodyEval' : current.sourceTrail selection.atomWord beta.principal beta.reverseRoute (site++(.fn::.body::q))=
        some (ambient++outerLoop) := by simpa only [List.append_assoc,List.singleton_append] using bodyEval
    rw [bodyEval',Option.bind_some,localArgEval,Option.map_some,ambientEq]
    simp only [newAmbient,List.append_assoc,List.singleton_append]
  obtain ⟨rho,renameBody⟩ := LTerm.contract_copied_lambda_body_rename occurs oldLambda currentLambda
  have sameBodyWord : currentBody.sourceTrail selection.atomWord beta.principal beta.reverseRoute z=
      oldBody.sourceTrail selection.atomWord beta.principal beta.reverseRoute z := by
    rw [renameBody,LTerm.sourceTrail_rename]
  obtain ⟨oldSub,oldSubLookup⟩ := labelled_lookup oldLeaf
  obtain ⟨relativeWord,relativeEval⟩ := LTerm.sourceTrail_exists selection.atomWord beta.principal beta.reverseRoute oldSubLookup
  have loopEq : relativeWord=loop := by
    have equation := lambda_body_eval selection.atomWord beta.principal beta.reverseRoute oldWholeLambda z
    rw [oldAmbientEval,Option.bind_some,relativeEval,Option.map_some,oldLeafEval] at equation
    exact (List.append_cancel_left (Option.some.inj equation)).symm
  have newRelativeEval : currentBody.sourceTrail selection.atomWord beta.principal beta.reverseRoute z=some loop := by
    rw [sameBodyWord,relativeEval,loopEq]
  have newWholeLambda : target.subterm (site++(q++r))=some (.lam currentStamp currentBody) := by
    rw [LTerm.subterm_append,step.contractum_at_site lookup]
    exact currentLambda
  have newLeafEval : target.sourceTrail selection.atomWord beta.principal beta.reverseRoute ((site++(q++r))++(.body::z))=
      some (newAmbient++loop) := by
    rw [lambda_body_eval selection.atomWord beta.principal beta.reverseRoute newWholeLambda z,newAmbientEval,Option.bind_some,newRelativeEval,Option.map_some]
  have newEnd : newAmbient.getLast?=some (g.wire (.inl ⟨binder,ctx⟩)) := by
    rw [actualSplit] at oldEnd
    cases last : pre.getLast? <;>
      simpa only [newAmbient,List.getLast?_append,List.getLast?_cons,last,Option.some_or] using oldEnd
  have sameAmbient : wantedAmbient=newAmbient := Option.some.inj (wantedAmbientEval.symm.trans newAmbientEval)
  have sameLoop : wantedLoop=loop := by
    have equal := Option.some.inj (wantedBodyEval.symm.trans newLeafEval)
    rw [sameAmbient] at equal
    exact List.append_cancel_left equal
  have sameBinder : wantedBinder=binder := by
    have equal := Option.some.inj (wantedFinish.symm.trans (sameAmbient ▸ newEnd))
    have wired := congrArg (fun endpoint => g.wire endpoint) equal
    simp only [Pairing.involutive] at wired
    exact congrArg Sigma.fst (Sum.inl.inj wired)
  have rooted : stem.head?=some (.inr (.inl root)) := by
    rw [←appWord]
    exact appTrail.rooted
  obtain ⟨_,outerLoopEnd⟩ := outerSupport.beta_endpoints beta rfl
  have outerEval : current.sourceTrail selection.atomWord beta.principal beta.reverseRoute (site++[.fn])=
      some (stem++beta.principal) := by simpa only [ambientEq] using ambientEval
  have outerBodyEval : current.sourceTrail selection.atomWord beta.principal beta.reverseRoute
      ((site++[.fn])++(.body::q))=some (stem++beta.principal++outerLoop) := by
    simpa only [ambientEq] using bodyEval
  have argumentEval : current.sourceTrail selection.atomWord beta.principal beta.reverseRoute (site++(.arg::r))=
      some (stem++beta.argEnd::pre) := by simpa only [actualSplit] using oldAmbientEval
  have argumentBodyEval : current.sourceTrail selection.atomWord beta.principal beta.reverseRoute
      ((site++(.arg::r))++(.body::z))=some (stem++beta.argEnd::(pre++loop)) := by
    simpa only [actualSplit,List.append_assoc,List.cons_append] using oldLeafEval
  have actualWhole : BetaDetourBlocks g
      (stem++beta.principal++outerLoop++beta.reverseRoute++(beta.argEnd::(pre++loop))) input output count := by
    simpa only [sameAmbient,sameLoop,newAmbient,List.append_assoc,List.singleton_append] using whole
  have actualBefore : ExpandedLabelling g
      (stem++beta.principal++outerLoop++beta.reverseRoute++(beta.argEnd::pre)) input seam := by
    simpa only [sameAmbient,newAmbient,List.append_assoc,List.singleton_append] using before
  have shell := typed.copied_assignment selection beta lambdaLookup occurs oldWholeLambda oldLeaf
    stem outerLoop pre loop outerEval outerBodyEval argumentEval argumentBodyEval shape role
    (by simpa only [actualSplit] using oldEnd) flow positive balance rootDepth rooted stemEnd outerLoopEnd actualWhole actualBefore
  simpa only [sameBinder] using shell
end
end Lamping.AG
