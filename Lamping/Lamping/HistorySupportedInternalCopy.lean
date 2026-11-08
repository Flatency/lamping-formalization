import Lamping.Lamping.HistoryGeneratedCopyStep
import Lamping.Lamping.SupportedLoopPorts
import Lamping.Lambda.NestedBinderCoordinates
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

/-- A lambda surrounding the actual event acquires an expanded supported
loop when its new bound leaf comes from that event's argument. Its previous
residual loop and the inserted loop are read from PREVIOUS L, and the two
rooted body premises from PREVIOUS P. No expanded detour is erased. -/
theorem SupportedSyntaxBinders.internal_copy_step
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
    (paths : GeneratedSyntaxPaths selection beta current)
    (binders : SupportedSyntaxBinders selection beta current) :
    ∃ (ambient loop : List (Endpoint g)) (binder : N) (ctx : Port (g.label binder).sort),
      target.sourceTrail selection.atomWord beta.principal beta.reverseRoute outer=some ambient ∧
      target.sourceTrail selection.atomWord beta.principal beta.reverseRoute (outer++(.body::(p++(q++r))))=some (ambient++loop) ∧
      SupportedExpandedBindingLoop g root ambient binder loop ∧
      (g.label binder).sort=.op .lam ∧HEq ctx (Sum.inl () : Port (.op .lam)) ∧
      ambient.getLast?=some (g.wire (.inl ⟨binder,ctx⟩)) := by
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
  | lam _ bodyRoutes =>
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
    obtain ⟨oldLeafSub,oldLeafLookup⟩ := labelled_lookup oldOuterLeaf
    have oldWholeLeaf : current.subterm (outer++(.body::(p++(.arg::r))))=some oldLeafSub := by
      rw [LTerm.subterm_append,outerLookup]
      exact oldLeafLookup
    obtain ⟨oldWord,oldWordEval,oldGenerated⟩ := paths oldWholeLeaf
    have oldWordEq : oldWord=ambient++outerLoop := Option.some.inj (oldWordEval.symm.trans oldOuterEval)
    have previousBody : GeneratedExpandedProperPath g root (ambient++(pre++beta.argEnd::tail)) := by
      simpa only [oldWordEq,outerLoopEq] using oldGenerated
    obtain ⟨nestedSub,nestedLookup⟩ := labelled_lookup occurs
    have nestedWholeLookup : current.subterm (((outer++(.body::p))++[.fn])++(.body::q))=some nestedSub := by
      rw [LTerm.subterm_append,innerLambda]
      exact nestedLookup
    obtain ⟨nestedWord,nestedWordEval,nestedGenerated⟩ := paths nestedWholeLookup
    have nestedWordEq : nestedWord=innerAmbient++innerLoop := Option.some.inj (nestedWordEval.symm.trans innerBodyEval)
    have nestedBody : GeneratedExpandedProperPath g root (ambient++pre++beta.principal++innerLoop) := by
      simpa only [nestedWordEq,innerAmbientEq] using nestedGenerated
    rw [outerLoopEq] at outerSupport
    have newSupport := SupportedExpandedBindingLoop.insert ambient binder beta pre innerLoop tail
      outerSupport nestedSupport previousBody nestedBody preEnd start last
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
    exact ⟨ambient,newLoop,binder,ctx,currentAmbientEval,newLeafEval,newSupport,shape,role,finish⟩
end
end Lamping.AG
