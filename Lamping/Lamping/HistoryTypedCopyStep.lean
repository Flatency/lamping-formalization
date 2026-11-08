import Lamping.Lamping.HistoryTypedPaths
import Lamping.Lamping.HistoryTypedBinders
import Lamping.Lamping.HistoryGeneratedCopyStep
import Lamping.Lamping.PairedExpandedInsertion
import Lamping.Lamping.ExpandedTransparencySurgery
import Lamping.Lamping.ReachableNesting
namespace Lamping.AG
open Graph Lambda Lambda.Labelled

private def IncomingSourcePort : SourcePort → Prop
  | .appContext _ | .lamContext _ | .lamBind _ | .free _ => True
  | _ => False

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {original : LTerm}

private theorem image_incoming {beta : BetaEdge g}
    (image : SyntaxTrailImage original root beta env ctx target p sub finish edges) :
    IncomingSourcePort finish := by
  induction image with
  | var image => simp only [sourceBinder]; split <;> trivial
  | lam | app => trivial
  | fn _ _ ih | arg _ _ ih | body _ _ ih => exact ih

private theorem label_of_sort {actual : Graph.Label signature} {op : Op}
    (shape : actual.sort=.op op) : actual=label op actual.index := by
  cases actual with
  | mk sort index => cases shape; rfl

private theorem incoming_realizes {finish endpoint}
    (realizes : SourcePortRealizes original g root finish endpoint)
    (incoming : IncomingSourcePort finish) :
    ∃ role level,AtProperRole g root endpoint role level ∧role.incoming := by
  cases realizes with
  | external => cases incoming
  | departure lookup sourceRole parent word roles finish => cases sourceRole <;> cases incoming
  | appContext lookup access word shape role finish =>
    exact ⟨.appCtx,_,.appCtx _ _ _ (label_of_sort shape) role,trivial⟩
  | lamContext lookup access word shape role finish =>
    exact ⟨.lamCtx,_,.lamCtx _ _ _ (label_of_sort shape) role,trivial⟩
  | binding lookup parent word shape contextRole bindingRole finish =>
    exact ⟨.lamBind,_,.lamBind _ _ _ (label_of_sort shape) bindingRole,trivial⟩
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

private theorem typed_copy
    (initial : INIT original) (matching : Matches g root original.erase)
    (selection : SourceEdgeSelection original g root) (beta : BetaEdge g)
    (inputs : RootInputs g root) {boundary : B → Bool} (flow : FlowBalance g boundary)
    (positive : boundary root=true) {heights : B → Int} (balance : IndexedLevelBalance g heights)
    (rootDepth : heights root=0) (transparency : Transparency g root)
    {allowed : Labelled.Label → Prop}
    (allWalks : ∀ {start stamp finish},SelectedSourceRoute (sourceEdges [] .external original) allowed start stamp finish →
      ∃ walk : PhysicalSourceWalk original root beta start stamp finish,walk.edges=selection.evalLabel beta stamp)
    {current target : LTerm} {site q r : Path} {stamp degree : Labelled.Label} {body argument sub : LTerm}
    (routes : SelectedTermRoutes (sourceEdges [] .external original) allowed [] .external current)
    (step : StepAt site current target)
    (lookup : current.subterm site=some (.app stamp (.lam degree body) argument))
    {appId lamId : Labelled.Label} {localCtx : SourcePort}
    (headRoute : SourceRoute (sourceEdges [] .external original) localCtx stamp (.appContext appId))
    (function : SourceRoute (sourceEdges [] .external original) (.appFn appId) degree (.lamContext lamId))
    (ports : BetaSourcePorts original root beta appId lamId)
    (active : selection.evalLabel beta degree=beta.principal)
    (argumentRoutes : SelectedTermRoutes (sourceEdges [] .external original) allowed env (.appArg appId) argument)
    (occurs : ArgumentOccurrence body.erase q) (atArgument : argument.subterm r=some sub)
    (paths : TypedSyntaxPaths selection beta current)
    (binders : SupportedSyntaxBinders selection beta current)
    (typedBinders : TypedSyntaxBinders selection beta current) :
    ∃ word,target.sourceTrail selection.atomWord beta.principal beta.reverseRoute (site++(q++r))=some word ∧
      ∀ requested : Context,∃ output count,BetaDetourBlocks g word requested output count := by
  obtain ⟨stem,stemEval,stemTyped⟩ := paths lookup
  obtain ⟨_appFinish,appTrail,appEval⟩ := selection.syntax_evaluation initial matching allWalks routes lookup
  have appWord : appTrail.edges=stem := Option.some.inj (appEval.symm.trans stemEval)
  have stemEnd : stem.getLast?=some (g.wire (.inl ⟨beta.app,beta.appCtx⟩)) := by
    rw [←appWord]
    exact ports.app_trail_last initial matching headRoute appTrail
  have lambdaLookup : current.subterm (site++[.fn])=some (.lam degree body) := by
    rw [LTerm.subterm_append,lookup]
    rfl
  obtain ⟨ambient,loop,binder,ctx,ambientEval,leafEval,support,_shape,_role,finish⟩ := binders lambdaLookup occurs
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
  have binderEq : binder=beta.lam := by
    have wires := Option.some.inj (finish.symm.trans lamEnd)
    have endpoints := congrArg (fun e => g.wire e) wires
    simp only [Pairing.involutive] at endpoints
    exact congrArg Sigma.fst (Sum.inl.inj endpoints)
  obtain ⟨_finish,argTrail,argEval⟩ := selection.syntax_evaluation initial matching allWalks argumentRoutes atArgument
  have argEndpoint : argTrail.fromEndpoint=beta.argEnd := argTrail.fromRealizes.unique initial matching ports.appArgument
  have argHead : argTrail.edges.head?=some beta.argEnd := argTrail.head.trans (congrArg some argEndpoint)
  obtain ⟨suffix,argSplit⟩ := List.head?_eq_some_iff.mp argHead
  have localArgEval : argument.sourceTrail selection.atomWord beta.principal beta.reverseRoute r=some (beta.argEnd::suffix) := by
    rw [argEval,argSplit]
  have argLookup : current.subterm (site++(.arg::r))=some sub := by
    rw [LTerm.subterm_append,lookup]
    exact atArgument
  obtain ⟨argWord,argWordEval,argTyped⟩ := paths argLookup
  have wholeArgEval := redex_argument_eval selection.atomWord beta.principal beta.reverseRoute lookup r
  rw [stemEval,Option.bind_some,localArgEval,Option.map_some,argWordEval] at wholeArgEval
  have argWordEq : argWord=stem++beta.argEnd::suffix := Option.some.inj wholeArgEval
  have argumentTyped : ∀ requested : Context,∃ output count,
      BetaDetourBlocks g (stem++beta.argEnd::suffix) requested output count := by
    intro requested
    obtain ⟨output,count,assigned⟩ := argTyped requested
    exact ⟨output,count,argWordEq ▸ assigned⟩
  obtain ⟨leafSub,leafLookup⟩ := labelled_lookup occurs
  have wholeLeafLookup : current.subterm ((site++[.fn])++(.body::q))=some leafSub := by
    rw [LTerm.subterm_append,lambdaLookup]
    exact leafLookup
  obtain ⟨endBody,bodyCount,bodyStream⟩ := paths.at_word wholeLeafLookup leafEval Context.empty
  obtain ⟨seam,_stemCount,stemStream⟩ := stemTyped Context.empty
  have ambientLabels : ExpandedLabelling g ambient Context.empty seam := by
    rw [ambientEq]
    apply (stemStream.labelling g).splice stemEnd (beta.principal_labeling seam).expanded beta.principalStart
    simpa only [Pairing.involutive] using ExpandedTurn.ordinary (beta.app_fun_turn seam)
  have shell := typedBinders lambdaLookup occurs (binder:=beta.lam) (ctx:=beta.lamCtx)
    ambientEval leafEval (congrArg Graph.Label.sort beta.lamLabel) beta.lamCtx_role lamEnd bodyStream ambientLabels
  obtain ⟨loopStart,loopEnd⟩ := support.beta_endpoints beta binderEq
  obtain ⟨loopTail,loopSplit⟩ := List.head?_eq_some_iff.mp loopStart
  obtain ⟨_leafFinish,leafTrail,leafTrailEval⟩ := selection.syntax_evaluation initial matching allWalks routes wholeLeafLookup
  have leafTrailWord : leafTrail.edges=ambient++loop := Option.some.inj (leafTrailEval.symm.trans leafEval)
  have bodyForward : ExpandedForward g (ambient++loop) := leafTrailWord ▸ leafTrail.forward
  have bodyEnd : (ambient++loop).getLast?=some (g.wire (.inl ⟨beta.lam,beta.lamBind⟩)) := by
    simp only [List.getLast?_append,loopEnd,Option.some_or]
  obtain ⟨binding,sameBinder⟩ := expanded_binding_suffix beta.lam beta.lamCtx beta.lamBody beta.lamBind
    (congrArg Graph.Label.sort beta.lamLabel) beta.lamCtx_role beta.lamBody_role beta.lamBind_role
    ambient loopTail Context.empty seam endBody
    (by simpa only [loopSplit] using bodyStream.labelling g)
    (by simpa only [loopSplit] using bodyForward) ambientLabels lamEnd
    (by simpa only [loopSplit] using bodyEnd) shell
  have bindingAtLoop : ∃ binding' : ExpandedBindingLoop g loop seam endBody,binding'.binder=beta.lam := by
    rw [loopSplit]
    exact ⟨binding,sameBinder⟩
  obtain ⟨binding',binder'⟩ := bindingAtLoop
  obtain ⟨role,level,atTerminal,incoming⟩ := incoming_realizes argTrail.toRealizes (image_incoming argTrail.image)
  have argEnd : (beta.argEnd::suffix).getLast?=some (g.wire argTrail.toEndpoint) := by
    rw [←argSplit]
    exact argTrail.last
  have rooted : stem.head?=some (.inr (.inl root)) := by rw [←appWord]; exact appTrail.rooted
  have bodyStream' : BetaDetourBlocks g (stem++beta.principal++loop) Context.empty endBody bodyCount := by
    simpa only [ambientEq,List.append_assoc] using bodyStream
  obtain ⟨count,inserted⟩ := inputs.insert_expanded_paired_body flow positive balance rootDepth
    (balance.nesting root rootDepth) transparency beta stem loop suffix argumentTyped bodyStream'
    (stemStream.labelling g) binding' binder' rooted stemEnd argTrail.toEndpoint role level argEnd atTerminal incoming
  refine ⟨stem++beta.principal++loop++beta.reverseRoute++[beta.argEnd]++suffix,?_,?_⟩
  · rw [step.sourceTrail_copy_splice selection.atomWord beta.principal beta.reverseRoute lookup active occurs r]
    have leafEval' : current.sourceTrail selection.atomWord beta.principal beta.reverseRoute (site++(.fn::.body::q))=
        some (ambient++loop) := by simpa only [List.append_assoc,List.singleton_append] using leafEval
    rw [leafEval',Option.bind_some,localArgEval,Option.map_some,ambientEq]
    simp only [List.append_assoc,List.singleton_append]
  · intro requested
    obtain ⟨output,_core,assigned⟩ := inserted requested
    exact ⟨output,count,assigned⟩
end
end Lamping.AG

namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i : Nat}

/-- Actual next-event copied paths are assigned for every root input from
previous typed paths and the previous specified-binder shell property. The
actual loop assignment is constructed; no new-path assignment is a premise. -/
theorem PathSite.relative_typed_copy_step
    (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
    {root : B} {original : LTerm} (initial : INIT original) (matching : Matches site.net root original.erase)
    (selection : SourceEdgeSelection original site.net root) (beta : BetaEdge site.net)
    (app : beta.app=.inr (.inl ())) (lam : beta.lam=.inr (.inr ()))
    (inputs : RootInputs site.net root) {boundary : B → Bool} (flow : FlowBalance site.net boundary)
    (positive : boundary root=true) {heights : B → Int} (balance : IndexedLevelBalance site.net heights)
    (rootDepth : heights root=0) (transparency : Transparency site.net root)
    (allPorts : ∀ {degree appId lamId},SelectedDegree original (site.betaSyntaxFiber root original.erase) degree →
      SourceRoute (sourceEdges [] .external original) (.appFn appId) degree (.lamContext lamId) →
      degree=lamId ∧BetaSourcePorts original root beta appId lamId)
    (allWalks : ∀ {start stamp finish},SelectedSourceRoute (sourceEdges [] .external original)
      (SelectedDegree original (site.betaSyntaxFiber root original.erase)) start stamp finish →
      ∃ walk : PhysicalSourceWalk original root beta start stamp finish,walk.edges=selection.evalLabel beta stamp)
    {ps : List Path} {p q r : Path} {current target : LTerm} {markedBefore markedAfter : Marked}
    (relativeBefore : Marked.RelativeHistory ps (Marked.mark (site.betaSyntaxFiber root original.erase) original.erase) markedBefore)
    (relativeAfter : Marked.RelativeHistory (ps++[p]) (Marked.mark (site.betaSyntaxFiber root original.erase) original.erase) markedAfter)
    (prior : History ps original current) (step : StepAt p current target)
    {stamp degree : Labelled.Label} {body argument sub : LTerm}
    (lookup : current.subterm p=some (.app stamp (.lam degree body) argument))
    (occurs : ArgumentOccurrence body.erase q) (atArgument : argument.subterm r=some sub)
    (paths : TypedSyntaxPaths selection beta current)
    (binders : SupportedSyntaxBinders selection beta current)
    (typedBinders : TypedSyntaxBinders selection beta current) :
    ∃ word,target.sourceTrail selection.atomWord beta.principal beta.reverseRoute (p++(q++r))=some word ∧
      ∀ requested : Context,∃ output count,BetaDetourBlocks site.net word requested output count := by
  have routes := relative_development_selected_routes initial relativeBefore prior
  obtain ⟨_env,_ctx,appId,lamId,headRoute,function,_bodyRoutes,argumentRoutes⟩ := routes.redex_children lookup
  have degreeAt : current.degreeAt p=some degree := by
    simp only [LTerm.degreeAt,lookup,Option.bind_some,LTerm.degree]
  have selected := relative_last_selected_degree initial relativeAfter prior step degreeAt
  obtain ⟨_degreeEq,ports⟩ := allPorts selected function.forget
  have active := site.selected_principal_word_at initial matching selection beta app lam selected
  exact typed_copy initial matching selection beta inputs flow positive balance rootDepth transparency allWalks routes step lookup
    headRoute.forget function.forget ports active argumentRoutes occurs atArgument paths binders typedBinders
end
end Lamping.AG
