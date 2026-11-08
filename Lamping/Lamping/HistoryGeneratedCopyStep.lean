import Lamping.Lamping.HistoryGeneratedInvariants
import Lamping.Lamping.CurrentRedexPorts
import Lamping.Lamping.ContextualSourceEvaluation
import Lamping.Lamping.SupportedLoopPorts
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

/-- The copied-position case of the P step. P and L here are PREVIOUS-state
induction hypotheses. App/argument/binder geometry and all literal prefix
splits are reconstructed from real selected routes and their physical walks. -/
private theorem generated_copy
    (initial : INIT original) (matching : Matches g root original.erase)
    (selection : SourceEdgeSelection original g root) (beta : BetaEdge g)
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
    (paths : GeneratedSyntaxPaths selection beta current)
    (binders : SupportedSyntaxBinders selection beta current) :
    ∃ word,target.sourceTrail selection.atomWord beta.principal beta.reverseRoute (site++(q++r))=some word ∧
      GeneratedExpandedProperPath g root word := by
  obtain ⟨stem,stemEval,_stemGen⟩ := paths lookup
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
  obtain ⟨argWord,argWordEval,argGenerated⟩ := paths argLookup
  have wholeArgEval := redex_argument_eval selection.atomWord beta.principal beta.reverseRoute lookup r
  rw [stemEval,Option.bind_some,localArgEval,Option.map_some,argWordEval] at wholeArgEval
  have argWordEq : argWord=stem++beta.argEnd::suffix := Option.some.inj wholeArgEval
  have argumentGenerated : GeneratedExpandedProperPath g root (stem++beta.argEnd::suffix) := argWordEq ▸ argGenerated
  obtain ⟨leafSub,leafLookup⟩ := labelled_lookup occurs
  have wholeLeafLookup : current.subterm ((site++[.fn])++(.body::q))=some leafSub := by
    rw [LTerm.subterm_append,lambdaLookup]
    exact leafLookup
  obtain ⟨leafWord,leafWordEval,leafGenerated⟩ := paths wholeLeafLookup
  have leafWordEq : leafWord=ambient++loop := Option.some.inj (leafWordEval.symm.trans leafEval)
  have bodyGenerated : GeneratedExpandedProperPath g root (ambient++loop) := leafWordEq ▸ leafGenerated
  have generated := support.insert_at_beta beta stem suffix ambientEq binderEq argumentGenerated bodyGenerated stemEnd
  refine ⟨stem++beta.principal++loop++beta.reverseRoute++[beta.argEnd]++suffix,?_,generated⟩
  rw [step.sourceTrail_copy_splice selection.atomWord beta.principal beta.reverseRoute lookup active occurs r]
  have leafEval' : current.sourceTrail selection.atomWord beta.principal beta.reverseRoute (site++(.fn::.body::q))=
      some (ambient++loop) := by simpa only [List.append_assoc,List.singleton_append] using leafEval
  rw [leafEval',Option.bind_some,localArgEval,Option.map_some,ambientEq]
  simp only [List.append_assoc,List.singleton_append]
end
end Lamping.AG

namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i : Nat}

theorem PathSite.selected_principal_word_at
    (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
    {root : B} {original : LTerm} (initial : INIT original) (matching : Matches site.net root original.erase)
    (selection : SourceEdgeSelection original site.net root) (beta : BetaEdge site.net)
    (app : beta.app=.inr (.inl ())) (lam : beta.lam=.inr (.inr ()))
    {degree : Labelled.Label} (selected : SelectedDegree original (site.betaSyntaxFiber root original.erase) degree) :
    selection.evalLabel beta degree=beta.principal := by
  obtain ⟨other,otherApp,otherLam,allWords⟩ := site.selected_principal_word initial matching
  obtain ⟨n,atomic⟩ := selected.atomic initial
  obtain ⟨name,member,_degreeAt⟩ := selected
  obtain ⟨redex,source,_name,sourceApp,sourceLam⟩ :=
    (mem_physicalBetaFiberPaths _ _ _ _ _ _).mp member
  have here := source.connection.beta_principal_unique beta (sourceApp.trans app.symm) (sourceLam.trans lam.symm)
  have there := source.connection.beta_principal_unique other (sourceApp.trans otherApp.symm) (sourceLam.trans otherLam.symm)
  calc
    selection.evalLabel beta degree=selection.evalLabel other degree := by rw [atomic]; rfl
    _=other.principal := allWords selection degree ⟨name,member,_degreeAt⟩
    _=beta.principal := there.symm.trans here

/-- The copied-position P case for an ACTUAL next relative-development event.
The shared route interpretation is fixed once outside the history induction.
Only the previous P/L are induction hypotheses; no target generatedness,
loop, application endpoint, argument split, or principal-word equality is input. -/
theorem PathSite.relative_generated_copy_step
    (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
    {root : B} {original : LTerm} (initial : INIT original) (matching : Matches site.net root original.erase)
    (selection : SourceEdgeSelection original site.net root) (beta : BetaEdge site.net)
    (app : beta.app=.inr (.inl ())) (lam : beta.lam=.inr (.inr ()))
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
    (paths : GeneratedSyntaxPaths selection beta current)
    (binders : SupportedSyntaxBinders selection beta current) :
    ∃ word,target.sourceTrail selection.atomWord beta.principal beta.reverseRoute (p++(q++r))=some word ∧
      GeneratedExpandedProperPath site.net root word := by
  have routes := relative_development_selected_routes initial relativeBefore prior
  obtain ⟨_env,_ctx,appId,lamId,headRoute,function,_bodyRoutes,argumentRoutes⟩ := routes.redex_children lookup
  have degreeAt : current.degreeAt p=some degree := by
    simp only [LTerm.degreeAt,lookup,Option.bind_some,LTerm.degree]
  have selected := relative_last_selected_degree initial relativeAfter prior step degreeAt
  obtain ⟨_degreeEq,ports⟩ := allPorts selected function.forget
  have active := site.selected_principal_word_at initial matching selection beta app lam selected
  exact generated_copy initial matching selection beta allWalks routes step lookup
    headRoute.forget function.forget ports active argumentRoutes occurs atArgument paths binders
end
end Lamping.AG
