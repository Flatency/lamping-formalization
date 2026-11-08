import Lamping.Lamping.HistoryGeneratedPathStep
import Lamping.Lamping.HistorySupportedRetainedStep
import Lamping.Lamping.HistorySupportedCopyStep
import Lamping.Lamping.HistorySupportedInternalCopy
import Lamping.Lambda.LabelArgumentBinderScope
import Lamping.Lambda.LabelRegions
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}
private theorem outside_descendant {site parent : Path} (apart : DisjointPositions site parent) (suffix : Path) :
    ¬∃ tail,parent++suffix=site++tail := by
  rintro ⟨tail,equal⟩
  rcases List.append_eq_append_iff.mp equal with ⟨extra,headEq,_⟩ | ⟨extra,headEq,_⟩
  · exact apart.2 ⟨extra,headEq⟩
  · exact apart.1 ⟨extra,headEq⟩
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

end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i : Nat}

/-- The binder component advances through an ACTUAL event. Lambda and bound
leaf positions are classified from the real contraction. Previous supports
are inherited, genuinely rebased for argument copies, or expanded using the
previous residual/nested rooted bodies; no target support is assumed. -/
theorem PathSite.relative_supported_binders_step
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
    {ps : List Path} {p : Path} {current target : LTerm} {markedBefore markedAfter : Marked}
    (relativeBefore : Marked.RelativeHistory ps (Marked.mark (site.betaSyntaxFiber root original.erase) original.erase) markedBefore)
    (relativeAfter : Marked.RelativeHistory (ps++[p]) (Marked.mark (site.betaSyntaxFiber root original.erase) original.erase) markedAfter)
    (prior : History ps original current) (step : StepAt p current target)
    {stamp degree : Labelled.Label} {body argument : LTerm}
    (lookup : current.subterm p=some (.app stamp (.lam degree body) argument))
    (paths : GeneratedSyntaxPaths selection beta current)
    (binders : SupportedSyntaxBinders selection beta current) :
    SupportedSyntaxBinders selection beta target := by
  classical
  have degreeAt : current.degreeAt p=some degree := by
    simp only [LTerm.degreeAt,lookup,Option.bind_some,LTerm.degree]
  have selected := relative_last_selected_degree initial relativeAfter prior step degreeAt
  have active := site.selected_principal_word_at initial matching selection beta app lam selected
  have routes := relative_development_selected_routes initial relativeBefore prior
  obtain ⟨_env,_ctx,appId,lamId,headRoute,function,_bodyRoutes,argumentRoutes⟩ := routes.redex_children lookup
  obtain ⟨_degreeEq,ports⟩ := allPorts selected function.forget
  intro lambdaPos currentStamp currentBody atLambda z currentLeaf
  by_cases below : ∃ relativePos,lambdaPos=p++relativePos
  · obtain ⟨relativePos,positionEq⟩ := below
    subst lambdaPos
    have currentLambda : (LTerm.contract stamp degree body argument).subterm relativePos=some (.lam currentStamp currentBody) := by
      rw [LTerm.subterm_append,step.contractum_at_site lookup,Option.bind_some] at atLambda
      exact atLambda
    rcases LTerm.contract_lambda_position_origins currentLambda with
      ⟨oldStamp,oldBody,oldLambda,_tau,_bodyEq⟩ | ⟨q,r,oldStamp,oldBody,split,occurs,oldLambda,_rho,_bodyEq⟩
    · exact SupportedSyntaxBinders.retained_lambda_step selection beta step lookup active oldLambda currentLambda currentLeaf binders
    · subst relativePos
      exact SupportedSyntaxBinders.copied_lambda_step initial matching selection beta allWalks routes step lookup
        headRoute.forget function.forget ports active argumentRoutes occurs oldLambda currentLambda currentLeaf paths binders
  · by_cases ancestor : ∃ rest,p=lambdaPos++rest
    · obtain ⟨rest,pathEq⟩ := ancestor
      have nonempty : rest≠[] := by
        intro empty
        apply below
        refine ⟨[],?_⟩
        simpa only [empty,List.append_nil] using pathEq.symm
      obtain ⟨relativePos,oldBody,restEq,oldLambda⟩ := step.strict_lambda_ancestor atLambda pathEq nonempty
      have localPath : p=(lambdaPos++[.body])++relativePos := by
        simpa only [restEq,List.append_assoc,List.singleton_append] using pathEq
      have oldBodyLookup : current.subterm (lambdaPos++[.body])=some oldBody := by
        rw [LTerm.subterm_append,oldLambda]
        cases oldBody <;> rfl
      have insideStep : StepAt ((lambdaPos++[Step.body])++relativePos) current target := localPath ▸ step
      obtain ⟨result,atResult,localStep⟩ :=
        insideStep.subterm_internal (lambdaPos++[Step.body]) oldBodyLookup
      have currentBodyLookup : target.subterm (lambdaPos++[.body])=some currentBody := by
        rw [LTerm.subterm_append,atLambda]
        cases currentBody <;> rfl
      have resultEq : result=currentBody := Option.some.inj (atResult.symm.trans currentBodyLookup)
      subst result
      have localLookup : oldBody.subterm relativePos=some (.app stamp (.lam degree body) argument) := by
        have global := lookup
        rw [localPath,LTerm.subterm_append,oldBodyLookup,Option.bind_some] at global
        exact global
      rcases localStep.outer_bound_variable_evaluation_origins selection.atomWord beta.principal beta.reverseRoute
          localLookup active currentLeaf with ⟨oldPosition,oldLeaf,sameWord⟩ | ⟨q,r,split,occurs,_argVariable⟩
      · obtain ⟨ambient,loop,binder,ctx,ambientEval,leafEval,support,shape,role,finish⟩ := binders oldLambda oldLeaf
        have ambientEq := step.sourceTrail_outside selection.atomWord beta.principal beta.reverseRoute lambdaPos below
        have newAmbientEval := ambientEq.trans ambientEval
        have leafEq : target.sourceTrail selection.atomWord beta.principal beta.reverseRoute (lambdaPos++(.body::z))=
            current.sourceTrail selection.atomWord beta.principal beta.reverseRoute (lambdaPos++(.body::oldPosition)) := by
          rw [lambda_body_eval selection.atomWord beta.principal beta.reverseRoute atLambda z,
            lambda_body_eval selection.atomWord beta.principal beta.reverseRoute oldLambda oldPosition,ambientEq,sameWord]
        exact ⟨ambient,loop,binder,ctx,newAmbientEval,leafEq.trans leafEval,support,shape,role,finish⟩
      · rw [split]
        have globalStep : StepAt (lambdaPos++(.body::relativePos)) current target := by
          simpa only [List.append_assoc,List.singleton_append] using insideStep
        exact SupportedSyntaxBinders.internal_copy_step initial matching selection beta allWalks routes globalStep localStep oldLambda localLookup
          headRoute.forget function.forget ports active argumentRoutes occurs (by simpa only [split] using currentLeaf) paths binders
    · have apart : DisjointPositions p lambdaPos := ⟨below,ancestor⟩
      have oldLambda : current.subterm lambdaPos=some (.lam currentStamp currentBody) :=
        (step.disjoint_subterm apart).symm.trans atLambda
      obtain ⟨ambient,loop,binder,ctx,ambientEval,leafEval,support,shape,role,finish⟩ := binders oldLambda currentLeaf
      have ambientEq := step.sourceTrail_outside selection.atomWord beta.principal beta.reverseRoute lambdaPos below
      have leafEq := step.sourceTrail_outside selection.atomWord beta.principal beta.reverseRoute (lambdaPos++(.body::z))
        (outside_descendant apart (.body::z))
      exact ⟨ambient,loop,binder,ctx,ambientEq.trans ambientEval,leafEq.trans leafEval,support,shape,role,finish⟩
end
end Lamping.AG
