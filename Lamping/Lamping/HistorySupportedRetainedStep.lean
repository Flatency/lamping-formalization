import Lamping.Lamping.HistoryGeneratedInvariants
import Lamping.Lamping.RetainedLambdaEvaluation
import Lamping.Lamping.ContextualSourceEvaluation
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {original : LTerm}

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

/-- A retained BODY-origin lambda keeps its previous support tree under an
actual contraction. Its current bound leaf is reflected to the old body;
no old bound-leaf, target loop or target support certificate is assumed. -/
theorem SupportedSyntaxBinders.retained_lambda_step
    (selection : SourceEdgeSelection original g root) (beta : BetaEdge g)
    {source target body argument oldBody currentBody : LTerm} {site p z : Path}
    {stamp degree oldStamp currentStamp : Labelled.Label}
    (step : StepAt site source target)
    (lookup : source.subterm site=some (.app stamp (.lam degree body) argument))
    (active : selection.evalLabel beta degree=beta.principal)
    (oldLambda : body.subterm p=some (.lam oldStamp oldBody))
    (currentLambda : (LTerm.contract stamp degree body argument).subterm p=some (.lam currentStamp currentBody))
    (currentLeaf : ArgumentOccurrence currentBody.erase z)
    (binders : SupportedSyntaxBinders selection beta source) :
    ∃ (ambient loop : List (Endpoint g)) (binder : N) (ctx : Port (g.label binder).sort),
      target.sourceTrail selection.atomWord beta.principal beta.reverseRoute (site++p)=some ambient ∧
      target.sourceTrail selection.atomWord beta.principal beta.reverseRoute ((site++p)++(.body::z))=some (ambient++loop) ∧
      SupportedExpandedBindingLoop g root ambient binder loop ∧
      (g.label binder).sort=.op .lam ∧HEq ctx (Sum.inl () : Port (.op .lam)) ∧
      ambient.getLast?=some (g.wire (.inl ⟨binder,ctx⟩)) := by
  obtain ⟨oldLeaf,bodyWord⟩ := LTerm.contract_retained_lambda_bound_path selection.atomWord beta.principal beta.reverseRoute
    oldLambda currentLambda currentLeaf
  have oldWholeLambda : source.subterm (site++(.fn::.body::p))=some (.lam oldStamp oldBody) := by
    rw [LTerm.subterm_append,lookup]
    exact oldLambda
  have currentWholeLambda : target.subterm (site++p)=some (.lam currentStamp currentBody) := by
    rw [LTerm.subterm_append,step.contractum_at_site lookup]
    exact currentLambda
  obtain ⟨ambient,loop,binder,ctx,ambientEval,leafEval,support,shape,role,finish⟩ := binders oldWholeLambda oldLeaf
  have ambientEq := step.sourceTrail_retained_nonvariable selection.atomWord beta.principal beta.reverseRoute
    lookup active oldLambda (by intros; intro impossible; cases impossible)
  have currentAmbientEval : target.sourceTrail selection.atomWord beta.principal beta.reverseRoute (site++p)=some ambient :=
    ambientEq.trans ambientEval
  have leafEq : target.sourceTrail selection.atomWord beta.principal beta.reverseRoute ((site++p)++(.body::z))=
      source.sourceTrail selection.atomWord beta.principal beta.reverseRoute ((site++(.fn::.body::p))++(.body::z)) := by
    rw [lambda_body_eval selection.atomWord beta.principal beta.reverseRoute currentWholeLambda z,
      lambda_body_eval selection.atomWord beta.principal beta.reverseRoute oldWholeLambda z,ambientEq,bodyWord]
  exact ⟨ambient,loop,binder,ctx,currentAmbientEval,leafEq.trans leafEval,support,shape,role,finish⟩
end
end Lamping.AG
