import Lamping.Lamping.HistoryTypedBinders
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

/-- Retained BODY-origin lambdas inherit the shell assertion for the EXACT
caller-supplied assignment. True capture protection reflects the old bound
leaf and preserves its whole word; no new path assignment is constructed
or assumed. This is one branch of the TypedL step, not the whole invariant. -/
theorem TypedSyntaxBinders.retained_lambda_step
    (selection : SourceEdgeSelection original g root) (beta : BetaEdge g)
    {source target body argument oldBody currentBody : LTerm} {site p z : Path}
    {stamp degree oldStamp currentStamp : Labelled.Label}
    (step : StepAt site source target)
    (lookup : source.subterm site=some (.app stamp (.lam degree body) argument))
    (active : selection.evalLabel beta degree=beta.principal)
    (oldLambda : body.subterm p=some (.lam oldStamp oldBody))
    (currentLambda : (LTerm.contract stamp degree body argument).subterm p=some (.lam currentStamp currentBody))
    (currentLeaf : ArgumentOccurrence currentBody.erase z)
    (typed : TypedSyntaxBinders selection beta source)
    {ambient loop : List (Endpoint g)} {binder : N} {ctx : Port (g.label binder).sort}
    (ambientEval : target.sourceTrail selection.atomWord beta.principal beta.reverseRoute (site++p)=some ambient)
    (bodyEval : target.sourceTrail selection.atomWord beta.principal beta.reverseRoute ((site++p)++(.body::z))=some (ambient++loop))
    (shape : (g.label binder).sort=.op .lam) (ctxRole : HEq ctx (Sum.inl () : Port (.op .lam)))
    (finish : ambient.getLast?=some (g.wire (.inl ⟨binder,ctx⟩)))
    {input output seam : Context} {count : Nat}
    (whole : BetaDetourBlocks g (ambient++loop) input output count)
    (before : ExpandedLabelling g ambient input seam) :
    Context.SameShell (g.label binder).index seam output := by
  obtain ⟨oldLeaf,bodyWord⟩ := LTerm.contract_retained_lambda_bound_path selection.atomWord beta.principal beta.reverseRoute
    oldLambda currentLambda currentLeaf
  have oldWholeLambda : source.subterm (site++(.fn::.body::p))=some (.lam oldStamp oldBody) := by
    rw [LTerm.subterm_append,lookup]
    exact oldLambda
  have currentWholeLambda : target.subterm (site++p)=some (.lam currentStamp currentBody) := by
    rw [LTerm.subterm_append,step.contractum_at_site lookup]
    exact currentLambda
  have ambientEq := step.sourceTrail_retained_nonvariable selection.atomWord beta.principal beta.reverseRoute
    lookup active oldLambda (by intros; intro impossible; cases impossible)
  have oldAmbientEval : source.sourceTrail selection.atomWord beta.principal beta.reverseRoute (site++(.fn::.body::p))=some ambient :=
    ambientEq.symm.trans ambientEval
  have leafEq : target.sourceTrail selection.atomWord beta.principal beta.reverseRoute ((site++p)++(.body::z))=
      source.sourceTrail selection.atomWord beta.principal beta.reverseRoute ((site++(.fn::.body::p))++(.body::z)) := by
    rw [lambda_body_eval selection.atomWord beta.principal beta.reverseRoute currentWholeLambda z,
      lambda_body_eval selection.atomWord beta.principal beta.reverseRoute oldWholeLambda z,ambientEq,bodyWord]
  have oldBodyEval : source.sourceTrail selection.atomWord beta.principal beta.reverseRoute
      ((site++(.fn::.body::p))++(.body::z))=some (ambient++loop) := leafEq.symm.trans bodyEval
  exact typed oldWholeLambda oldLeaf oldAmbientEval oldBodyEval shape ctxRole finish whole before
end
end Lamping.AG
