import Lamping.Lambda.CopiedLambdaBodies
import Lamping.Lambda.ContractumPositionOrigins
import Lamping.Lamping.SourceRouteEvaluation
import Lamping.Lambda.FunctionArgumentOccurrenceReflect
namespace Lamping.Lambda.Labelled.LTerm
/-- A retained old lambda has a body substituted under its protected binder.
The substitution at that exact old path is constructed by descent. -/
theorem subst_retained_lambda_body {oldBody currentBody body : LTerm} {p : Path} {sigma : Nat → SubValue}
    (oldLambda : body.subterm p=some (.lam oldStamp oldBody))
    (currentLambda : (body.subst sigma).subterm p=some (.lam currentStamp currentBody)) :
    ∃ tau,currentBody=oldBody.subst (lift tau) := by
  induction p generalizing body sigma with
  | nil =>
    have oldEq : body=.lam oldStamp oldBody := by simpa only [subterm,Option.some.injEq] using oldLambda
    subst body
    have parts := LTerm.lam.inj (Option.some.inj currentLambda)
    exact ⟨sigma,parts.2.symm⟩
  | cons step rest ih =>
    cases body with
    | var => cases step <;> simp [subterm] at oldLambda
    | app stamp fn arg =>
      cases step with
      | body => simp [subterm] at oldLambda
      | fn | arg => exact ih oldLambda currentLambda
    | lam stamp inner =>
      cases step with
      | fn | arg => simp [subterm] at oldLambda
      | body => exact ih oldLambda currentLambda

/-- The outer beta prefix can change the retained lambda's incoming label,
but its body is still substituted under a real protected binder. -/
theorem contract_retained_lambda_body {oldBody currentBody body argument : LTerm} {p : Path}
    (oldLambda : body.subterm p=some (.lam oldStamp oldBody))
    (currentLambda : (contract beta alpha body argument).subterm p=some (.lam currentStamp currentBody)) :
    ∃ tau,currentBody=oldBody.subst (lift tau) := by
  cases p with
  | nil =>
    have oldEq : body=.lam oldStamp oldBody := by simpa only [subterm,Option.some.injEq] using oldLambda
    subst body
    have parts := LTerm.lam.inj (Option.some.inj currentLambda)
    exact ⟨single (argument.prepend alpha.under),parts.2.symm⟩
  | cons step rest =>
    rw [contract,prepend_subterm_nonempty _ _ (by simp)] at currentLambda
    exact subst_retained_lambda_body oldLambda currentLambda

/-- Protected substitution keeps EVERY label along a genuine protected
variable path. Other substitution slots may contain arbitrary put terms. -/
theorem sourceTrail_subst_protected {X : Type} (atoms : Nat → List X) (overWord underWord : List X)
    {body : LTerm} {p : Path} {k n : Nat} {sigma : Nat → SubValue}
    (lookup : subtermAt body.erase p=some (.var (k+binderDepth p))) (bound : k<n)
    (kept : ∀ i,i<n → sigma i=.keep i) :
    (body.subst sigma).sourceTrail atoms overWord underWord p=
      body.sourceTrail atoms overWord underWord p := by
  induction p generalizing body sigma k n with
  | nil =>
    cases body with
    | app => simp [erase,subtermAt] at lookup
    | lam => simp [erase,subtermAt] at lookup
    | var stamp index =>
      have same : index=k := by simpa only [erase,subtermAt,binderDepth,Nat.add_zero,Option.some.injEq,Term.var.injEq] using lookup
      subst index
      simp only [subst,kept k bound,sourceTrail,label]
  | cons step rest ih =>
    cases body with
    | var => cases step <;> simp [erase,subtermAt] at lookup
    | app stamp fn arg =>
      cases step with
      | body => simp [erase,subtermAt] at lookup
      | fn | arg => simp only [subst,sourceTrail,ih lookup bound kept]
    | lam stamp inner =>
      cases step with
      | fn | arg => simp [erase,subtermAt] at lookup
      | body =>
        have atInner := lookup
        simp only [erase,subtermAt,binderDepth] at atInner
        rw [←Nat.add_assoc,Nat.add_right_comm k (binderDepth rest) 1] at atInner
        have keptLift : ∀ i,i<n+1 → lift sigma i=.keep i := by {
          intro i small
          cases i with
          | zero => rfl
          | succ i => exact (by simp only [lift,kept i (by omega)]) }
        simp only [subst,sourceTrail,ih atInner (Nat.succ_lt_succ bound) keptLift]

private theorem erase_subst_lift (body : LTerm) (sigma : Nat → SubValue) :
    (body.subst (lift sigma)).erase=Lambda.subst (Lambda.liftSub (fun i => (sigma i).erase)) body.erase := by
  rw [erase_subst]
  congr 1
  funext i
  exact erase_lift sigma i

/-- A current bound leaf under a retained lambda already existed at the
SAME old body path. Capture avoidance prevents substituted arguments from
supplying this binder, and its entire relative body trail is unchanged. -/
theorem retained_lambda_bound_path {X : Type} (atoms : Nat → List X) (overWord underWord : List X)
    {oldBody currentBody : LTerm} (sigma : Nat → SubValue)
    (bodyEq : currentBody=oldBody.subst (lift sigma))
    (currentLeaf : ArgumentOccurrence currentBody.erase z) :
    ArgumentOccurrence oldBody.erase z ∧
      currentBody.sourceTrail atoms overWord underWord z=oldBody.sourceTrail atoms overWord underWord z := by
  have oldLeaf : ArgumentOccurrence oldBody.erase z := by
    apply ArgumentOccurrence.subst_reflect (σ:=fun i => (sigma i).erase)
    rw [bodyEq,erase_subst_lift] at currentLeaf
    exact currentLeaf
  refine ⟨oldLeaf,?_⟩
  rw [bodyEq]
  apply sourceTrail_subst_protected atoms overWord underWord (k:=0) (n:=1)
  · simpa only [Nat.zero_add] using oldLeaf
  · decide
  · intro i small
    have zero : i=0 := by omega
    subst i
    rfl

/-- Actual retained BODY-origin lambda interface. Neither the old bound
leaf nor a graph loop/support certificate is a caller premise. -/
theorem contract_retained_lambda_bound_path {X : Type} (atoms : Nat → List X) (overWord underWord : List X)
    {oldBody currentBody body argument : LTerm} {p : Path}
    (oldLambda : body.subterm p=some (.lam oldStamp oldBody))
    (currentLambda : (contract beta alpha body argument).subterm p=some (.lam currentStamp currentBody))
    (currentLeaf : ArgumentOccurrence currentBody.erase z) :
    ArgumentOccurrence oldBody.erase z ∧
      currentBody.sourceTrail atoms overWord underWord z=oldBody.sourceTrail atoms overWord underWord z := by
  obtain ⟨tau,bodyEq⟩ := contract_retained_lambda_body oldLambda currentLambda
  exact retained_lambda_bound_path atoms overWord underWord tau bodyEq currentLeaf
/-- Every actual contractum lambda comes from a retained old body lambda
or a specified argument-copy lambda. Both old shapes and their body
relations are derived, never supplied as origin certificates. -/
theorem contract_lambda_position_origins {body argument currentBody : LTerm} {p : Path}
    (currentLambda : (contract beta alpha body argument).subterm p=some (.lam currentStamp currentBody)) :
    (∃ oldStamp oldBody,body.subterm p=some (.lam oldStamp oldBody) ∧
      ∃ tau,currentBody=oldBody.subst (lift tau)) ∨
    (∃ q r oldStamp oldBody,p=q++r ∧ ArgumentOccurrence body.erase q ∧
      argument.subterm r=some (.lam oldStamp oldBody) ∧ ∃ rho,currentBody=oldBody.rename rho) := by
  have bare : subtermAt (Lambda.contract body.erase argument.erase) p=some (.lam currentBody.erase) := by
    rw [←erase_contract,←erase_subterm,currentLambda]
    rfl
  rcases subtermAt_contract_origins bare with ⟨old,oldLookup,nonvar,shape⟩ |
    ⟨_,_,_,_,_,shape⟩ | ⟨q,r,split,occurs,_⟩
  · cases old with
    | var k => exact False.elim (nonvar k rfl)
    | app => cases shape
    | lam oldTermBody =>
      have lifted : (body.subterm p).map erase=some (.lam oldTermBody) := by rw [erase_subterm]; exact oldLookup
      obtain ⟨oldSub,atOld,oldShape⟩ := Option.map_eq_some_iff.mp lifted
      cases oldSub with
      | var => cases oldShape
      | app => cases oldShape
      | lam oldStamp oldBody =>
        exact Or.inl ⟨oldStamp,oldBody,atOld,contract_retained_lambda_body atOld currentLambda⟩
  · cases shape
  · obtain ⟨oldStamp,oldBody,oldLambda,renamed⟩ := contract_copied_lambda_origin occurs
      (show (contract beta alpha body argument).subterm (q++r)=some (.lam currentStamp currentBody) by rw [←split]; exact currentLambda)
    exact Or.inr ⟨q,r,oldStamp,oldBody,split,occurs,oldLambda,renamed⟩
end Lamping.Lambda.Labelled.LTerm
