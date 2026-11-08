import Lamping.Lambda.LabelCopyInteriors
namespace Lamping.Lambda.Labelled.LTerm
 theorem CopyInterior.lambda_body_rename (copied : CopyInterior original copy)
    (oldLambda : original.subterm r=some (.lam oldStamp oldBody))
    (currentLambda : copy.subterm r=some (.lam currentStamp currentBody)) :
    ∃ rho,currentBody=oldBody.rename rho := by
  obtain ⟨rho,prefixLabel,equal⟩ := copied
  cases r with
  | nil =>
    have oldEq : original=.lam oldStamp oldBody := by simpa only [subterm,Option.some.injEq] using oldLambda
    rw [oldEq,LTerm.rename,LTerm.prepend] at equal
    rw [equal] at currentLambda
    have pair := LTerm.lam.inj (Option.some.inj currentLambda)
    exact ⟨Lambda.liftRen rho,pair.2.symm⟩
  | cons step rest =>
    rw [equal,prepend_subterm_nonempty _ _ (by simp)] at currentLambda
    obtain ⟨tau,transport⟩ := subterm_rename original rho (step::rest)
    rw [transport,oldLambda,Option.map_some] at currentLambda
    have pair := LTerm.lam.inj (Option.some.inj currentLambda)
    exact ⟨Lambda.liftRen tau,pair.2.symm⟩
/-- A real contractum lambda at the specified argument copy has the SAME
old lambda body up to capture-avoiding renaming. Its root label may have
acquired incoming prefixes, including when r=[] or the whole copy is root. -/
theorem contract_copied_lambda_body_rename {body argument oldBody currentBody : LTerm} {q r : Path}
    (occurs : ArgumentOccurrence body.erase q)
    (oldLambda : argument.subterm r=some (.lam oldStamp oldBody))
    (currentLambda : (contract beta alpha body argument).subterm (q++r)=some (.lam currentStamp currentBody)) :
    ∃ rho,currentBody=oldBody.rename rho := by
  rw [subterm_append] at currentLambda
  cases atCopy : (contract beta alpha body argument).subterm q with
  | none => rw [atCopy] at currentLambda; cases currentLambda
  | some copy =>
    rw [atCopy,Option.bind_some] at currentLambda
    exact (contract_argument_copy_interior occurs atCopy).lambda_body_rename oldLambda currentLambda
end Lamping.Lambda.Labelled.LTerm

namespace Lamping.Lambda.Labelled.LTerm
 theorem CopyInterior.lambda_origin (copied : CopyInterior original copy)
    (currentLambda : copy.subterm r=some (.lam currentStamp currentBody)) :
    ∃ oldStamp oldBody,original.subterm r=some (.lam oldStamp oldBody) ∧
      ∃ rho,currentBody=oldBody.rename rho := by
  obtain ⟨rho,prefixLabel,equal⟩ := copied
  cases r with
  | nil =>
    cases original with
    | var => rw [equal] at currentLambda; cases currentLambda
    | app => rw [equal] at currentLambda; cases currentLambda
    | lam stamp body =>
      rw [equal] at currentLambda
      have parts := LTerm.lam.inj (Option.some.inj currentLambda)
      exact ⟨stamp,body,rfl,Lambda.liftRen rho,parts.2.symm⟩
  | cons step rest =>
    rw [equal,prepend_subterm_nonempty _ _ (by simp)] at currentLambda
    obtain ⟨tau,transport⟩ := subterm_rename original rho (step::rest)
    rw [transport] at currentLambda
    obtain ⟨old,atOld,same⟩ := Option.map_eq_some_iff.mp currentLambda
    cases old with
    | var => cases same
    | app => cases same
    | lam stamp body =>
      have parts := LTerm.lam.inj same
      exact ⟨stamp,body,atOld,Lambda.liftRen tau,parts.2.symm⟩
end Lamping.Lambda.Labelled.LTerm
namespace Lamping.Lambda.Labelled.LTerm
/-- A real copied target lambda supplies its original argument lambda and
body renaming itself; no original lambda shape is a caller certificate. -/
theorem contract_copied_lambda_origin {body argument currentBody : LTerm} {q r : Path}
    (occurs : ArgumentOccurrence body.erase q)
    (currentLambda : (contract beta alpha body argument).subterm (q++r)=some (.lam currentStamp currentBody)) :
    ∃ oldStamp oldBody,argument.subterm r=some (.lam oldStamp oldBody) ∧
      ∃ rho,currentBody=oldBody.rename rho := by
  rw [subterm_append] at currentLambda
  cases atCopy : (contract beta alpha body argument).subterm q with
  | none => rw [atCopy] at currentLambda; cases currentLambda
  | some copy =>
    rw [atCopy,Option.bind_some] at currentLambda
    exact (contract_argument_copy_interior occurs atCopy).lambda_origin currentLambda
end Lamping.Lambda.Labelled.LTerm