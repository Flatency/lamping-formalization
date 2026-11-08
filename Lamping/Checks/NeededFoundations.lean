import Lamping.Lambda.Needed

namespace Lamping.Checks.NeededFoundations
open Lambda

private def identity : Term := .lam (.var 0)
private def identityApplication : Term := .app identity identity
private def underLambda : Term := .lam (.app (.lam (.var 0)) (.var 0))

theorem actual_closed_lo_and_needed :
    Closed identity ∧ Closed identityApplication ∧ Closed underLambda ∧
    isBetaNormal identity=true ∧ loRedex identity=none ∧
    loRedex identityApplication=some [] ∧
    loRedex underLambda=some [.body] ∧
    Needed (⟨[],by
      exact ⟨identityApplication,rfl,True.intro⟩⟩ : RedexOcc identityApplication) ∧
    Needed (⟨[.body],by
      exact ⟨.app (.lam (.var 0)) (.var 0),rfl,True.intro⟩⟩ : RedexOcc underLambda) := by
  have normal : BetaNF identity := by
    intro r
    rcases r with ⟨p,valid⟩
    cases p with
    | nil => simp [identity,subtermAt,IsRedex] at valid
    | cons s p =>
      cases s <;> cases p <;> simp [identity,subtermAt,IsRedex] at valid
  refine ⟨?_,?_,?_,(isBetaNormal_eq_true_iff identity).mpr normal,?_,?_,?_,?_,?_⟩
  · simp [identity,Closed,Scoped]
  · simp [identityApplication,identity,Closed,Scoped]
  · simp [underLambda,Closed,Scoped]
  · exact (loRedex_none_iff identity).mpr normal
  · rfl
  · rfl
  · exact loRedex_needed (t:=identityApplication) (p:=[]) rfl
  · exact loRedex_needed (t:=underLambda) (p:=[.body]) rfl

#print axioms actual_closed_lo_and_needed
end Lamping.Checks.NeededFoundations
