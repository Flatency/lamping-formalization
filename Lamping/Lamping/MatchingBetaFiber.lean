import Lamping.Lamping.MatchingRedexEndpointUniqueness
import Lamping.Lamping.PathSiteBeta
import Lamping.Lambda.FiniteRedexFibers
namespace Lamping.AG
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable (g : Net signature N B W) (root : B) (t : Term) (app lam : N)
/-- Source occurrence membership uses an actual rooted provenance certificate.
No target graph correctness or arbitrary path-completion claim is a field. -/
def AtPhysicalBeta (p : Path) : Prop :=
  ∃ (redex : RedexOcc t) (source : ActualRedexAccess g root redex),
    redex.val=p ∧ source.connection.app=app ∧ source.connection.lam=lam
noncomputable def physicalBetaTest : Path → Bool := by
  classical
  exact fun p => decide (AtPhysicalBeta g root t app lam p)
noncomputable def physicalBetaFiberPaths : List Path :=
  redexFiberPaths t (physicalBetaTest g root t app lam)
theorem physicalBetaTest_iff (p : Path) :
    physicalBetaTest g root t app lam p=true ↔ AtPhysicalBeta g root t app lam p := by
  classical
  simp only [physicalBetaTest,decide_eq_true_eq]
theorem mem_physicalBetaFiberPaths (p : Path) :
    p∈physicalBetaFiberPaths g root t app lam ↔ AtPhysicalBeta g root t app lam p := by
  rw [physicalBetaFiberPaths,mem_redexFiberPaths,physicalBetaTest_iff]
  constructor
  · exact And.right
  · intro member
    obtain ⟨redex,source,eq,atApp,atLam⟩ := member
    exact ⟨eq ▸ redex.property,redex,source,eq,atApp,atLam⟩
/-- Every actual source witness for the same syntax redex makes the same
physical selection; neither an arbitrary connection nor a chosen representative
can change the fiber. -/
theorem ActualRedexAccess.physical_selection_iff {redex : RedexOcc t}
    (matching : Matches g root t) (source : ActualRedexAccess g root redex) :
    redex.val∈physicalBetaFiberPaths g root t app lam ↔
      source.connection.app=app ∧ source.connection.lam=lam := by
  rw [mem_physicalBetaFiberPaths]
  constructor
  · rintro ⟨otherRedex,other,eq,atApp,atLam⟩
    have same : otherRedex=redex := Subtype.ext eq
    subst otherRedex
    have unique := ActualRedexAccess.endpoints_unique matching other source
    exact ⟨unique.2.2.1.symm.trans atApp,unique.2.2.2.symm.trans atLam⟩
  · rintro ⟨atApp,atLam⟩
    exact ⟨redex,source,rfl,atApp,atLam⟩
noncomputable instance physicalBetaFiberFiniteNames : FiniteNames {p : Path // p∈physicalBetaFiberPaths g root t app lam} :=
  redexFiberFiniteNames t (physicalBetaTest g root t app lam)
theorem physicalBetaFiber_finite_bound :
    (physicalBetaFiberPaths g root t app lam).length≤(redexPositions t).length :=
  redexFiberPaths_length_le _ _
theorem physicalBetaFiber_complete_exists :
    ∃ ps marked,Marked.CompleteOldDevelopment (physicalBetaFiberPaths g root t app lam) t ps marked :=
  redexFiber_complete_exists _ _
variable {g root t app lam}
theorem physicalBetaFiber_complete_betaHistory
    (complete : Marked.CompleteOldDevelopment (physicalBetaFiberPaths g root t app lam) t ps marked) :
    BetaHistory ps t marked.erase := redexFiber_complete_betaHistory complete
theorem physicalBetaFiber_complete_empty
    (complete : Marked.CompleteOldDevelopment (physicalBetaFiberPaths g root t app lam) t ps marked)
    (empty : physicalBetaFiberPaths g root t app lam=[]) : ps=[] ∧ marked.erase=t :=
  redexFiber_complete_empty_endpoint complete empty
theorem physicalBetaFiber_complete_nonempty
    (complete : Marked.CompleteOldDevelopment (physicalBetaFiberPaths g root t app lam) t ps marked)
    (positive : physicalBetaFiberPaths g root t app lam≠[]) :
    ∃ p rest middle,ps=p::rest ∧ BetaAt t p middle ∧ BetaHistory rest middle marked.erase :=
  redexFiber_complete_nonempty complete positive
theorem physicalBetaFiber_complete_exhausted
    (complete : Marked.CompleteOldDevelopment (physicalBetaFiberPaths g root t app lam) t ps marked)
    (member : name∈physicalBetaFiberPaths g root t app lam) : Marked.tracePositions name marked=[] :=
  redexFiber_complete_exhausted complete member
theorem physicalBetaFiber_complete_betas
    (complete : Marked.CompleteOldDevelopment (physicalBetaFiberPaths g root t app lam) t ps marked) :
    Betas t marked.erase := redexFiber_complete_betas complete
theorem physicalBetaFiber_complete_residuals
    (first : Marked.CompleteOldDevelopment (physicalBetaFiberPaths g root t app lam) t ps left)
    (second : Marked.CompleteOldDevelopment (physicalBetaFiberPaths g root t app lam) t qs right)
    (old : RedexOcc t) : left.erase=right.erase ∧
      Marked.tracePositions old.val left=Marked.tracePositions old.val right :=
  redexFiber_complete_residuals first second old
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i : Nat}
/-- The actual beta site's distinguished physical app/lambda pair fixes the
source syntax fiber; finiteness comes from syntax, not root-path enumeration. -/
noncomputable def PathSite.betaSyntaxFiber
    (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V)) (root : B) (t : Term) : List Path :=
  physicalBetaFiberPaths site.net root t (.inr (.inl ())) (.inr (.inr ()))
theorem PathSite.betaSyntaxFiber_complete_exists
    (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V)) (root : B) (t : Term) :
    ∃ ps marked,Marked.CompleteOldDevelopment (site.betaSyntaxFiber root t) t ps marked :=
  physicalBetaFiber_complete_exists _ _ _ _ _
end
end Lamping.AG



