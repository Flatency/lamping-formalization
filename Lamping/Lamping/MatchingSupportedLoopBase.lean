import Lamping.Lamping.MatchingBetaGeneratedBase
import Lamping.Lamping.SupportedExpandedLoops
namespace Lamping.AG
open Graph Lambda
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i : Nat}

/-- Actual source Matches supplies supported ordinary loop bases for every
redex of the actual old physical fiber. Neither the support nor any body
generation certificate is an input. Later historical loop support remains
a separate induction obligation. -/
theorem PathSite.beta_fiber_supported_loop_base
    (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
    {root : B} {t : Term} (matching : Matches site.net root t) :
    ∃ beta : BetaEdge site.net,beta.app=.inr (.inl ()) ∧beta.lam=.inr (.inr ()) ∧
      ∀ (redex : RedexOcc t),redex.val∈site.betaSyntaxFiber root t →
      ∀ {body argument},subtermAt t redex.val=some (.app (.lam body) argument) →
      ∀ p,subtermAt body p=some (.var (binderDepth p)) →
      ∃ (pre loop suffix : List (Endpoint site.net)),
        accessWord site.net pre=redex.val ∧accessWord site.net loop=p ∧
        SupportedExpandedBindingLoop site.net root (pre++beta.principal) beta.lam loop ∧
        GeneratedExpandedProperPath site.net root (pre++beta.argEnd::suffix) ∧
        GeneratedExpandedProperPath site.net root (pre++beta.principal++loop) ∧
        GeneratedExpandedProperPath site.net root
          (pre++beta.principal++loop++beta.reverseRoute++[beta.argEnd]++suffix) := by
  obtain ⟨beta,app,lam,bases⟩ := site.beta_fiber_generated_insert_base matching
  refine ⟨beta,app,lam,?_⟩
  intro redex member body argument lookup p variableLookup
  obtain ⟨pre,loop,suffix,a,b,binding,binder,preWord,loopWord,argumentGen,bodyGen,inserted⟩ :=
    bases redex member lookup p variableLookup
  have support : SupportedExpandedBindingLoop site.net root (pre++beta.principal) beta.lam loop := by
    rw [←binder]
    exact .base (pre++beta.principal) loop a b binding
  exact ⟨pre,loop,suffix,preWord,loopWord,support,argumentGen,bodyGen,inserted⟩
end
end Lamping.AG
