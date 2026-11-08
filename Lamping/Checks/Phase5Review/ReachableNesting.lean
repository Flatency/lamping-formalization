import Lamping.Lamping.ReachableNesting
import Lamping.Lamping.BetaEncodingIso
import Lamping.Lambda.LabelCanonicalFirstRedex
namespace Lamping.Checks.Phase5Review.ReachableNesting
open AG Graph Lambda

theorem actual_beta_trace : GraphTrace (ActualNet.initial identityApp)
    (ActualNet.ofNet actualBetaSite.reduce) [.beta 0] :=
  GraphTrace.single (.atSite betaKeptLabels actualBetaSite betaEncodingIso (.refl _))

theorem initial_nonzero_nesting : Nesting identityAppNet (.inl ()) :=
  initial_trace_nesting identityApp (ActualNet.initial identityApp) [] (.refl _)

theorem actual_beta_nesting : Nesting actualBetaSite.reduce (.inl ()) :=
  initial_trace_nesting identityApp (ActualNet.ofNet actualBetaSite.reduce) [.beta 0] actual_beta_trace

-- The actual retained lambda has nonzero index; no closed/SND premise is used.
example : actualBetaSite.reduce.label (.inl (.inr (.inl ())))=label .lam 1 := rfl
example : Closed identityApp := ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
#print axioms Labelling.rooted_terminal_unique
#print axioms IndexedLevelBalance.nesting
#print axioms initial_trace_nesting
#print axioms actual_beta_trace
#print axioms initial_nonzero_nesting
#print axioms actual_beta_nesting
#print axioms Labelled.History.canonical_degree_support
#print axioms Labelled.History.canonical_argument_internal
#print axioms Labelled.History.canonical_first_leftmost
end Lamping.Checks.Phase5Review.ReachableNesting
