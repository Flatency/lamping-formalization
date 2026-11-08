import Lamping.Lamping.RedexChainDegrees
namespace Lamping.Checks.RedexChainDegrees
open AG Graph Lambda Lambda.Labelled
private def redex (appLabel lamLabel : Nat) : LTerm :=
  .app (.atom appLabel) (.lam (.atom lamLabel) (.var (.atom 30) 0))
    (.lam (.atom 40) (.var (.atom 50) 0))
private def term (rightLabel : Nat) : LTerm :=
  .app (.atom 0) (redex 1 9) (redex 2 rightLabel)
private theorem closed (rightLabel : Nat) : Closed (term rightLabel).erase :=
  ⟨⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩,⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩⟩

/-- The two parent app labels differ. Bare singleton-chain isomorphism
only compares the actual selected function-edge label. -/
theorem repeated_degree_distinct_redexes :
    ChainIncidenceIsomorphic (chainSyntaxIncidence (term 9) (closed 9) [[.fn,.fn]])
      (chainSyntaxIncidence (term 9) (closed 9) [[.arg,.fn]]) :=
  (redex_chain_iso_iff_degree (closed 9) (p:=[.fn]) (q:=[.arg]) rfl rfl).mpr rfl

theorem repeated_degree_is_not_current_init : ¬INIT (term 9) := by
  intro initial
  have same := LTerm.initial_degree_injective initial (p:=[.fn]) (q:=[.arg])
    (alpha:=.atom 9) rfl rfl
  cases same

theorem different_degree_prevents_singleton_iso :
    ¬ChainIncidenceIsomorphic (chainSyntaxIncidence (term 10) (closed 10) [[.fn,.fn]])
      (chainSyntaxIncidence (term 10) (closed 10) [[.arg,.fn]]) := by
  intro iso
  have same := (redex_chain_iso_iff_degree (closed 10) (p:=[.fn]) (q:=[.arg]) rfl rfl).mp iso
  cases same

#print axioms EdgeLabelledIncidence.singleton_iso
#print axioms redex_chain_iso_iff_degree
#print axioms redex_chain_representation_iff_degree
#print axioms repeated_degree_distinct_redexes
#print axioms repeated_degree_is_not_current_init
#print axioms different_degree_prevents_singleton_iso
end Lamping.Checks.RedexChainDegrees
