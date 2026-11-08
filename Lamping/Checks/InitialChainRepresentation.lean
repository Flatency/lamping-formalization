import Lamping.Lamping.InitialChainRepresentation

namespace Lamping.Checks.InitialChainRepresentation
open AG Graph Lambda Lambda.Labelled
private abbrev identity : Term := .lam (.var 0)
private abbrev term := initLabels (.app (.app identity identity) (.app identity identity))
private theorem closed : Closed term.erase := by
  rw [erase_initLabels]
  exact ⟨⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩,⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩⟩
private abbrev net := (encode 0 term.erase).net

private theorem rootChain : PrerequisiteChain term [] [[.fn],[.fn,.fn]] :=
  .app rfl (by intro l b bad; cases bad) (.redex_app rfl)
private theorem rightLambdaChain : PrerequisiteChain term [.arg,.arg] [[.arg,.arg],[.arg,.fn]] :=
  .lam (parent:=[.arg]) (step:=.arg) rfl (by decide) (.redex_app rfl)
private theorem leftRedexApp : PrerequisiteChain term [.fn] [[.fn,.fn]] := .redex_app rfl
private theorem leftRedexLambda : PrerequisiteChain term [.fn,.fn] [[.fn,.fn]] := .redex_lam (p:=[.fn]) rfl

theorem actual_equal_length_distinct_chains_have_distinct_blocks
    (selection : OccurrenceFragmentSelection term net (.inl ())) :
    canonicalChainImage selection rootChain≠canonicalChainImage selection rightLambdaChain := by
  intro same
  have positions := initial_canonical_blocks_reflect_edges rootChain rightLambdaChain
    selection selection same
  cases positions

/-- A real app-start and lambda-start redex chain need not have the same
point/direction. The theorem compares the precise nonpointed incidence object. -/
theorem actual_redex_incidence_iff_blocks
    (left right : OccurrenceFragmentSelection term net (.inl ())) :
    ChainIncidenceIsomorphic (chainSyntaxIncidence term closed [[.fn,.fn]])
      (chainSyntaxIncidence term closed [[.fn,.fn]]) ↔
      canonicalChainImage left leftRedexApp=canonicalChainImage right leftRedexLambda :=
  initial_chain_incidence_iff_blocks closed (init_is_INIT _) leftRedexApp leftRedexLambda left right

theorem actual_initial_all_chain_realization :
    ∃ selection : OccurrenceFragmentSelection term net (.inl ()),
    ∀ (p q : Path) (left right : List Path)
      (first : PrerequisiteChain term p left) (second : PrerequisiteChain term q right),
      ChainIncidenceIsomorphic (chainSyntaxIncidence term closed left)
        (chainSyntaxIncidence term closed right) ↔
        canonicalChainImage selection first=canonicalChainImage selection second :=
  initial_chain_incidence_realization term closed (init_is_INIT _) 0

#print axioms initial_canonical_blocks_reflect_edges
#print axioms initial_chain_incidence_iff_blocks
#print axioms initial_chain_incidence_realization
#print axioms actual_equal_length_distinct_chains_have_distinct_blocks
#print axioms actual_redex_incidence_iff_blocks
#print axioms actual_initial_all_chain_realization
end Lamping.Checks.InitialChainRepresentation
