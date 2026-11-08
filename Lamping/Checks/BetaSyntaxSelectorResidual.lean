import Lamping.Lamping.BetaSyntaxSelectorResidual
import Lamping.Checks.BetaFiberDegrees
import Lamping.Checks.Soundness
namespace Lamping.Checks.BetaSyntaxSelectorResidual
open AG Graph Lambda Lambda.Labelled
private abbrev original := initLabels identityApp
private abbrev developed := LTerm.contract (.atom 0) (.atom 1)
  (.var (.atom 2) 0) (.lam (.atom 3) (.var (.atom 4) 0))
private theorem closed : Closed identityApp := ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
private theorem matching : Matches actualBetaSite.net (.inl ()) original.erase :=
  betaEncodingIso.matches (encode_closed_matches identityApp closed 0)
private theorem relative : Marked.RelativeHistory [[]]
    (Marked.mark (actualBetaSite.betaSyntaxFiber (.inl ()) original.erase) original.erase) (.lam (.var 0)) := by
  change Marked.RelativeHistory [[]]
    (if ([] : Path)∈actualBetaSite.betaSyntaxFiber (.inl ()) original.erase then
      .red [[]] (.var 0) (.lam (.var 0)) else .app [[]] (.lam (.var 0)) (.lam (.var 0))) (.lam (.var 0))
  rw [if_pos BetaFiberDegrees.actual_root_member]
  exact .cons (.root _ _ _) (.nil _)
private theorem normal : Marked.Normal (.lam (.var 0)) := by simp [Marked.Normal]
private def labels : History [[]] original developed := .cons (.root _ _ _ _) (.nil _)

/-- The real encoded I I event supplies every condition internally. For
every actual selected RHS access and every input, its literal ancestor is
the ONE shared evaluator word, including the strict copied variable. -/
theorem actual_all_selected_accesses :
    ∃ edge : BetaEdge actualBetaSite.net,
      ∃ selection : SourceEdgeSelection original actualBetaSite.net (.inl ()),
      Matches actualBetaSite.reduce (.inl ()) developed.erase ∧
      ∀ {p sub},developed.subterm p=some sub →
        ∀ (access : RootAccess actualBetaSite.reduce (.inl ())),
        accessWord actualBetaSite.reduce access.val=p →∀ requested : Context,
        ∃ old output,∃ (node : BetaKept) (port : Port (betaKeptLabels node).sort),
          developed.sourceTrail selection.atomWord edge.principal edge.reverseRoute p=some old ∧
          BetaPathResidual actualBetaSite edge (access.val.map (plugEnd _ _).invFun) old ∧
          Labelling actualBetaSite.reduce access.val requested output ∧
          old.getLast?=some (actualBetaSite.net.wire (.inl ⟨.inl node,port⟩)) ∧
          portKind (betaKeptLabels node).sort port=some (syntaxShape sub.erase).kind := by
  have initial := init_is_INIT identityApp
  have inputs := betaEncodingIso.rootInputs (encode_closed_independence identityApp closed 0).rootInputs
  obtain ⟨initialBalance⟩ := encode_indexed_balance identityApp 0
  have balance := betaEncodingIso.indexed_balance initialBalance
  have transparency := betaEncodingIso.transparency (encode_closed_transparency identityApp closed 0)
  have flow := SoundnessBetaAncestor.actualFlow
  obtain ⟨edge,selection,_geometry,all⟩ := actualBetaSite.beta_complete_selector_residuals
    initial closed matching inputs flow rfl balance rfl transparency relative normal labels
  have targetMatching := actualBetaSite.beta_complete_matches initial closed matching inputs flow rfl
    balance rfl transparency relative normal labels
  refine ⟨edge,selection,targetMatching,?_⟩
  intro p sub lookup access word requested
  obtain ⟨finish,trail,output,node,port,evaluation,residual,assignment,ending,proper⟩ :=
    all lookup access word requested
  have last := trail.last
  rw [ending] at last
  exact ⟨trail.edges,output,node,port,evaluation,residual,assignment,last,proper⟩

/-- Both actual target occurrences consume the bridge. In particular the
variable is reached through its actual argument binder, not an invented
lambda context-to-binding passage. -/
theorem actual_lambda_and_copied_variable (requested : Context) :
    ∃ edge : BetaEdge actualBetaSite.net,
      ∃ selection : SourceEdgeSelection original actualBetaSite.net (.inl ()),
      ∀ p∈[([] : Path),[.body]],
        ∃ access : RootAccess actualBetaSite.reduce (.inl ()),∃ old output,
          accessWord actualBetaSite.reduce access.val=p ∧
          developed.sourceTrail selection.atomWord edge.principal edge.reverseRoute p=some old ∧
          BetaPathResidual actualBetaSite edge (access.val.map (plugEnd _ _).invFun) old ∧
          Labelling actualBetaSite.reduce access.val requested output := by
  obtain ⟨edge,selection,targetMatching,all⟩ := actual_all_selected_accesses
  refine ⟨edge,selection,?_⟩
  intro p member
  have existsTerm : ∃ sub,developed.subterm p=some sub := by
    simp at member
    rcases member with rfl | rfl <;> exact ⟨_,rfl⟩
  obtain ⟨sub,lookup⟩ := existsTerm
  let position : Position developed.erase := ⟨p,by rw [←LTerm.erase_subterm,lookup];rfl⟩
  obtain ⟨access,word,_shape⟩ := Matches.observation _ targetMatching position
  obtain ⟨old,output,_node,_port,evaluation,residual,assignment,_last,_proper⟩ := all lookup access word requested
  exact ⟨access,old,output,word,evaluation,residual,assignment⟩

#print axioms PhysicalSyntaxTrail.complete_variable_terminal
#print axioms PathSite.beta_syntax_selector_residual
#print axioms PathSite.beta_actual_selector_residual
#print axioms PathSite.beta_complete_selector_residuals
#print axioms actual_all_selected_accesses
#print axioms actual_lambda_and_copied_variable
end Lamping.Checks.BetaSyntaxSelectorResidual

