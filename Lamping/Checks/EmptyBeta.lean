import Lamping.Lamping.EmptyBetaMatching
namespace Lamping.Checks.EmptyBeta
open AG Graph

private def exterior := leftNet .app .lam 0 0
private def right : Net signature Empty Bool Empty where
  label := Empty.elim
  wire := {
    mate := fun e => match e with
      | .inl ⟨n,_⟩ => nomatch n
      | .inr (.inl b) => .inr (.inl (!b))
      | .inr (.inr (w,_)) => nomatch w
    involutive := by
      rintro (⟨n,_⟩ | (b | ⟨w,_⟩))
      · exact nomatch n
      · cases b <;> rfl
      · exact nomatch w
    fixedPointFree := by
      rintro (⟨n,_⟩ | (b | ⟨w,_⟩)) same
      · exact nomatch n
      · cases b <;> cases same
      · exact nomatch w }

private def segments : List (Endpoint exterior) :=
  [exterior.wire (.inl ⟨.inl (),appCtx⟩),.inl ⟨.inl (),.inl ()⟩]

/-- A real non-singleton all-left labelled path is reflected by the new API.
This tests exterior reflection, not the full empty-fiber Matches premises. -/
theorem actual_exterior_turn : Labelling exterior segments Context.empty Context.empty := by
  have original : Labelling exterior segments Context.empty Context.empty := by
    apply Labelling.cons
    · rw [Pairing.involutive]
      exact LabelledTurn.node (g:=exterior) (.inl ()) appCtx (.inl ()) (.direct (.appFun Context.empty))
    · exact .single _ _
  exact (original.plugLeft exterior right).plugLeft_reflect exterior right

theorem actual_exterior_has_two_occurrences : segments.length=2 := rfl
theorem first_departure_is_retained :
    (segments.map (AG.plugLeft exterior right)).head?=
      some (AG.plugLeft exterior right (exterior.wire (.inl ⟨.inl (),appCtx⟩))) := rfl

#print axioms actual_exterior_turn
#print axioms actual_exterior_has_two_occurrences
#print axioms first_departure_is_retained
#print axioms WireExcursions.empty_beta_outside
#print axioms PathSite.empty_beta_source_exterior
#print axioms PathSite.empty_beta_access_backward
#print axioms PathSite.empty_beta_access_forward
#print axioms PathSite.empty_beta_binding_access_backward
#print axioms PathSite.empty_beta_matches_rootInputs
end Lamping.Checks.EmptyBeta

