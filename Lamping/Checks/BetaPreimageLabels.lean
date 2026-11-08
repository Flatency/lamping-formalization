import Lamping.Lambda.BetaPreimageLabels
namespace Lamping.Checks.BetaPreimageLabels
open Lambda Lambda.Labelled
private abbrev body : LTerm := .lam (.atom 3) (.app (.atom 4) (.var (.atom 5) 0) (.var (.atom 6) 1))
private abbrev argument : LTerm := .lam (.atom 7) (.app (.atom 20) (.var (.atom 9) 0) (.var (.atom 10) 0))
private abbrev redex : LTerm := .app (.atom 1) (.lam (.atom 2) body) argument
private abbrev contractum := LTerm.contract (.atom 1) (.atom 2) body argument
private abbrev source : LTerm := .lam (.atom 20) redex
private abbrev target : LTerm := .lam (.atom 20) contractum
private def turn : StepAt [.body] source target := .body (.root _ _ _ _)
private abbrev edges : List Path := [[.body,.body,.arg,.body],[],[.body,.body,.fn]]
private abbrev oldEdges : List Path := [[.body,.arg,.body],[],[.body,.fn,.body,.body,.fn]]
private theorem outside : ¬∃ relative,([] : Path)=[.body]++relative := by
  rintro ⟨relative,equal⟩;cases equal
private def origins : BetaEdgePreimages body argument [.body] edges oldEdges := by
  refine .cons (.copied (q := [.body,.arg]) (relative := [.body]) rfl rfl)
    (.cons (.context outside) (.cons (.retained (relative := [.body,.fn]) rfl ?_) .nil))
  intro stamp equal
  cases equal
private theorem lookups (edge : Path) (member : edge∈edges) : ∃ current,target.subterm edge=some current := by
  rcases List.mem_cons.mp member with rfl | rest
  · exact ⟨.app (.atom 20) (.var (.atom 9) 0) (.var (.atom 10) 0),rfl⟩
  · rcases List.mem_cons.mp rest with rfl | final
    · exact ⟨target,rfl⟩
    · have equal := List.mem_singleton.mp final
      subst edge;exact ⟨.var (.atom 5) 0,rfl⟩
private theorem uncreated (edge : Path) (member : edge∈edges) : ¬BetaCreatedIncoming body [.body] edge := by
  rcases List.mem_cons.mp member with rfl | rest
  · decide
  · rcases List.mem_cons.mp rest with rfl | final
    · decide
    · have equal := List.mem_singleton.mp final
      subst edge;decide

/-- One real list traverses ARG, outside context, then retained body
coordinates. Its labels are preserved in the same order, with repetitions. -/
theorem exact_mixed_preimage_labels :
    edges.map target.labelAt=oldEdges.map source.labelAt ∧
    oldEdges.map source.labelAt=[some (.atom 20),some (.atom 20),some (.atom 5)] := by
  exact ⟨turn.beta_preimage_ordered_labels rfl origins lookups uncreated,rfl⟩

/-- There really is another old node with the same label, but it cannot
replace the supplied context preimage coordinate. -/
theorem matching_label_is_not_a_coordinate :
    source.labelAt []=source.labelAt [.body,.arg,.body] ∧
    ¬BetaNodePreimage body argument [.body] [] [.body,.arg,.body] := by
  refine ⟨rfl,?_⟩
  intro wrong
  have equal := BetaNodePreimage.unique (.context outside) wrong
  cases equal

/-- A copy root still has a true node preimage, but its incoming edge is
created, and its label is not preserved at that same old coordinate. -/
theorem copy_root_needs_uncreated_premise :
    BetaNodePreimage body argument [.body] [.body,.body,.arg] [.body,.arg] ∧
    BetaCreatedIncoming body [.body] [.body,.body,.arg] ∧
    target.labelAt [.body,.body,.arg]≠source.labelAt [.body,.arg] := by
  exact ⟨.copied (q := [.body,.arg]) (relative := []) rfl rfl,by decide,by decide⟩

end Lamping.Checks.BetaPreimageLabels
#print axioms Lamping.Lambda.Labelled.StepAt.beta_preimage_label
#print axioms Lamping.Lambda.Labelled.StepAt.beta_preimage_labelAt
#print axioms Lamping.Lambda.Labelled.StepAt.beta_preimage_ordered_labels
#print axioms Lamping.Checks.BetaPreimageLabels.exact_mixed_preimage_labels
#print axioms Lamping.Checks.BetaPreimageLabels.matching_label_is_not_a_coordinate
