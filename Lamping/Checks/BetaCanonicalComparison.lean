import Lamping.Lamping.BetaCanonicalComparison
import Lamping.Checks.Soundness
namespace Lamping.Checks.BetaCanonicalComparison
open AG Graph Lambda
private abbrev site := actualBetaSite
private abbrev fragmentCut := cutFragment site.net (pathPartition (Schema.beta 0) Unit) site.closed
private def rootOutside : Endpoint fragmentCut := .inr (.inl (.inl (.inl ())))
private def bodyOutside : Endpoint fragmentCut := .inr (.inl (.inr (.inr true)))
private def keptContext : Endpoint fragmentCut := .inl ⟨.inr (.inl ()),.inl ()⟩
private def keptBody : Endpoint fragmentCut := .inl ⟨.inr (.inl ()),.inr true⟩
private def keptPivot : Endpoint fragmentCut := fragmentCut.wire keptContext

/-- This actual encoded I I ancestor traverses BOTH beta reconnections and
a retained Cro, with its genuine changing assignment. Both literal uniqueness
directions are consumed; no atomic/empty-word premise is imposed. -/
theorem actual_two_reconnections_unique (a : Context) :
    ∃ (edge : BetaEdge site.net) (old : List (Endpoint site.net)),
      SiteBetaGeometry site edge ∧
      BetaPathResidual site edge (SoundnessBetaAncestor.reduced.map (plugEnd _ _).invFun) old ∧
      ExpandedLabelling site.net old a (a.cons .empty) ∧
      (∀ other,BetaPathResidual site edge
        (SoundnessBetaAncestor.reduced.map (plugEnd _ _).invFun) other → other=old) ∧
      (∀ other,BetaPathResidual site edge other old →
        other=SoundnessBetaAncestor.reduced.map (plugEnd _ _).invFun) := by
  obtain ⟨edge,old,geometry,residual,labels,_head,_last⟩ := SoundnessBetaAncestor.actual_ancestor a
  refine ⟨edge,old,geometry,residual,labels,?_,?_⟩
  · intro other relation
    exact relation.source_unique site geometry residual
  · intro other relation
    exact relation.target_unique site geometry residual rfl

/-- The real root-to-body reconnection fixes the first and last prefix
ordinals. The last cut is the singleton boundary of an empty suffix, not
an invented empty prerequisite chain. -/
theorem actual_context_first_and_last_cuts :
    ∃ edge : BetaEdge site.net,SiteBetaGeometry site edge ∧
      BetaPathResidual site edge
        [Sum.inl rootOutside,Sum.inr (.inr (.inl (.inl false))),Sum.inl bodyOutside]
        (site.outsideEnd rootOutside::(edge.principal++[site.outsideEnd bodyOutside])) ∧
      BetaPathResidual site edge [Sum.inl bodyOutside] [site.outsideEnd bodyOutside] := by
  obtain ⟨edge,geometry⟩ := site.siteBetaGeometry_exists
  have whole : BetaPathResidual site edge
      [Sum.inl rootOutside,Sum.inr (.inr (.inl (.inl false))),Sum.inl bodyOutside]
      (site.outsideEnd rootOutside::(edge.principal++[site.outsideEnd bodyOutside])) :=
    .context rfl (.single bodyOutside)
  have firstCut := whole.cut_at_actual_prefix site geometry (.single rootOutside)
    (parentOld:=[site.outsideEnd rootOutside]) (oldPiece:=edge.principal++[site.outsideEnd bodyOutside])
    (parentRaw:=[Sum.inl rootOutside])
    (newPiece:=[Sum.inr (.inr (.inl (.inl false))),Sum.inl bodyOutside]) rfl rfl rootOutside rfl
  have oldLast : (site.outsideEnd rootOutside::(edge.principal++[site.outsideEnd bodyOutside])).getLast?=
      some (site.outsideEnd bodyOutside) := by
    simp only [List.getLast?_cons,List.getLast?_append,List.getLast?_nil,Option.some_or,
      Option.getD_some,Option.getD_none]
  have lastCut := whole.cut_at_actual_prefix site geometry whole
    (oldPiece:=[]) (newPiece:=[]) (by rw [List.append_nil]) (by rw [List.append_nil]) bodyOutside oldLast
  exact ⟨edge,geometry,firstCut,lastCut⟩

/-- The retained argument lambda has a real ordinary context/body turn.
The exact parent-prefix cut removes its shared leading arrival and returns
the actual singleton child residual. This is a local path consumer, not a
claim that a full target occurrence selector has already been constructed. -/
theorem actual_kept_lambda_cut (a : Context) :
    ∃ edge : BetaEdge site.net,SiteBetaGeometry site edge ∧
      Labelling fragmentCut [keptPivot,keptBody] a a ∧
      BetaPathResidual site edge [Sum.inl keptBody] [site.outsideEnd keptBody] := by
  obtain ⟨edge,geometry⟩ := site.siteBetaGeometry_exists
  have labels : Labelling fragmentCut [keptPivot,keptBody] a a := by
    apply Labelling.cons
    · change LabelledTurn fragmentCut (fragmentCut.wire (fragmentCut.wire keptContext)) keptBody a a
      rw [Pairing.involutive]
      exact LabelledTurn.node (g:=fragmentCut) (.inr (.inl ())) (.inl ()) (.inr true) (.direct (.lamBody a))
    · exact .single _ _
  have whole : BetaPathResidual site edge [Sum.inl keptPivot,Sum.inl keptBody]
      [site.outsideEnd keptPivot,site.outsideEnd keptBody] := .outside (.single keptBody)
  have parentLast : [site.outsideEnd keptPivot].getLast?=
      some (site.net.wire (.inl ⟨.inl (.inr (.inl ())),.inl ()⟩)) :=
    congrArg some (site.outsideEnd_wire keptContext).symm
  have actual := whole.cut_at_kept_prefix site geometry (.single keptPivot)
    (parentOld:=[site.outsideEnd keptPivot]) (oldPiece:=[site.outsideEnd keptBody])
    (parentRaw:=[Sum.inl keptPivot]) (newPiece:=[Sum.inl keptBody]) rfl rfl
    (.inr (.inl ())) (.inl ()) parentLast (by intro impossible;cases impossible)
  exact ⟨edge,geometry,labels,actual⟩

#print axioms BetaPathResidual.canonical
#print axioms BetaPathResidual.target_unique
#print axioms BetaPathResidual.source_unique
#print axioms BetaPathResidual.split_outside
#print axioms BetaPathResidual.cut_at_actual_prefix
#print axioms BetaPathResidual.cut_at_kept_prefix
#print axioms actual_two_reconnections_unique
#print axioms actual_context_first_and_last_cuts
#print axioms actual_kept_lambda_cut
end Lamping.Checks.BetaCanonicalComparison
