import Lamping.Lamping.UncreatedChainIncidence
import Lamping.Lambda.UniformOldChainPreimages
namespace Lamping.AG
open Graph Lambda Lambda.Labelled

private theorem marker_free_middle {final middle : LTerm} {edges middleEdges : List Path}
    {degree : Label} {edge : Path} {node : LTerm}
    (labels : edges.map final.labelAt=middleEdges.map middle.labelAt)
    (safe : ∀ edge∈edges,∀ current,final.subterm edge=some current →
      current.label.OuterBarsSafe (fun payload=>payload≠degree))
    (member : edge∈middleEdges) (lookup : middle.subterm edge=some node) :
    node.label.OuterBarsSafe (fun payload=>payload≠degree) := by
  have present : some node.label∈middleEdges.map middle.labelAt :=
    List.mem_map.mpr ⟨edge,member,by simp only [LTerm.labelAt,lookup,Option.map_some]⟩
  rw [←labels] at present
  obtain ⟨original,inside,equal⟩ := List.mem_map.mp present
  change (final.subterm original).map LTerm.label=some node.label at equal
  obtain ⟨current,atCurrent,labelEq⟩ := Option.map_eq_some_iff.mp equal
  rw [←labelEq]
  exact safe original inside current atCurrent
end Lamping.AG

namespace Lamping.Lambda.Marked
open Labelled AG

/-- Bare directed incidence reflection along the SAME complete or partial
finite OLD history. The final chain reads no marker of the selected degree;
intermediate labelled sources may already contain that marker. -/
theorem RelativeOldHistory.marker_free_chain_incidence_preimages {F ps : List Path} {m n : Marked}
    (old : RelativeOldHistory F ps m n) {d : Path →Option Label}
    {source target : LTerm} {degree : Label} {start : Path} {edges : List Path}
    (sourceClosed : Closed source.erase) (targetClosed : Closed target.erase)
    (aligned : DegreeAligned d m source) (labels : Labelled.History ps source target)
    (selected : ∀ path∈F,d path=some degree)
    (chain : PrerequisiteChain target start edges)
    (safe : ∀ edge∈edges,∀ node,target.subterm edge=some node →
      node.label.OuterBarsSafe (fun payload=>payload≠degree)) :
    ∃ oldStart oldEdges,PrerequisiteChain source oldStart oldEdges ∧
      BetaNodeHistoryPreimage labels start oldStart ∧
      BetaEdgeHistoryPreimages labels edges oldEdges ∧
      edges.map target.labelAt=oldEdges.map source.labelAt ∧edges.length=oldEdges.length ∧
      ChainIncidenceIsomorphic (chainSyntaxIncidence target targetClosed edges)
        (chainSyntaxIncidence source sourceClosed oldEdges) := by
  induction old generalizing source target start edges with
  | nil => cases labels;exact ⟨start,edges,chain,.nil _ _,BetaEdgeHistoryPreimages.refl _ _,rfl,rfl,⟨ChainIncidenceIso.refl _⟩⟩
  | @cons path _ _ _ _ reduction member tail ih =>
    cases labels with
    | @cons _ _ middle _ _ turn remaining =>
      have middleClosed : Closed middle.erase := turn.betaAt.beta.scoped sourceClosed
      obtain ⟨middleStart,middleEdges,middleChain,startTrace,edgeTraces,middleLabels,middleLength,⟨middleIso⟩⟩ :=
        ih middleClosed targetClosed (aligned.step reduction turn) remaining chain safe
      obtain ⟨name,chosen,residual⟩ := (mem_setResidualPositions _ _ _).mp member
      have atDegree := (aligned.trace_degree residual).trans (selected name chosen)
      obtain ⟨beta,body,argument,redex⟩ := LTerm.degreeAt_redex atDegree
      have uncreated edge (inside : edge∈middleEdges) : ¬BetaCreatedIncoming body path edge := by
        have exists_node : ∃ node,middle.subterm edge=some node := by
          rcases middleChain.eligible inside with ⟨parent,stamp,fn,arg,equal,atParent⟩ |
            ⟨stamp,inner,atLambda⟩
          · refine ⟨fn,?_⟩
            rw [equal,LTerm.subterm_append,atParent];cases fn <;> rfl
          · exact ⟨_,atLambda⟩
        obtain ⟨node,lookup⟩ := exists_node
        intro created
        exact turn.created_label_not_safe redex lookup created
          (AG.marker_free_middle middleLabels safe inside lookup)
      obtain ⟨oldStart,oldEdges,startOrigin,oldChain,edgeOrigins,oldLabels,oldLength⟩ :=
        turn.uncreated_chain_reflect redex middleChain uncreated
      obtain ⟨oldIso,_edgeMap,_vertexMap⟩ :=
        uncreated_chain_iso sourceClosed middleClosed turn redex middleChain oldChain uncreated edgeOrigins
      exact ⟨oldStart,oldEdges,oldChain,.one (step:=turn) redex startOrigin startTrace,
        edgeTraces.prepend (step:=turn) redex edgeOrigins,middleLabels.trans oldLabels,middleLength.trans oldLength,
        ⟨middleIso.trans oldIso⟩⟩
end Lamping.Lambda.Marked
