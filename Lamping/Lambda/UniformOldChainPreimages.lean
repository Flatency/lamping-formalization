import Lamping.Lambda.BetaChainExistenceReflection
import Lamping.Lambda.LabelUniformDevelopment
namespace Lamping.Lambda.Labelled
/-- Ordered literal occurrence ancestry through ONE actual history. -/
inductive BetaEdgeHistoryPreimages {ps : List Path} {source target : LTerm}
    (labels : History ps source target) : List Path →List Path →Prop where
  | nil : BetaEdgeHistoryPreimages labels [] []
  | cons : BetaNodeHistoryPreimage labels edge oldEdge →
      BetaEdgeHistoryPreimages labels edges oldEdges →
      BetaEdgeHistoryPreimages labels (edge::edges) (oldEdge::oldEdges)
namespace BetaEdgeHistoryPreimages
 theorem refl (source : LTerm) (edges : List Path) :
    BetaEdgeHistoryPreimages (.nil source) edges edges := by
  induction edges with
  | nil => exact .nil
  | cons e es ih => exact .cons (.nil _ _) ih
 theorem prepend {body argument : LTerm} {site : Path} {beta alpha : Label}
    {step : StepAt site source middle} {remaining : History ps middle target}
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (later : BetaEdgeHistoryPreimages remaining edges middleEdges)
    (earlier : BetaEdgePreimages body argument site middleEdges oldEdges) :
    BetaEdgeHistoryPreimages (.cons step remaining) edges oldEdges := by
  induction later generalizing oldEdges with
  | nil => cases earlier;exact .nil
  | cons origin tail ih =>
    cases earlier with
    | cons before rest => exact .cons (.one (step:=step) redex before origin) (ih rest)
end BetaEdgeHistoryPreimages
end Lamping.Lambda.Labelled
namespace Lamping.Lambda.Labelled

private theorem marker_free_of_same_labels {left right : LTerm} {edges otherEdges : List Path}
    {degree : Label} {edge : Path} {current : LTerm}
    (same : edges.map left.labelAt=otherEdges.map right.labelAt)
    (safe : ∀ edge∈edges,∀ node,left.subterm edge=some node →
      node.label.OuterBarsSafe (fun payload=>payload≠degree))
    (member : edge∈otherEdges) (lookup : right.subterm edge=some current) :
    current.label.OuterBarsSafe (fun payload=>payload≠degree) := by
  have present : some current.label∈otherEdges.map right.labelAt :=
    List.mem_map.mpr ⟨edge,member,by simp only [LTerm.labelAt,lookup,Option.map_some]⟩
  rw [←same] at present
  obtain ⟨original,atOriginal,labelEq⟩ := List.mem_map.mp present
  change (left.subterm original).map LTerm.label=some current.label at labelEq
  obtain ⟨old,lookupOld,equal⟩ := Option.map_eq_some_iff.mp labelEq
  rw [←equal]
  exact safe original atOriginal old lookupOld
end Lamping.Lambda.Labelled

namespace Lamping.Lambda.Marked
open Labelled

/-- All marker-free chains reflect through the SAME actual finite OLD
schedule. Intermediate sources may already contain the common degree's
markers. Only the actual read edges, not their starting nodes, must be old. -/
theorem RelativeOldHistory.marker_free_chain_preimages {F ps : List Path} {m n : Marked}
    (old : RelativeOldHistory F ps m n) {d : Path →Option Label}
    {source target : LTerm} {degree : Label} {start : Path} {edges : List Path}
    (aligned : DegreeAligned d m source) (labels : Labelled.History ps source target)
    (selected : ∀ path∈F,d path=some degree)
    (chain : PrerequisiteChain target start edges)
    (safe : ∀ edge∈edges,∀ node,target.subterm edge=some node →
      node.label.OuterBarsSafe (fun payload=>payload≠degree)) :
    ∃ oldStart oldEdges,PrerequisiteChain source oldStart oldEdges ∧
      BetaNodeHistoryPreimage labels start oldStart ∧
      BetaEdgeHistoryPreimages labels edges oldEdges ∧
      edges.map target.labelAt=oldEdges.map source.labelAt ∧edges.length=oldEdges.length := by
  induction old generalizing source target start edges with
  | nil => cases labels;exact ⟨start,edges,chain,.nil _ _,BetaEdgeHistoryPreimages.refl _ _,rfl,rfl⟩
  | @cons path _ _ _ _ reduction member tail ih =>
    cases labels with
    | @cons _ _ middle _ _ turn remaining =>
      obtain ⟨middleStart,middleEdges,middleChain,startTrace,edgeTraces,middleLabels,middleLength⟩ :=
        ih (aligned.step reduction turn) remaining chain safe
      obtain ⟨name,chosen,residual⟩ := (mem_setResidualPositions _ _ _).mp member
      have atDegree := (aligned.trace_degree residual).trans (selected name chosen)
      obtain ⟨beta,body,argument,redex⟩ := LTerm.degreeAt_redex atDegree
      have uncreated edge (inside : edge∈middleEdges) : ¬BetaCreatedIncoming body path edge := by
        have lookup : ∃ current,middle.subterm edge=some current := by
          rcases middleChain.eligible inside with ⟨parent,stamp,fn,arg,equal,atParent⟩ |
            ⟨stamp,inner,atLambda⟩
          · refine ⟨fn,?_⟩
            rw [equal,LTerm.subterm_append,atParent]; cases fn <;> rfl
          · exact ⟨_,atLambda⟩
        obtain ⟨current,atCurrent⟩ := lookup
        intro created
        exact turn.created_label_not_safe redex atCurrent created
          (marker_free_of_same_labels middleLabels safe inside atCurrent)
      obtain ⟨oldStart,oldEdges,startOrigin,oldChain,edgeOrigins,oldLabels,oldLength⟩ :=
        turn.uncreated_chain_reflect redex middleChain uncreated
      exact ⟨oldStart,oldEdges,oldChain,.one (step:=turn) redex startOrigin startTrace,
        edgeTraces.prepend (step:=turn) redex edgeOrigins,middleLabels.trans oldLabels,middleLength.trans oldLength⟩
end Lamping.Lambda.Marked



namespace Lamping.Lambda.Labelled.BetaEdgeHistoryPreimages
/-- Retains the actual occurrence witness at its list slot; labels need
not be distinct. -/
theorem mem (origins : BetaEdgeHistoryPreimages labels edges oldEdges)
    (member : edge∈edges) : ∃ oldEdge∈oldEdges,BetaNodeHistoryPreimage labels edge oldEdge := by
  induction origins with
  | nil => cases member
  | cons origin tail ih =>
    rcases List.mem_cons.mp member with rfl | inside
    · exact ⟨_,List.mem_cons_self,origin⟩
    · obtain ⟨oldEdge,oldMember,trace⟩ := ih inside
      exact ⟨oldEdge,List.mem_cons_of_mem _ oldMember,trace⟩
theorem unique (left : BetaEdgeHistoryPreimages labels edges oldEdges)
    (right : BetaEdgeHistoryPreimages labels edges otherEdges) : oldEdges=otherEdges := by
  induction left generalizing otherEdges with
  | nil => cases right;rfl
  | cons origin tail ih =>
    cases right with
    | cons other rest => rw [origin.unique other,ih rest]
end Lamping.Lambda.Labelled.BetaEdgeHistoryPreimages