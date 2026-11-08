import Lamping.Lambda.UniformOldChainPreimages
namespace Lamping.Lambda.Marked
open Labelled

/-- All marker-free chains reflect through the SAME actual finite OLD
schedule. Intermediate sources may already contain the common degree's
markers. Only the actual read edges, not their starting nodes, must be old. -/
theorem RelativeOldHistory.marker_free_chain_reflect {F ps : List Path} {m n : Marked}
    (old : RelativeOldHistory F ps m n) {d : Path →Option Label}
    {source target : LTerm} {degree : Label} {start : Path} {edges : List Path}
    (aligned : DegreeAligned d m source) (labels : Labelled.History ps source target)
    (selected : ∀ path∈F,d path=some degree)
    (chain : PrerequisiteChain target start edges)
    (safe : ∀ edge∈edges,∀ node,target.subterm edge=some node →
      node.label.OuterBarsSafe (fun payload=>payload≠degree)) :
    ∃ oldStart oldEdges,PrerequisiteChain source oldStart oldEdges ∧
      edges.map target.labelAt=oldEdges.map source.labelAt ∧edges.length=oldEdges.length := by
  obtain ⟨oldStart,oldEdges,oldChain,_,_,same,length⟩ :=
    old.marker_free_chain_preimages aligned labels selected chain safe
  exact ⟨oldStart,oldEdges,oldChain,same,length⟩
end Lamping.Lambda.Marked
namespace Lamping.Lambda
open Labelled

theorem ParallelStep.marker_free_chain_reflect {source target : LTerm}
    {F : List Path} {degree : Label} {start : Path} {edges : List Path}
    (step : ParallelStep F source.erase target.erase) (labels : History step.paths source target)
    (selected : ∀ path∈F,source.degreeAt path=some degree)
    (chain : PrerequisiteChain target start edges)
    (safe : ∀ edge∈edges,∀ node,target.subterm edge=some node →
      node.label.OuterBarsSafe (fun payload=>payload≠degree)) :
    ∃ oldStart oldEdges,PrerequisiteChain source oldStart oldEdges ∧
      edges.map target.labelAt=oldEdges.map source.labelAt ∧edges.length=oldEdges.length :=
  step.complete.1.marker_free_chain_reflect (DegreeAligned.initial source F) labels selected chain safe

/-- In a marker-fresh source, old-label membership supplies the whole
schedule's marker-free condition. This is syntax chain/label transport,
without an incidence isomorphism or physical REP conclusion. -/
theorem ParallelStep.old_label_chain_reflect {source target : LTerm}
    {F : List Path} {degree : Label} {start : Path} {edges : List Path}
    (step : ParallelStep F source.erase target.erase) (labels : History step.paths source target)
    (selected : ∀ path∈F,source.degreeAt path=some degree)
    (sourceSafe : source.OuterBarsSafe (fun payload=>payload≠degree))
    (chain : PrerequisiteChain target start edges)
    (oldLabels : ∀ edge∈edges,∀ node,target.subterm edge=some node →node.label∈source.labels) :
    ∃ oldStart oldEdges,PrerequisiteChain source oldStart oldEdges ∧
      edges.map target.labelAt=oldEdges.map source.labelAt ∧edges.length=oldEdges.length :=
  step.marker_free_chain_reflect labels selected chain (fun edge member node lookup=>
    (LTerm.outerBarsSafe_iff _ _).mp sourceSafe _ (oldLabels edge member node lookup))
end Lamping.Lambda
