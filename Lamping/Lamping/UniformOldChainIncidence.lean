import Lamping.Lamping.UniformOldChainIncidencePreimages

namespace Lamping.Lambda.Marked
open Labelled AG

/-- Bare directed incidence reflection along the SAME complete or partial
finite OLD history. The final chain reads no marker of the selected degree;
intermediate labelled sources may already contain that marker. -/
theorem RelativeOldHistory.marker_free_chain_incidence {F ps : List Path} {m n : Marked}
    (old : RelativeOldHistory F ps m n) {d : Path →Option Label}
    {source target : LTerm} {degree : Label} {start : Path} {edges : List Path}
    (sourceClosed : Closed source.erase) (targetClosed : Closed target.erase)
    (aligned : DegreeAligned d m source) (labels : Labelled.History ps source target)
    (selected : ∀ path∈F,d path=some degree)
    (chain : PrerequisiteChain target start edges)
    (safe : ∀ edge∈edges,∀ node,target.subterm edge=some node →
      node.label.OuterBarsSafe (fun payload=>payload≠degree)) :
    ∃ oldStart oldEdges,PrerequisiteChain source oldStart oldEdges ∧
      edges.map target.labelAt=oldEdges.map source.labelAt ∧edges.length=oldEdges.length ∧
      ChainIncidenceIsomorphic (chainSyntaxIncidence target targetClosed edges)
        (chainSyntaxIncidence source sourceClosed oldEdges) := by
  obtain ⟨oldStart,oldEdges,oldChain,_,_,same,length,incidence⟩ :=
    old.marker_free_chain_incidence_preimages sourceClosed targetClosed aligned labels selected chain safe
  exact ⟨oldStart,oldEdges,oldChain,same,length,incidence⟩
end Lamping.Lambda.Marked

namespace Lamping.Lambda
open Labelled AG

theorem ParallelStep.marker_free_chain_incidence {source target : LTerm}
    {F : List Path} {degree : Label} {start : Path} {edges : List Path}
    (sourceClosed : Closed source.erase) (targetClosed : Closed target.erase)
    (step : ParallelStep F source.erase target.erase) (labels : History step.paths source target)
    (selected : ∀ path∈F,source.degreeAt path=some degree)
    (chain : PrerequisiteChain target start edges)
    (safe : ∀ edge∈edges,∀ node,target.subterm edge=some node →
      node.label.OuterBarsSafe (fun payload=>payload≠degree)) :
    ∃ oldStart oldEdges,PrerequisiteChain source oldStart oldEdges ∧
      edges.map target.labelAt=oldEdges.map source.labelAt ∧edges.length=oldEdges.length ∧
      ChainIncidenceIsomorphic (chainSyntaxIncidence target targetClosed edges)
        (chainSyntaxIncidence source sourceClosed oldEdges) :=
  step.complete.1.marker_free_chain_incidence sourceClosed targetClosed
    (DegreeAligned.initial source F) labels selected chain safe

/-- In a fresh source, actual old-label membership discharges the marker
condition. The output is syntax incidence, without physical REP equality. -/
theorem ParallelStep.old_label_chain_incidence {source target : LTerm}
    {F : List Path} {degree : Label} {start : Path} {edges : List Path}
    (sourceClosed : Closed source.erase) (targetClosed : Closed target.erase)
    (step : ParallelStep F source.erase target.erase) (labels : History step.paths source target)
    (selected : ∀ path∈F,source.degreeAt path=some degree)
    (sourceSafe : source.OuterBarsSafe (fun payload=>payload≠degree))
    (chain : PrerequisiteChain target start edges)
    (oldLabels : ∀ edge∈edges,∀ node,target.subterm edge=some node →node.label∈source.labels) :
    ∃ oldStart oldEdges,PrerequisiteChain source oldStart oldEdges ∧
      edges.map target.labelAt=oldEdges.map source.labelAt ∧edges.length=oldEdges.length ∧
      ChainIncidenceIsomorphic (chainSyntaxIncidence target targetClosed edges)
        (chainSyntaxIncidence source sourceClosed oldEdges) :=
  step.marker_free_chain_incidence sourceClosed targetClosed labels selected chain
    (fun edge member node lookup=>(LTerm.outerBarsSafe_iff _ _).mp sourceSafe _ (oldLabels edge member node lookup))
end Lamping.Lambda
