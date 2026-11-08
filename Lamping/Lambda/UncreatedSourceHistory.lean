import Lamping.Lambda.NodeIncomingFirstCreation
import Lamping.Lambda.BetaIncidencePreimages
namespace Lamping.Lambda.Labelled
open SyntaxIncidence
/-- Actual vertex ancestry for one fixed history: the external boundary
stays external; proper vertices carry the real operational node trace. -/
inductive BetaVertexHistoryPreimage {ps : List Path} {source target : LTerm}
    (labels : History ps source target) : Vertex target →Vertex source →Prop where
  | boundary : BetaVertexHistoryPreimage labels none none
  | proper {current : ProperPosition target} {old : ProperPosition source} :
      BetaNodeHistoryPreimage labels current.val old.val →
      BetaVertexHistoryPreimage labels (some current) (some old)

namespace BetaVertexHistoryPreimage
theorem refl {source : LTerm} (labels : History [] source source) (vertex : Vertex source) :
    BetaVertexHistoryPreimage labels vertex vertex := by
  cases labels
  cases vertex with
  | none => exact .boundary
  | some p => exact .proper (.nil _ _)

theorem prepend
    {site : Path} {ps : List Path} {source middle target body argument : LTerm} {beta alpha : Label}
    {step : StepAt site source middle} {remaining : History ps middle target}
    {current : Vertex target} {mid : Vertex middle} {old : Vertex source}
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (origin : BetaVertexPreimage body argument site source middle mid old)
    (tail : BetaVertexHistoryPreimage remaining current mid) :
    BetaVertexHistoryPreimage (.cons step remaining) current old := by
  cases origin with
  | boundary => cases tail;exact .boundary
  | proper origin =>
    cases tail with
    | proper earlier => exact .proper (.one (step:=step) redex origin earlier)
end BetaVertexHistoryPreimage

/-- The actual SOURCE endpoint is transported along a genuinely uncreated
incoming lineage. This theorem does not supply any successful chain or iso. -/
theorem UncreatedNodeHistoryPreimage.source_history
    {ps : List Path} {source target current : LTerm} {labels : History ps source target}
    {edge oldEdge : Path} {vertex : Vertex target}
    (trace : UncreatedNodeHistoryPreimage labels edge oldEdge)
    (lookup : target.subterm edge=some current)
    (endpoint : Source target edge vertex) :
    ∃old oldVertex,source.subterm oldEdge=some old ∧old.label=current.label ∧
      Source source oldEdge oldVertex ∧BetaVertexHistoryPreimage labels vertex oldVertex := by
  induction trace generalizing current with
  | nil => exact ⟨current,vertex,lookup,rfl,endpoint,BetaVertexHistoryPreimage.refl _ _⟩
  | @one site ps source middle target body argument beta alpha edge mid oldEdge step remaining redex origin uncreated tail ih =>
    obtain ⟨midNode,midVertex,atMid,midLabel,midSource,midTrace⟩ := ih lookup endpoint
    obtain ⟨old,atOld,oldLabel⟩ := step.beta_preimage_label redex origin atMid uncreated
    obtain ⟨oldVertex,oldSource,vertexOrigin⟩ :=
      step.beta_incidence_source_preimage redex origin atMid uncreated midSource
    exact ⟨old,oldVertex,atOld,oldLabel.trans midLabel,oldSource,
      midTrace.prepend (step:=step) redex vertexOrigin⟩
#print axioms BetaVertexHistoryPreimage.prepend
#print axioms UncreatedNodeHistoryPreimage.source_history
end Lamping.Lambda.Labelled
