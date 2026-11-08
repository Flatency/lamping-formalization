import Lamping.Lambda.UncreatedSourceHistory
namespace Lamping.Lambda.Labelled
open SyntaxIncidence

theorem BetaVertexHistoryPreimage.unique
    {ps : List Path} {source target : LTerm} {labels : History ps source target}
    {vertex : Vertex target} {first second : Vertex source}
    (left : BetaVertexHistoryPreimage labels vertex first)
    (right : BetaVertexHistoryPreimage labels vertex second) : first=second := by
  cases left with
  | boundary => cases right;rfl
  | proper left =>
    cases right with
    | proper right =>
      have equal := left.unique right
      congr 1
      exact Subtype.ext equal

/-- The TARGET endpoint follows the SAME actual node history, including
created incoming edges. No successful chain is assumed or completed. -/
theorem BetaNodeHistoryPreimage.target_history
    {ps : List Path} {source target : LTerm} {labels : History ps source target}
    {edge oldEdge : Path} {vertex : Vertex target}
    (trace : BetaNodeHistoryPreimage labels edge oldEdge)
    (endpoint : Target target edge vertex) :
    ∃oldVertex,Target source oldEdge oldVertex ∧
      BetaVertexHistoryPreimage labels vertex oldVertex := by
  induction trace with
  | nil => exact ⟨vertex,endpoint,BetaVertexHistoryPreimage.refl _ _⟩
  | @one site ps source middle target body argument beta alpha edge mid oldEdge step remaining redex origin tail ih =>
    obtain ⟨midVertex,midTarget,midTrace⟩ := ih endpoint
    obtain ⟨oldVertex,oldTarget,vertexOrigin⟩ :=
      step.beta_incidence_target_preimage redex origin midTarget
    exact ⟨oldVertex,oldTarget,midTrace.prepend (step:=step) redex vertexOrigin⟩
end Lamping.Lambda.Labelled
