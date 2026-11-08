import Lamping.Lamping.LabelledTraceProjection
import Lamping.Lamping.LabelledEventSemantics

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

private theorem closed_after_labels {source target : LTerm} {ps : List Path}
    (labels : History ps source target) (closed : Closed source.erase) : Closed target.erase := by
  revert closed
  induction labels with
  | nil => exact id
  | cons turn _ ih => exact fun closed=>ih (turn.betaAt.beta.scoped closed)

section
variable {B : Type} [FiniteNames B]
variable {g h : ActualNet B} {root : B} {schemas : List Schema} {source target : LTerm}
  {raw : ParallelHistory source.erase target.erase}

theorem LabelledGraphProjection.graph_trace
    (projection : LabelledGraphProjection g h root schemas source target raw) :
    GraphTrace g h schemas := by
  induction projection with
  | iso same => exact .iso same
  | cons event _ ih => exact .cons event.graph_step ih

theorem LabelledGraphProjection.label_history
    (projection : LabelledGraphProjection g h root schemas source target raw) :
    History raw.derivation.paths source target := by
  induction projection with
  | iso _ => exact .nil _
  | cons event _ ih =>
    simpa only [ParallelHistory.derivation_append,Derivation.append] using
      event.label_history.append ih

/-- Raw alignment already determines its labelled schedule and fixed target
semantics, for any actual OLD schedules carried by its events. Intermediate
Matches and structural invariants are derived, not supplied per boundary.
No REP or family-maximality assertion follows from raw alignment alone. -/
theorem LabelledGraphProjection.target_matches
    (projection : LabelledGraphProjection g h root schemas source target raw)
    {directions : B → Bool} {heights : B → Int}
    (flow : FlowBalance g.net directions) (positive : directions root=true)
    (balance : IndexedLevelBalance g.net heights) (rootDepth : heights root=0)
    (inputs : RootInputs g.net root) (transparent : Transparency g.net root)
    (matching : Matches g.net root source.erase) (closed : Closed source.erase) :
    RootInputs h.net root ∧Matches h.net root target.erase := by
  induction projection with
  | iso same => exact ⟨same.rootInputs inputs,same.matches matching⟩
  | cons event tail ih =>
    have step := event.graph_step
    have nextMatching := event.target_matches flow positive balance rootDepth inputs transparent matching closed
    have nextInputs := step.rootInputs flow positive balance rootDepth inputs transparent matching
    obtain ⟨nextFlow⟩ := step.flowBalance flow
    obtain ⟨nextBalance⟩ := step.indexed_balance balance
    have nextTransparent := step.transparency_indexed flow positive balance rootDepth transparent
    exact ih nextFlow positive nextBalance rootDepth nextInputs nextTransparent nextMatching
      (closed_after_labels event.label_history closed)

end
end Lamping.AG
