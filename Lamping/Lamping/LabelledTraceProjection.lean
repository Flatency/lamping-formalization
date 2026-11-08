import Lamping.Lamping.LabelledGraphEvents
import Lamping.Lamping.GraphTraceSoundness

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

section
variable {B : Type} [FiniteNames B]

/-- Raw event alignment retains actual beta-site evidence at every graph
step. Empty beta selections are still present. CompleteDerivation is NOT
a field or a consequence of the definition. -/
inductive LabelledGraphProjection : ActualNet B → ActualNet B → B → List Schema →
    (source target : LTerm) → ParallelHistory source.erase target.erase → Prop where
  | iso {g h : ActualNet B} {root : B} {source : LTerm} (same : NetIso g.net h.net) :
      LabelledGraphProjection g h root [] source source (.nil source.erase)
  | cons {g h k : ActualNet B} {root : B} {s : Schema} {ss : List Schema}
      {source middle target : LTerm}
      {first : ParallelHistory source.erase middle.erase}
      {rest : ParallelHistory middle.erase target.erase}
      (event : LabelledGraphEvent s g h root source middle first)
      (tail : LabelledGraphProjection h k root ss middle target rest) :
      LabelledGraphProjection g k root (s::ss) source target (first.append rest)

private theorem labels_closed {source target : LTerm} {ps : List Path}
    (labels : History ps source target) (closed : Closed source.erase) : Closed target.erase := by
  revert closed
  induction labels with
  | nil => exact id
  | cons turn _ ih => exact fun closed => ih (turn.betaAt.beta.scoped closed)

/-- Actual finite traces construct a globally transported labelled history
with raw parallel step boundaries. No intermediate matching, family purity
or complete-projection certificate is supplied by the caller. -/
theorem GraphTrace.labelled_projection {g h : ActualNet B} {schemas : List Schema}
    (trace : GraphTrace g h schemas)
    {directions : B → Bool} {heights : B → Int} {root : B}
    (flow : FlowBalance g.net directions) (positive : directions root=true)
    (balance : IndexedLevelBalance g.net heights) (rootDepth : heights root=0)
    (inputs : RootInputs g.net root) (oldT : Transparency g.net root)
    {source : LTerm} (matching : Matches g.net root source.erase) (closed : Closed source.erase) :
    ∃ (target : LTerm) (projection : ParallelHistory source.erase target.erase),
      LabelledGraphProjection g h root schemas source target projection ∧
      History projection.derivation.paths source target ∧
      RootInputs h.net root ∧ Matches h.net root target.erase := by
  induction trace generalizing source with
  | iso same => exact ⟨source,.nil _,.iso same,.nil _,same.rootInputs inputs,same.matches matching⟩
  | cons step tail ih =>
    obtain ⟨middle,first,event,labels,nextMatching⟩ :=
      step.labelled_event flow positive balance rootDepth inputs oldT matching closed
    have nextInputs := step.rootInputs flow positive balance rootDepth inputs oldT matching
    obtain ⟨nextFlow⟩ := step.flowBalance flow
    obtain ⟨nextBalance⟩ := step.indexed_balance balance
    have nextT := step.transparency_indexed flow positive balance rootDepth oldT
    obtain ⟨target,rest,remaining,remainingLabels,finalInputs,finalMatching⟩ :=
      ih nextFlow nextBalance nextInputs nextT nextMatching (labels_closed labels closed)
    refine ⟨target,first.append rest,.cons event remaining,?_,finalInputs,finalMatching⟩
    simpa only [ParallelHistory.derivation_append,Derivation.append] using labels.append remainingLabels

/-- The source may be any existing labelling of the closed initial term.
INIT is not repeated at intermediate steps. This is a raw projection, not
the P09 complete-family projection theorem. -/
theorem initial_labelled_trace_projection (source : LTerm) (closed : Closed source.erase)
    (target : ActualNet (Boundary source.erase)) (schemas : List Schema)
    (trace : GraphTrace (ActualNet.initial source.erase) target schemas) :
    ∃ (result : LTerm) (projection : ParallelHistory source.erase result.erase),
      LabelledGraphProjection (ActualNet.initial source.erase) target (.inl ()) schemas
        source result projection ∧ History projection.derivation.paths source result ∧
      RootInputs target.net (.inl ()) ∧ Matches target.net (.inl ()) result.erase := by
  obtain ⟨flow⟩ := encode_flowBalance source.erase 0
  obtain ⟨balance⟩ := encode_indexed_balance source.erase 0
  exact trace.labelled_projection flow rfl balance rfl (encode_closed_independence source.erase closed 0).rootInputs
    (encode_closed_transparency source.erase closed 0) (encode_closed_matches source.erase closed 0) closed

end
end Lamping.AG
