import Lamping.Lamping.LabelledTraceProjection
import Lamping.Lambda.ObservableHistory

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

section
variable {B : Type} [FiniteNames B]

/-- A raw physical projection admits deletion of its silent beta boundaries
without changing one contraction path or the existing labelled history.
This theorem does not assert whole-family maximality or reachable REP. -/
theorem GraphTrace.observable_projection {g h : ActualNet B} {schemas : List Schema}
    (trace : GraphTrace g h schemas)
    {directions : B → Bool} {heights : B → Int} {root : B}
    (flow : FlowBalance g.net directions) (positive : directions root=true)
    (balance : IndexedLevelBalance g.net heights) (rootDepth : heights root=0)
    (inputs : RootInputs g.net root) (transparent : Transparency g.net root)
    {source : LTerm} (matching : Matches g.net root source.erase) (closed : Closed source.erase) :
    ∃ (target : LTerm) (raw observed : ParallelHistory source.erase target.erase),
      LabelledGraphProjection g h root schemas source target raw ∧
      ParallelHistory.Observable observed ∧ raw.derivation=observed.derivation ∧
      PermEq raw observed ∧ History observed.derivation.paths source target ∧
      RootInputs h.net root ∧ Matches h.net root target.erase := by
  obtain ⟨target,raw,aligned,labels,finalInputs,finalMatching⟩ :=
    trace.labelled_projection flow positive balance rootDepth inputs transparent matching closed
  obtain ⟨observed,nonempty,same,permutation⟩ := raw.exists_observable
  exact ⟨target,raw,observed,aligned,nonempty,same,permutation,same ▸ labels,finalInputs,finalMatching⟩

/-- The initial labelling is retained exactly, including non-INIT labels.
Nonempty retained selections alone do not imply CompleteDerivation. -/
theorem initial_observable_trace_projection (source : LTerm) (closed : Closed source.erase)
    (target : ActualNet (Boundary source.erase)) (schemas : List Schema)
    (trace : GraphTrace (ActualNet.initial source.erase) target schemas) :
    ∃ (result : LTerm) (raw observed : ParallelHistory source.erase result.erase),
      LabelledGraphProjection (ActualNet.initial source.erase) target (.inl ()) schemas source result raw ∧
      ParallelHistory.Observable observed ∧ raw.derivation=observed.derivation ∧
      PermEq raw observed ∧ History observed.derivation.paths source result ∧
      RootInputs target.net (.inl ()) ∧ Matches target.net (.inl ()) result.erase := by
  obtain ⟨flow⟩ := encode_flowBalance source.erase 0
  obtain ⟨balance⟩ := encode_indexed_balance source.erase 0
  exact trace.observable_projection flow rfl balance rfl
    (encode_closed_independence source.erase closed 0).rootInputs
    (encode_closed_transparency source.erase closed 0) (encode_closed_matches source.erase closed 0) closed

end
end Lamping.AG
