import Lamping.Lamping.ComputedTransparentCorridor
import Lamping.Lamping.CorridorBoundaryTurns
import Lamping.Lamping.LocalTransport

namespace Lamping.AG.ExposureScheduling
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

/-- Literal data before the computed corridor, retaining physical ordinals. -/
def PhysicalControlFocus.beforeCorridor (es : List (Endpoint g)) :
    PhysicalControlFocus g → List (Endpoint g)
  | .initialReader _ => []
  | .terminalWriter occurrence => occurrence.before++[occurrence.entry]
  | .internalPeak _ writer _ => es.take (writer.physicalOrdinal+1)

/-- Literal data after the computed corridor; this includes the reader exit. -/
def PhysicalControlFocus.afterCorridor (es : List (Endpoint g)) :
    PhysicalControlFocus g → List (Endpoint g)
  | .initialReader occurrence => occurrence.exit::occurrence.after
  | .terminalWriter _ => []
  | .internalPeak _ _ reader => es.drop (reader.physicalOrdinal+1)

/-- The SAME computed focus has this exact whole occurrence partition.
Neither a caller-selected subpath nor a desired route equation is required. -/
theorem computeFocusCorridorData_partition (connection : RedexConnection g)
    (focus : PhysicalControlFocus g)
    (chosen : selectPhysicalControlFocus g connection.edges=some focus)
    (data : FocusCorridorData g) (computed : computeFocusCorridorData connection focus=some data) :
    connection.edges=(focus.beforeCorridor connection.edges++data.edges)++
      focus.afterCorridor connection.edges := by
  rw [computeFocusCorridorData_edges connection focus data computed]
  have spec := selectPhysicalControlFocus_sound g connection.edges focus chosen
  cases focus with
  | initialReader occurrence =>
    have member := List.mem_of_getElem? spec.1
    simpa only [PhysicalControlFocus.beforeCorridor,PhysicalControlFocus.afterCorridor,
      PhysicalControlFocus.skipped,List.nil_append,List.append_assoc,List.singleton_append] using
      controlOccurrences_split g connection.edges occurrence member
  | terminalWriter occurrence =>
    have member : occurrence∈controlOccurrences g connection.edges := by
      obtain ⟨earlier,split⟩ := List.getLast?_eq_some_iff.mp spec.1
      rw [split]
      exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
    simpa only [PhysicalControlFocus.beforeCorridor,PhysicalControlFocus.afterCorridor,
      PhysicalControlFocus.skipped,List.append_nil,List.append_assoc,List.singleton_append] using
      controlOccurrences_split g connection.edges occurrence member
  | internalPeak index writer reader =>
    exact controlOccurrences_internal_partition g connection.edges index writer reader spec.1 spec.2.1

/-- Both actual boundary traversals use one middle from the SAME original
whole labelling. Empty boundaries retain its real input/output contexts.
Witnesses remain in Prop and do not choose any runtime node, port or recipe. -/
theorem computeFocusCorridorData_boundary_traversals (connection : RedexConnection g)
    (focus : PhysicalControlFocus g)
    (chosen : selectPhysicalControlFocus g connection.edges=some focus)
    (data : FocusCorridorData g) (computed : computeFocusCorridorData connection focus=some data)
    {a b : Context} (labels : Labelling g connection.edges a b) :
    ∃ middle,
      (focus.beforeCorridor connection.edges=[] ∧a=middle ∨
        ∃ initial previous input, ∃ (incoming : Port (g.label data.first.1).sort),
          focus.beforeCorridor connection.edges=initial++[previous] ∧
          Labelling g (initial++[previous]) a input ∧
          g.wire previous=Sum.inl (Sigma.mk data.first.1 incoming) ∧
          Traversal (g.label data.first.1).index (g.label data.first.1).sort
            incoming data.first.2 input middle) ∧
      (focus.afterCorridor connection.edges=[] ∧middle=b ∨
        ∃ next remaining output, ∃ (outgoing : Port (g.label data.last.1).sort),
          focus.afterCorridor connection.edges=next::remaining ∧
          next=Sum.inl (Sigma.mk data.last.1 outgoing) ∧
          Traversal (g.label data.last.1).index (g.label data.last.1).sort
            data.last.2 outgoing middle output ∧
          Labelling g (next::remaining) output b) := by
  let route := FocusCorridorData.toTransparentCorridor connection focus chosen data computed
  have partition := computeFocusCorridorData_partition connection focus chosen data computed
  have whole : Labelling g
      ((focus.beforeCorridor connection.edges++route.edges)++focus.afterCorridor connection.edges) a b := by
    change Labelling g
      ((focus.beforeCorridor connection.edges++data.edges)++focus.afterCorridor connection.edges) a b
    rw [←partition]
    exact labels
  obtain ⟨middle,left,right⟩ := whole.corridor_boundary_turns route
    (focus.beforeCorridor connection.edges) (focus.afterCorridor connection.edges)
  refine ⟨middle,?_,?_⟩
  · rcases left with empty|⟨initial,previous,input,split,pref,turn⟩
    · exact Or.inl empty
    · change LabelledTurn g (g.wire previous) (Sum.inl data.first) input middle at turn
      obtain ⟨incoming,arrives,reverseRule⟩ :=
        turn.reverse.from_node data.first.1 data.first.2 rfl
      exact Or.inr ⟨initial,previous,input,incoming,split,pref,arrives,reverseRule.reverse⟩
  · rcases right with empty|⟨next,remaining,output,split,turn,suff⟩
    · exact Or.inl empty
    · change LabelledTurn g (Sum.inl data.last) next middle output at turn
      obtain ⟨outgoing,leaves,rule⟩ := turn.from_node data.last.1 data.last.2 rfl
      exact Or.inr ⟨next,remaining,output,outgoing,split,leaves,rule,suff⟩
end
end Lamping.AG.ExposureScheduling
