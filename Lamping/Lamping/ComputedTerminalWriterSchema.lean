import Lamping.Lamping.ComputedFocusBoundaryTraversals
import Lamping.Lamping.ComputedEndpointSchemaSpecs
import Lamping.Lamping.TerminalWriterIndexBound

namespace Lamping.AG.ExposureScheduling
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {depths : B → Int}

/-- The computed terminal writer selects a forward action on the two
physical nodes of this occurrence. -/
theorem computedTerminalWriterSchema (connection : RedexConnection g)
    (balance : IndexedLevelBalance g depths) (rootDepth : depths root=0)
    (writer : ControlOccurrence g)
    (chosen : selectPhysicalControlFocus g connection.edges=some (.terminalWriter writer))
    (data : FocusCorridorData g)
    (computed : computeFocusCorridorData connection (.terminalWriter writer)=some data) :
    ∃ op schema,
      (g.label data.first.1).sort=.op op ∧
      (g.label data.last.1).sort=.op .lam ∧
      computeControlPairSchema op .lam (g.label data.first.1).index (g.label data.last.1).index=
        some (schema,false) ∧
      OrientedControlSchemaFits (schema,false) op .lam
        (g.label data.first.1).index (g.label data.last.1).index := by
  let focus : PhysicalControlFocus g := .terminalWriter writer
  let route := FocusCorridorData.toTransparentCorridor connection focus chosen data computed
  obtain ⟨a,b,labels⟩ := connection.proper.1
  have spec := selectPhysicalControlFocus_sound g connection.edges (.terminalWriter writer) chosen
  have member : writer∈controlOccurrences g connection.edges := by
    obtain ⟨earlier,split⟩ := List.getLast?_eq_some_iff.mp spec.1
    rw [split]
    exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
  obtain ⟨op,sort,control,writerRole,_reader⟩ :=
    ControlOccurrence.principal_roles labels writer member
  have shape := computed
  simp only [computeFocusCorridorData,Option.some.injEq] at shape
  subst data
  obtain ⟨_middle,left,_right⟩ :=
    computeFocusCorridorData_boundary_traversals connection focus chosen _ computed labels
  rcases left with ⟨empty,_⟩ | ⟨initial,previous,_input,_incoming,before,_pref,_arrives,_turn⟩
  · change writer.before++[writer.entry]=[] at empty
    simp at empty
  · have nonempty : focus.beforeCorridor connection.edges≠[] := by
      rw [before]
      simp
    have part := computeFocusCorridorData_partition connection focus chosen _ computed
    have split : connection.edges=focus.beforeCorridor connection.edges++route.edges := by
      simpa only [focus,PhysicalControlFocus.afterCorridor,List.append_nil,route,
        FocusCorridorData.toTransparentCorridor] using part
    have leftPrincipal : IsPrincipal (g:=g) route.first := ⟨op,sort,writerRole spec.2⟩
    have leftControl : IsControlNode (g:=g) route.first.1 := ⟨op,sort,control⟩
    have lower := connection.terminal_writer_index_lt balance rootDepth route
      leftPrincipal leftControl (focus.beforeCorridor connection.edges) nonempty split
    have lamIndex : (g.label connection.lam).index=connection.lamIndex :=
      congrArg Graph.Label.index connection.lamLabel
    obtain ⟨schema,selected,fit⟩ := computeControlPairSchema_terminal_writer control lower
    refine ⟨op,schema,sort,congrArg Graph.Label.sort connection.lamLabel,?_,?_⟩
    · simpa only [lamIndex] using selected
    · simpa only [lamIndex] using fit
end
end Lamping.AG.ExposureScheduling
