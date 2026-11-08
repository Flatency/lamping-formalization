import Lamping.Lamping.ComputedFocusBoundaryTraversals
import Lamping.Lamping.ComputedEndpointSchemaSpecs
import Lamping.Lamping.InitialReaderIndexBound

namespace Lamping.AG.ExposureScheduling
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {depths : B → Int}

/-- The actual initial reader determines the reverse branch of the finite
table on the two computed physical nodes. -/
theorem computedInitialReaderSchema {t : Term} {redex : RedexOcc t}
    (access : ActualRedexAccess g root redex)
    (inputs : RootInputs g root) (balance : IndexedLevelBalance g depths)
    (rootDepth : depths root=0) (reader : ControlOccurrence g)
    (chosen : selectPhysicalControlFocus g access.connection.edges=some (.initialReader reader))
    (data : FocusCorridorData g)
    (computed : computeFocusCorridorData access.connection (.initialReader reader)=some data) :
    ∃ op schema,
      (g.label data.first.1).sort=.op .app ∧
      (g.label data.last.1).sort=.op op ∧
      computeControlPairSchema .app op (g.label data.first.1).index (g.label data.last.1).index=
        some (schema,true) ∧
      OrientedControlSchemaFits (schema,true) .app op
        (g.label data.first.1).index (g.label data.last.1).index := by
  let focus : PhysicalControlFocus g := .initialReader reader
  let route := FocusCorridorData.toTransparentCorridor access.connection focus chosen data computed
  obtain ⟨a,b,labels⟩ := access.connection.proper.1
  have spec := selectPhysicalControlFocus_sound g access.connection.edges (.initialReader reader) chosen
  obtain ⟨op,sort,control,_writer,readerRole⟩ :=
    ControlOccurrence.principal_roles labels reader (List.mem_of_getElem? spec.1)
  obtain ⟨incoming,arrives,principal⟩ := readerRole spec.2
  have wire : g.wire reader.entry=Sum.inl (Sigma.mk reader.node incoming) := arrives
  have shape := computed
  simp only [computeFocusCorridorData,wire,nodePortOfEndpoint,Option.map_some,
    Option.some.injEq] at shape
  subst data
  obtain ⟨middle,_left,right⟩ :=
    computeFocusCorridorData_boundary_traversals access.connection focus chosen _ computed labels
  rcases right with ⟨empty,_⟩ | ⟨next,remaining,output,outgoing,after,_leaves,_turn,_suff⟩
  · change reader.exit::reader.after=[] at empty
    cases empty
  · have part := computeFocusCorridorData_partition access.connection focus chosen _ computed
    have split : access.connection.edges=route.edges++next::remaining := by
      change access.connection.edges=(_++_)++_ at part
      rw [after] at part
      simpa only [focus,PhysicalControlFocus.beforeCorridor,List.nil_append,route,
        FocusCorridorData.toTransparentCorridor] using part
    have rightPrincipal : IsPrincipal (g:=g) route.last := ⟨op,sort,principal⟩
    have rightControl : IsControlNode (g:=g) route.last.1 := ⟨op,sort,control⟩
    have lower := access.initial_reader_index_lt inputs balance rootDepth route
      rightPrincipal rightControl next remaining split
    have appIndex : (g.label access.connection.app).index=access.connection.appIndex :=
      congrArg Graph.Label.index access.connection.appLabel
    obtain ⟨schema,selected,fit⟩ := computeControlPairSchema_initial_reader control lower
    refine ⟨op,schema,congrArg Graph.Label.sort access.connection.appLabel,sort,?_,?_⟩
    · simpa only [appIndex] using selected
    · simpa only [appIndex] using fit
end
end Lamping.AG.ExposureScheduling
