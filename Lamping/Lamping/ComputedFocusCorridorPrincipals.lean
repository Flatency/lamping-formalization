import Lamping.Lamping.ComputedFocusCorridorData
import Lamping.Lamping.PrincipalCorridorExtraction

namespace Lamping.AG.ExposureScheduling
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

/-- Both ports of THIS computed focus corridor are actual principal ports.
Existential operation/port witnesses are consumed only inside this proposition. -/
theorem computeFocusCorridorData_principals (connection : RedexConnection g)
    (focus : PhysicalControlFocus g)
    (chosen : selectPhysicalControlFocus g connection.edges=some focus)
    (data : FocusCorridorData g) (computed : computeFocusCorridorData connection focus=some data) :
    IsPrincipal (g:=g) data.first ∧ IsPrincipal (g:=g) data.last := by
  have spec := selectPhysicalControlFocus_sound g connection.edges focus chosen
  obtain ⟨a,b,labels⟩ := connection.proper.1
  cases focus with
  | initialReader occurrence =>
    have member := List.mem_of_getElem? spec.1
    obtain ⟨op,sort,_control,_writer,reader⟩ :=
      ControlOccurrence.principal_roles labels occurrence member
    obtain ⟨incoming,arrives,principal⟩ := reader spec.2
    have actualWire : g.wire occurrence.entry=Sum.inl (Sigma.mk occurrence.node incoming) := arrives
    simp only [computeFocusCorridorData,actualWire,nodePortOfEndpoint,Option.map_some,
      Option.some.injEq] at computed
    cases computed
    exact ⟨⟨.app,congrArg (fun l : Graph.Label signature => l.sort) connection.appLabel,
      connection.appPrincipal⟩,⟨op,sort,principal⟩⟩
  | terminalWriter occurrence =>
    have member : occurrence∈controlOccurrences g connection.edges := by
      obtain ⟨earlier,split⟩ := List.getLast?_eq_some_iff.mp spec.1
      rw [split]
      exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
    obtain ⟨op,sort,_control,writer,_reader⟩ :=
      ControlOccurrence.principal_roles labels occurrence member
    simp only [computeFocusCorridorData,Option.some.injEq] at computed
    cases computed
    exact ⟨⟨op,sort,writer spec.2⟩,
      ⟨.lam,congrArg (fun l : Graph.Label signature => l.sort) connection.lamLabel,
        connection.lamPrincipal⟩⟩
  | internalPeak _index writer reader =>
    have writerMember := List.mem_of_getElem? spec.1
    have readerMember := List.mem_of_getElem? spec.2.1
    obtain ⟨leftOp,leftSort,_leftControl,writerRole,_leftReader⟩ :=
      ControlOccurrence.principal_roles labels writer writerMember
    obtain ⟨rightOp,rightSort,_rightControl,_rightWriter,readerRole⟩ :=
      ControlOccurrence.principal_roles labels reader readerMember
    obtain ⟨incoming,arrives,principal⟩ := readerRole spec.2.2.2.1
    have actualWire : g.wire reader.entry=Sum.inl (Sigma.mk reader.node incoming) := arrives
    simp only [computeFocusCorridorData,actualWire,nodePortOfEndpoint,Option.map_some,
      Option.some.injEq] at computed
    cases computed
    exact ⟨⟨leftOp,leftSort,writerRole spec.2.2.1⟩,⟨rightOp,rightSort,principal⟩⟩
end
end Lamping.AG.ExposureScheduling
