import Lamping.Lamping.ControlWordFocusGaps
import Lamping.Lamping.PhysicalControlFocusPrincipalRoles

namespace Lamping.AG.ExposureScheduling
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]

/-- Bare computed geometry only. No validity, schema, rank, or desired image
is stored in the data returned by the selector. -/
structure FocusCorridorData (g : Net signature N B W) where
  first : NodePort signature N g.label
  last : NodePort signature N g.label
  edges : List (Endpoint g)

def nodePortOfEndpoint (g : Net signature N B W) : Endpoint g → Option (NodePort signature N g.label)
  | Sum.inl p => some p
  | Sum.inr _ => none

theorem nodePortOfEndpoint_eq_some_iff (g : Net signature N B W)
    (e : Endpoint g) (p : NodePort signature N g.label) :
    nodePortOfEndpoint g e=some p ↔ e=Sum.inl p := by
  cases e <;> simp [nodePortOfEndpoint]

/-- Select both actual endpoints and the complete skipped list from fixed
data. In particular the reader endpoint is computed by the actual wire. -/
def computeFocusCorridorData {g : Net signature N B W}
    (connection : RedexConnection g) (focus : PhysicalControlFocus g) :
    Option (FocusCorridorData g) :=
  match focus with
  | .initialReader o =>
      (nodePortOfEndpoint g (g.wire o.entry)).map fun last =>
        { first := Sigma.mk connection.app connection.appPort
          last := last
          edges := focus.skipped connection.edges }
  | .terminalWriter o =>
      some { first := Sigma.mk o.node o.outgoing
             last := Sigma.mk connection.lam connection.lamPort
             edges := focus.skipped connection.edges }
  | .internalPeak _ writer reader =>
      (nodePortOfEndpoint g (g.wire reader.entry)).map fun last =>
        { first := Sigma.mk writer.node writer.outgoing
          last := last
          edges := focus.skipped connection.edges }

/-- Even before semantic validation, successful computation retains exactly
the whole interval selected by this same physical focus. -/
theorem computeFocusCorridorData_edges {g : Net signature N B W}
    (connection : RedexConnection g) (focus : PhysicalControlFocus g)
    (data : FocusCorridorData g) (computed : computeFocusCorridorData connection focus=some data) :
    data.edges=focus.skipped connection.edges := by
  cases focus with
  | initialReader o =>
    cases h : nodePortOfEndpoint g (g.wire o.entry) with
    | none => simp [computeFocusCorridorData,h] at computed
    | some last =>
      simp only [computeFocusCorridorData,h,Option.map_some,Option.some.injEq] at computed
      cases computed
      rfl
  | terminalWriter _o =>
    simp only [computeFocusCorridorData,Option.some.injEq] at computed
    cases computed
    rfl
  | internalPeak _index _writer reader =>
    cases h : nodePortOfEndpoint g (g.wire reader.entry) with
    | none => simp [computeFocusCorridorData,h] at computed
    | some last =>
      simp only [computeFocusCorridorData,h,Option.map_some,Option.some.injEq] at computed
      cases computed
      rfl

/-- Actual selected readers have a node at their computed incoming endpoint.
The proof justifies the data match; it never chooses the program's port. -/
theorem computeFocusCorridorData_ne_none {g : Net signature N B W}
    (connection : RedexConnection g) (focus : PhysicalControlFocus g)
    (chosen : selectPhysicalControlFocus g connection.edges=some focus) :
    computeFocusCorridorData connection focus≠none := by
  have spec := selectPhysicalControlFocus_sound g connection.edges focus chosen
  cases focus with
  | initialReader o =>
    have member : o∈controlOccurrences g connection.edges := List.mem_of_getElem? spec.1
    obtain ⟨a,b,labels⟩ := connection.proper.1
    obtain ⟨_op,_sort,_control,_writer,reader⟩ := ControlOccurrence.principal_roles labels o member
    obtain ⟨incoming,arrives,_principal⟩ := reader spec.2
    have actualWire : g.wire o.entry=Sum.inl (Sigma.mk o.node incoming) := arrives
    simp only [computeFocusCorridorData,actualWire,nodePortOfEndpoint,Option.map_some]
    intro impossible
    cases impossible
  | terminalWriter _o =>
    simp only [computeFocusCorridorData]
    intro impossible
    cases impossible
  | internalPeak _index _writer reader =>
    have member : reader∈controlOccurrences g connection.edges := List.mem_of_getElem? spec.2.1
    obtain ⟨a,b,labels⟩ := connection.proper.1
    obtain ⟨_op,_sort,_control,_writer,readerRole⟩ := ControlOccurrence.principal_roles labels reader member
    obtain ⟨incoming,arrives,_principal⟩ := readerRole spec.2.2.2.1
    have actualWire : g.wire reader.entry=Sum.inl (Sigma.mk reader.node incoming) := arrives
    simp only [computeFocusCorridorData,actualWire,nodePortOfEndpoint,Option.map_some]
    intro impossible
    cases impossible
end
end Lamping.AG.ExposureScheduling
