import Lamping.Lamping.ComputedFocusNonemptySides
import Lamping.Lamping.ComputedControlSchemaTable

namespace Lamping.AG.ExposureScheduling
open Graph

private theorem intoPrincipal {index : Nat} {kind : Kind} {op : Op}
    {p q : Port kind} {a b : Context}
    (turn : Traversal index kind p q a b) (sort : kind=.op op)
    (principal : HEq q (Sum.inl () : Port (.op op))) :
    ∃ incoming : Port (.op op), Traversal index (.op op) incoming (Sum.inl ()) a b := by
  cases sort
  have eq := eq_of_heq principal
  subst q
  exact ⟨p,turn⟩

private theorem outOfPrincipal {index : Nat} {kind : Kind} {op : Op}
    {p q : Port kind} {a b : Context}
    (turn : Traversal index kind p q a b) (sort : kind=.op op)
    (principal : HEq p (Sum.inl () : Port (.op op))) :
    ∃ outgoing : Port (.op op), Traversal index (.op op) (Sum.inl ()) outgoing a b := by
  cases sort
  have eq := eq_of_heq principal
  subst p
  exact ⟨q,turn⟩

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

/-- At the selected internal peak, the actual computed nodes and their
shared-middle traversals certify the result of the finite schema table. -/
theorem computedInternalPeakSchema (connection : RedexConnection g)
    (index : Nat) (writer reader : ControlOccurrence g)
    (chosen : selectPhysicalControlFocus g connection.edges=some (.internalPeak index writer reader))
    (data : FocusCorridorData g)
    (computed : computeFocusCorridorData connection (.internalPeak index writer reader)=some data) :
    ∃ left right selected,
      (g.label data.first.1).sort=.op left ∧
      (g.label data.last.1).sort=.op right ∧
      computeControlPairSchema left right (g.label data.first.1).index (g.label data.last.1).index=
        some selected ∧
      OrientedControlSchemaFits selected left right
        (g.label data.first.1).index (g.label data.last.1).index := by
  let focus : PhysicalControlFocus g := .internalPeak index writer reader
  obtain ⟨a,b,labels⟩ := connection.proper.1
  have spec := selectPhysicalControlFocus_sound g connection.edges
    (.internalPeak index writer reader) chosen
  obtain ⟨left,leftSort,leftControl,writerRole,_⟩ :=
    ControlOccurrence.principal_roles labels writer (List.mem_of_getElem? spec.1)
  obtain ⟨right,rightSort,rightControl,_,readerRole⟩ :=
    ControlOccurrence.principal_roles labels reader (List.mem_of_getElem? spec.2.1)
  obtain ⟨incoming,arrives,rightPrincipal⟩ := readerRole spec.2.2.2.1
  have wire : g.wire reader.entry=Sum.inl (Sigma.mk reader.node incoming) := arrives
  have shape := computed
  simp only [computeFocusCorridorData,wire,nodePortOfEndpoint,Option.map_some,
    Option.some.injEq] at shape
  subst data
  have sides := selectPhysicalControlFocus_boundary_sides connection focus chosen
  obtain ⟨_middle,before,after⟩ :=
    computeFocusCorridorData_boundary_traversals connection focus chosen _ computed labels
  rcases before with ⟨empty,_⟩ | ⟨_,_,_,_,_,_,_,leftTurn⟩
  · exact False.elim (sides.1 empty)
  rcases after with ⟨empty,_⟩ | ⟨_,_,_,_,_,_,rightTurn,_⟩
  · exact False.elim (sides.2 empty)
  obtain ⟨_,leftRule⟩ := intoPrincipal leftTurn leftSort (writerRole spec.2.2.1)
  obtain ⟨_,rightRule⟩ := outOfPrincipal rightTurn rightSort rightPrincipal
  obtain ⟨selected,result,fit⟩ :=
    computeControlPairSchema_correct leftControl rightControl leftRule rightRule
  exact ⟨left,right,selected,leftSort,rightSort,result,fit⟩
end
end Lamping.AG.ExposureScheduling
