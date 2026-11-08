import Lamping.Lamping.ExposureControlWords

namespace Lamping.AG.ExposureScheduling
open Graph

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]

/-- Data from one literal overlapping pair; no semantic validity or chosen
position proof is stored. Repeated visits retain different before/after data. -/
structure ControlOccurrence (g : Net signature N B W) where
  before : List (Endpoint g)
  entry : Endpoint g
  node : N
  outgoing : Port (g.label node).sort
  after : List (Endpoint g)
  bit : Bool

def ControlOccurrence.exit {g : Net signature N B W} (occurrence : ControlOccurrence g) : Endpoint g :=
  .inl ⟨occurrence.node,occurrence.outgoing⟩

def ControlOccurrence.physicalOrdinal {g : Net signature N B W}
    (occurrence : ControlOccurrence g) : Nat := occurrence.before.length

def ControlOccurrence.incomingEndpoint {g : Net signature N B W}
    (occurrence : ControlOccurrence g) : Endpoint g := g.wire occurrence.entry

/-- Classify the actual exit using the old controlPortWord data function. -/
def occurrenceAt (g : Net signature N B W) (before : List (Endpoint g))
    (entry exit : Endpoint g) (after : List (Endpoint g)) : Option (ControlOccurrence g) :=
  match exit with
  | .inl ⟨node,outgoing⟩ =>
      (controlPortWord (g.label node).sort outgoing).head?.map fun bit =>
        ⟨before,entry,node,outgoing,after,bit⟩
  | .inr _ => none

/-- Overlap, rather than consume disjoint pairs: entry::exit::after recurses
on exit::after and extends the literal prefix by exactly entry. -/
def scanFrom (g : Net signature N B W) :
    List (Endpoint g) → List (Endpoint g) → List (ControlOccurrence g)
  | before,entry::exit::after =>
      (occurrenceAt g before entry exit after).toList ++ scanFrom g (before++[entry]) (exit::after)
  | _,_ => []

def controlOccurrences (g : Net signature N B W) (es : List (Endpoint g)) :
    List (ControlOccurrence g) := scanFrom g [] es

/-- Every existing port emits zero or one control bit. No arbitrary head of
a multi-letter word is silently discarded by occurrenceAt. -/
theorem controlPortWord_head_toList (kind : Kind) (port : Port kind) :
    (controlPortWord kind port).head?.toList=controlPortWord kind port := by
  cases kind with
  | garbage => rfl
  | op op => cases op <;> cases port <;> rfl

theorem occurrenceAt_bits (g : Net signature N B W) (before : List (Endpoint g))
    (entry exit : Endpoint g) (after : List (Endpoint g)) :
    ((occurrenceAt g before entry exit after).toList).map ControlOccurrence.bit=
      match exit with
      | .inl ⟨node,outgoing⟩ => controlPortWord (g.label node).sort outgoing
      | .inr _ => [] := by
  cases exit with
  | inr boundary => rfl
  | inl nodeport =>
    rcases nodeport with ⟨node,outgoing⟩
    calc
      ((occurrenceAt g before entry (.inl ⟨node,outgoing⟩) after).toList).map ControlOccurrence.bit =
          (controlPortWord (g.label node).sort outgoing).head?.toList := by
        simp only [occurrenceAt]
        cases (controlPortWord (g.label node).sort outgoing).head? <;> rfl
      _ = _ := controlPortWord_head_toList _ _

theorem scanFrom_bits (g : Net signature N B W) (before es : List (Endpoint g)) :
    (scanFrom g before es).map ControlOccurrence.bit=controlWord g es := by
  induction es generalizing before with
  | nil => rfl
  | cons entry tail ih =>
    cases tail with
    | nil => rfl
    | cons exit after =>
      rw [scanFrom,List.map_append,occurrenceAt_bits,ih]
      cases exit <;> rfl

theorem controlOccurrences_bits (g : Net signature N B W) (es : List (Endpoint g)) :
    (controlOccurrences g es).map ControlOccurrence.bit=controlWord g es := scanFrom_bits g [] es

#print axioms Lamping.AG.ExposureScheduling.ControlOccurrence
#print axioms Lamping.AG.ExposureScheduling.ControlOccurrence.exit
#print axioms Lamping.AG.ExposureScheduling.ControlOccurrence.physicalOrdinal
#print axioms Lamping.AG.ExposureScheduling.ControlOccurrence.incomingEndpoint
#print axioms Lamping.AG.ExposureScheduling.occurrenceAt
#print axioms Lamping.AG.ExposureScheduling.scanFrom
#print axioms Lamping.AG.ExposureScheduling.controlOccurrences
#print axioms Lamping.AG.ExposureScheduling.controlPortWord_head_toList
#print axioms Lamping.AG.ExposureScheduling.occurrenceAt_bits
#print axioms Lamping.AG.ExposureScheduling.scanFrom_bits
#print axioms Lamping.AG.ExposureScheduling.controlOccurrences_bits

end
end Lamping.AG.ExposureScheduling
