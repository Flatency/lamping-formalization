import Lamping.Lamping.InitialOccurrencePaths
namespace Lamping.AG.InitialOffsets
open Graph Lambda
/-- Marker strings are explicitly present for every level 0 through p. -/
def Shape.markerWords : Shape → List (List Bool)
  | .base word => [word]
  | .lower higher word => word::higher.markerWords
@[simp] theorem Shape.markerWords_length (shape : Shape) : shape.markerWords.length=shape.offset+1 := by
  induction shape with
  | base => rfl
  | lower higher word ih => simp [Shape.markerWords,Shape.offset,ih,Nat.add_assoc]
theorem Shape.first_event (shape : Shape) (n : Nat) :
    (shape.events n).head?=some (.cro (n+shape.offset)) := by
  induction shape generalizing n with
  | base word => rfl
  | lower higher word ih =>
    simp only [Shape.events,List.head?_append,ih]
    change some (Event.cro (n+1+higher.offset))=some (Event.cro (n+(higher.offset+1)))
    congr 2
    omega
/-- A single reviewable statement of the corrected initial-loop invariants.
Only the raw source graph incidence and a proper labelling are input. -/
theorem corrected_initial_invariants (t : Term) (n : Nat)
    (es : List (Endpoint (encode n t).net)) (a b : Context)
    (loop : RawLoop (encode n t).net es a b) :
    ∃ shape : Shape,
      eventsOfEdges (encode n t).net es=shape.events ((encode n t).net.label loop.binder).index ∧
      bracketOffset (encode n t).net es=shape.offset ∧
      (eventsOfEdges (encode n t).net es).head?=
        some (.cro (((encode n t).net.label loop.binder).index+shape.offset)) ∧
      shape.markerWords.length=shape.offset+1 ∧
      b=a.replace ((encode n t).net.label loop.binder).index
        ((a.tail (((encode n t).net.label loop.binder).index+shape.offset)).cons
          (shape.level a ((encode n t).net.label loop.binder).index)) ∧
      Context.SameShell ((encode n t).net.label loop.binder).index a b ∧
      (∀ c, ∃ d, Nonempty (BindingLoop (encode n t).net es c d)) ∧
      NoBinderRevisit (encode n t).net loop.binder es := by
  obtain ⟨shape,word,offset,formula⟩ := encode_rawLoop_offset t n es a b loop
  exact ⟨shape,word,offset.symm,by rw [word,Shape.first_event],shape.markerWords_length,formula,
    encode_rawLoop_shell t n es a b loop,encode_rawLoop_transparent t n es loop,
    encode_rawLoop_no_revisit t n es a b loop⟩
end Lamping.AG.InitialOffsets
