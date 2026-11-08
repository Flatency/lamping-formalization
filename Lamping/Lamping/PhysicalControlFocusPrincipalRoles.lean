import Lamping.Lamping.ControlWordOccurrenceTurns

namespace Lamping.AG.ExposureScheduling
open Graph

private theorem singleton_control_kind (kind : Kind) (p : Port kind) (bit : Bool)
    (letter : controlPortWord kind p=[bit]) :
    ∃ op,kind=.op op ∧ (op=.fan ∨ op=.cro ∨ op=.bra) := by
  cases kind with
  | garbage => simp [controlPortWord] at letter
  | op op =>
    cases op with
    | app => simp [controlPortWord] at letter
    | lam => simp [controlPortWord] at letter
    | fan => exact ⟨.fan,rfl,Or.inl rfl⟩
    | cro => exact ⟨.cro,rfl,Or.inr (Or.inl rfl)⟩
    | bra => exact ⟨.bra,rfl,Or.inr (Or.inr rfl)⟩

private theorem writer_token_principal {kind : Kind} {op : Op}
    (sort : kind=.op op) (control : op=.fan ∨ op=.cro ∨ op=.bra)
    (p : Port kind) (letter : controlPortWord kind p=[true]) :
    HEq p (Sum.inl () : Port (.op op)) := by
  cases sort
  rcases control with rfl|rfl|rfl <;> cases p with
  | inl u => cases u; exact HEq.rfl
  | inr q => simp [controlPortWord] at letter

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

/-- Read the principal roles of the SAME actual emitted occurrence. Reader
incoming ports are proved to be the actual wire mate, not chosen as data. -/
theorem ControlOccurrence.principal_roles {es : List (Endpoint g)} {a b : Context}
    (labels : Labelling g es a b) (o : ControlOccurrence g)
    (member : o ∈ controlOccurrences g es) :
    ∃ op,(g.label o.node).sort=.op op ∧ (op=.fan ∨ op=.cro ∨ op=.bra) ∧
      (o.bit=true → HEq o.outgoing (Sum.inl () : Port (.op op))) ∧
      (o.bit=false → ∃ p : Port (g.label o.node).sort,
        o.incomingEndpoint=Sum.inl ⟨o.node,p⟩ ∧ HEq p (Sum.inl () : Port (.op op))) := by
  have letter := controlOccurrences_letter g es o member
  obtain ⟨op,sort,control⟩ := singleton_control_kind (g.label o.node).sort o.outgoing o.bit letter
  refine ⟨op,sort,control,?_,?_⟩
  · intro writer
    have actualLetter : controlPortWord (g.label o.node).sort o.outgoing=[true] := by
      rw [writer] at letter
      exact letter
    exact writer_token_principal sort control o.outgoing actualLetter
  · intro reader
    obtain ⟨_left,_right,incoming,_oldPrefix,arrives,_turn,_oldSuffix,incomingLetter⟩ :=
      controlOccurrences_labelled_turn g es labels o member
    have actualLetter : controlPortWord (g.label o.node).sort incoming=[true] := by
      rw [reader] at incomingLetter
      simpa only [Bool.not_false] using incomingLetter
    exact ⟨incoming,arrives,writer_token_principal sort control incoming actualLetter⟩
end
end Lamping.AG.ExposureScheduling
