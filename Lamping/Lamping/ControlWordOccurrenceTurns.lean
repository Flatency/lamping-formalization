import Lamping.Lamping.ControlWordPhysicalFocus
import Lamping.Lamping.FirstNodeDecomposition
import Lamping.Lamping.LocalTransport

namespace Lamping.AG.ExposureScheduling
open Graph

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]

private theorem member_some {A : Type} {value : A} {optional : Option A}
    (member : value∈optional.toList) : optional=some value := by
  cases optional with
  | none => cases member
  | some other =>
    have same : value=other := List.mem_singleton.mp member
    cases same
    rfl

theorem scanFrom_self_emit (g : Net signature N B W) (before es : List (Endpoint g))
    (occurrence : ControlOccurrence g) (member : occurrence∈scanFrom g before es) :
    occurrenceAt g occurrence.before occurrence.entry occurrence.exit occurrence.after=some occurrence := by
  revert member
  induction es generalizing before with
  | nil => intro member; cases member
  | cons entry tail ih =>
    intro member
    cases tail with
    | nil => cases member
    | cons exit after =>
      change occurrence∈(occurrenceAt g before entry exit after).toList++
        scanFrom g (before++[entry]) (exit::after) at member
      rcases List.mem_append.mp member with current | later
      · have picked := member_some current
        obtain ⟨beforeEq,entryEq,exitEq,afterEq⟩ :=
          occurrenceAt_geometry g before entry exit after occurrence picked
        rw [beforeEq,entryEq,exitEq,afterEq]
        exact picked
      · exact ih (before++[entry]) later

theorem controlOccurrences_letter (g : Net signature N B W) (es : List (Endpoint g))
    (occurrence : ControlOccurrence g) (member : occurrence∈controlOccurrences g es) :
    controlPortWord (g.label occurrence.node).sort occurrence.outgoing=[occurrence.bit] := by
  have picked := scanFrom_self_emit g [] es occurrence member
  have projected := occurrenceAt_bits g occurrence.before occurrence.entry occurrence.exit occurrence.after
  rw [picked] at projected
  simpa only [ControlOccurrence.exit,Option.toList,List.map_cons,List.map_nil] using projected.symm

private theorem incoming_letter {index : Nat} {kind : Kind} {p q : Port kind}
    {a b : Context} (turn : Traversal index kind p q a b) (bit : Bool)
    (letter : controlPortWord kind q=[bit]) : controlPortWord kind p=[!bit] := by
  cases turn with
  | direct passage => cases passage <;> cases bit <;> simp_all [controlPortWord,fanO,fanStar]
  | inverse passage => cases passage <;> cases bit <;> simp_all [controlPortWord,fanO,fanStar]

/-- Labels justify the SAME fixed data turn. Existential port/context
witnesses are used only in this proposition, never to create scan records. -/
theorem controlOccurrences_labelled_turn (g : Net signature N B W) (es : List (Endpoint g))
    {a b : Context} (labels : Labelling g es a b) (occurrence : ControlOccurrence g)
    (member : occurrence∈controlOccurrences g es) :
    ∃ (left right : Context) (incoming : Port (g.label occurrence.node).sort),
      Labelling g (occurrence.before++[occurrence.entry]) a left ∧
      occurrence.incomingEndpoint=.inl ⟨occurrence.node,incoming⟩ ∧
      Traversal (g.label occurrence.node).index (g.label occurrence.node).sort
        incoming occurrence.outgoing left right ∧
      Labelling g (occurrence.exit::occurrence.after) right b ∧
      controlPortWord (g.label occurrence.node).sort incoming=[!occurrence.bit] := by
  have whole : Labelling g
      (occurrence.before++occurrence.entry::occurrence.exit::occurrence.after) a b := by
    rw [←controlOccurrences_split g es occurrence member]
    exact labels
  obtain ⟨left,oldPrefix,suffix⟩ := whole.split_segment
  cases suffix with
  | cons turn rest =>
    obtain ⟨incoming,arrives,reverseRule⟩ :=
      turn.reverse.from_node occurrence.node occurrence.outgoing rfl
    have rule := reverseRule.reverse
    exact ⟨left,_,incoming,oldPrefix,arrives,rule,rest,
      incoming_letter rule occurrence.bit (controlOccurrences_letter g es occurrence member)⟩

private theorem pair_cut {A : Type} (es : List A) (e f : A)
    (member : (e,f)∈es.zip es.tail) : ∃ before after,es=before++e::f::after := by
  induction es with
  | nil => cases member
  | cons first tail ih =>
    cases tail with
    | nil => cases member
    | cons second tail =>
      rcases List.mem_cons.mp member with same | later
      · obtain ⟨rfl,rfl⟩ := Prod.mk.inj same
        exact ⟨[],tail,rfl⟩
      · obtain ⟨before,after,split⟩ := ih later
        exact ⟨first::before,after,congrArg (List.cons first) split⟩

private theorem pair_at_cut {A : Type} (before : List A) (e f : A) (after : List A) :
    (e,f)∈(before++e::f::after).zip (before++e::f::after).tail := by
  induction before with
  | nil => exact List.mem_cons.mpr (Or.inl rfl)
  | cons first before ih => cases before with
    | nil => exact List.mem_cons_of_mem _ ih
    | cons second before => exact List.mem_cons_of_mem _ ih

private theorem zip_right_member {A C : Type} {xs : List A} {ys : List C} {a : A} {b : C}
    (member : (a,b)∈xs.zip ys) : b∈ys := by
  induction xs generalizing ys with
  | nil => simp at member
  | cons x xs ih =>
    cases ys with
    | nil => simp at member
    | cons y ys =>
      rcases List.mem_cons.mp member with same |rest
      · exact List.mem_cons.mpr (Or.inl (congrArg Prod.snd same))
      · exact List.mem_cons_of_mem _ (ih rest)

private theorem controlled_nonempty (kind : Kind) (port : Port kind)
    (control : ∃ op,kind=Kind.op op ∧(op=Op.fan ∨op=Op.cro ∨op=Op.bra)) :
    controlPortWord kind port≠[] := by
  rcases control with ⟨op,rfl,controlled⟩
  rcases controlled with rfl|rfl|rfl <;> cases port <;> intro impossible <;> cases impossible

/-- An actual literal interval of THIS connection is transparent when the
computed scan emits no records. No transparency certificate is an input. -/
theorem connection_zero_scan_interval {g : Net signature N B W} (connection : RedexConnection g)
    (pre segment post : List (Endpoint g)) (literal : connection.edges=pre++segment++post)
    (empty : controlOccurrences g segment=[]) : TransparentTurns (g:=g) segment := by
  have zero : controlWord g segment=[] := by
    have projected := controlOccurrences_bits g segment
    rw [empty] at projected
    exact projected.symm
  intro e f member
  obtain ⟨before,after,cut⟩ := pair_cut segment e f member
  have whole : connection.edges=(pre++before)++e::f::(after++post) := by
    rw [literal,cut]
    simp only [List.append_assoc,List.cons_append]
  have wholeMember : (e,f)∈connection.edges.zip connection.edges.tail := by
    rw [whole]; exact pair_at_cut _ _ _ _
  rcases connection.control_only e f wholeMember with transparent |
      ⟨node,p,q,op,sort,controlled,_arrives,leaves⟩
  · exact transparent
  · have atExit := (List.flatMap_eq_nil_iff.mp zero) f (zip_right_member member)
    rw [leaves] at atExit
    change controlPortWord (g.label node).sort q=[] at atExit
    exact False.elim ((controlled_nonempty (g.label node).sort q ⟨op,sort,controlled⟩) atExit)

theorem occurrence_prefix_zero_scan_transparent {g : Net signature N B W}
    (connection : RedexConnection g) (occurrence : ControlOccurrence g)
    (member : occurrence∈controlOccurrences g connection.edges)
    (empty : controlOccurrences g (occurrence.before++[occurrence.entry])=[]) :
    TransparentTurns (g:=g) (occurrence.before++[occurrence.entry]) := by
  apply connection_zero_scan_interval connection [] (occurrence.before++[occurrence.entry])
    (occurrence.exit::occurrence.after) ?_ empty
  simpa only [List.nil_append,List.append_assoc,List.singleton_append] using
    controlOccurrences_split g connection.edges occurrence member

theorem occurrence_suffix_zero_scan_transparent {g : Net signature N B W}
    (connection : RedexConnection g) (occurrence : ControlOccurrence g)
    (member : occurrence∈controlOccurrences g connection.edges)
    (empty : controlOccurrences g (occurrence.exit::occurrence.after)=[]) :
    TransparentTurns (g:=g) (occurrence.exit::occurrence.after) := by
  apply connection_zero_scan_interval connection (occurrence.before++[occurrence.entry])
    (occurrence.exit::occurrence.after) [] ?_ empty
  simpa only [List.append_nil,List.append_assoc,List.singleton_append] using
    controlOccurrences_split g connection.edges occurrence member

#print axioms Lamping.AG.ExposureScheduling.scanFrom_self_emit
#print axioms Lamping.AG.ExposureScheduling.controlOccurrences_letter
#print axioms Lamping.AG.ExposureScheduling.controlOccurrences_labelled_turn
#print axioms Lamping.AG.ExposureScheduling.connection_zero_scan_interval
#print axioms Lamping.AG.ExposureScheduling.occurrence_prefix_zero_scan_transparent
#print axioms Lamping.AG.ExposureScheduling.occurrence_suffix_zero_scan_transparent

end
end Lamping.AG.ExposureScheduling
