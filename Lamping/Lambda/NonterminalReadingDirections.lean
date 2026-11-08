import Lamping.Lambda.DirectedReadingCreation
import Lamping.Lambda.ActualIncomingLabelRoles
namespace Lamping.Lambda.Labelled

private theorem lambda_function_is_redex {t body : LTerm} {edge : Path} {stamp : Label}
    (lookup : t.subterm edge=some (.lam stamp body))
    (function : edge.getLast?=some .fn) : PrerequisiteRedexEdge t edge := by
  obtain ⟨parent,split⟩ := List.getLast?_eq_some_iff.mp function
  rw [split,LTerm.subterm_append] at lookup
  cases atParent : t.subterm parent with
  | none => rw [atParent] at lookup;cases lookup
  | some node =>
    rw [atParent,Option.bind_some] at lookup
    cases node with
    | var => cases lookup
    | lam => cases lookup
    | app appStamp fn arg =>
      have same : fn=.lam stamp body := by simpa only [LTerm.subterm,Option.some.injEq] using lookup
      subst fn
      exact ⟨parent,appStamp,stamp,body,arg,split,atParent⟩

private theorem path_not_self_function (p : Path) : p≠p++[.fn] := by
  intro equal
  have length:=congrArg List.length equal
  simp only [List.length_append,List.length_singleton] at length
  omega

/-- On a nonterminal read, the incoming FUNCTION role determines the
forward sign. The terminal applied lambda is deliberately excluded. -/
theorem PrerequisiteReadsDirected.nonredex_forward_iff_function
    (reading : PrerequisiteReadsDirected t middle edge forward)
    (notRedex : ¬PrerequisiteRedexEdge t edge) :
    forward=true ↔edge.getLast?=some .fn := by
  cases forward with
  | true =>
    constructor
    · intro _
      rw [reading.2]
      simp only [List.getLast?_append,List.getLast?_singleton,Option.some_or]
    · intro _;rfl
  | false =>
    have edgeEq : edge=middle := reading.2
    constructor
    · intro impossible;cases impossible
    · intro function
      rcases reading.1 with ⟨stamp,fn,arg,atApp,equal⟩ | ⟨stamp,body,atLambda,equal⟩
      · exact False.elim (path_not_self_function middle (edgeEq.symm.trans equal))
      · have lookup : t.subterm edge=some (.lam stamp body) := by rw [equal];exact atLambda
        exact False.elim (notRedex (lambda_function_is_redex lookup function))

/-- Equal incoming roles synchronize two real NONREDEX reads. This does
not synchronize the terminal singleton's opposite endpoint readings. -/
theorem PrerequisiteReadsDirected.nonredex_direction_eq
    (left : PrerequisiteReadsDirected t a edge forward)
    (right : PrerequisiteReadsDirected t b otherEdge otherForward)
    (leftNot : ¬PrerequisiteRedexEdge t edge) (rightNot : ¬PrerequisiteRedexEdge t otherEdge)
    (sameRole : edge.getLast?=otherEdge.getLast?) : forward=otherForward := by
  have leftRule:=left.nonredex_forward_iff_function leftNot
  have rightRule:=right.nonredex_forward_iff_function rightNot
  cases forward <;> cases otherForward
  · rfl
  · have fn := (rightRule.mp rfl)
    rw [←sameRole] at fn
    cases leftRule.mpr fn
  · have fn := leftRule.mp rfl
    rw [sameRole] at fn
    cases rightRule.mpr fn
  · rfl

/-- The incoming-role equality is derived from the SAME initial source and
actual full history; it is not an orientation premise supplied by the caller. -/
theorem History.equal_label_nonredex_read_direction
    {ps : List Path} {source target leftNode rightNode : LTerm} {edge otherEdge : Path}
    (labels : History ps source target) (initial : INIT source)
    (atLeft : target.subterm edge=some leftNode) (atRight : target.subterm otherEdge=some rightNode)
    (same : leftNode.label=rightNode.label)
    (left : PrerequisiteReadsDirected target a edge forward)
    (right : PrerequisiteReadsDirected target b otherEdge otherForward)
    (leftNot : ¬PrerequisiteRedexEdge target edge) (rightNot : ¬PrerequisiteRedexEdge target otherEdge) :
    forward=otherForward :=
  left.nonredex_direction_eq right leftNot rightNot
    (labels.incoming_role_eq_of_label initial atLeft atRight same)

#print axioms PrerequisiteReadsDirected.nonredex_forward_iff_function
#print axioms PrerequisiteReadsDirected.nonredex_direction_eq
#print axioms History.equal_label_nonredex_read_direction
end Lamping.Lambda.Labelled
