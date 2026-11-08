import Lamping.Checks.Q0LocalModelTransparency
import Lamping.Lamping.ChainRepresentation
import Lamping.Lamping.MatchingSharedSyntaxEvaluation

namespace Lamping.Checks.Q0LocalModelFragments
open AG Graph Lambda Lambda.Labelled Q0LocalModelFixture

def piece : AccessCode → List (Endpoint net)
  | .root => [rootEnd]
  | .leftA => [.inl ⟨Node.R,.inl ()⟩,.inl ⟨Node.C0,.inl ()⟩,.inl ⟨Node.F,.inl ()⟩]
  | .leftB => [.inl ⟨Node.A,.inl ()⟩]
  | .leftL => [.inl ⟨Node.B,.inl ()⟩]
  | .leftV => [.inl ⟨Node.L,.inr true⟩,.inl ⟨Node.C1,.inl ()⟩]
  | .leftJ => [.inl ⟨Node.B,.inr true⟩]
  | .leftJV => [.inl ⟨Node.J,.inr true⟩,.inl ⟨Node.CJ,.inl ()⟩]
  | .leftK => [.inl ⟨Node.A,.inr true⟩]
  | .leftKV => [.inl ⟨Node.K,.inr true⟩,.inl ⟨Node.CK,.inl ()⟩]
  | .rightA => [.inl ⟨Node.R,.inr true⟩,.inl ⟨Node.F,.inl ()⟩]
  | .rightB => [.inl ⟨Node.A,.inl ()⟩]
  | .rightL => [.inl ⟨Node.B,.inl ()⟩]
  | .rightV => [.inl ⟨Node.L,.inr true⟩,.inl ⟨Node.C1,.inl ()⟩]
  | .rightJ => [.inl ⟨Node.B,.inr true⟩]
  | .rightJV => [.inl ⟨Node.J,.inr true⟩,.inl ⟨Node.CJ,.inl ()⟩]
  | .rightK => [.inl ⟨Node.A,.inr true⟩]
  | .rightKV => [.inl ⟨Node.K,.inr true⟩,.inl ⟨Node.CK,.inl ()⟩]

def fromEnd : AccessCode → Endpoint net
  | .root => rootEnd
  | .leftA => .inl ⟨Node.R,.inl ()⟩
  | .leftB => .inl ⟨Node.A,.inl ()⟩
  | .leftL => .inl ⟨Node.B,.inl ()⟩
  | .leftV => .inl ⟨Node.L,.inr true⟩
  | .leftJ => .inl ⟨Node.B,.inr true⟩
  | .leftJV => .inl ⟨Node.J,.inr true⟩
  | .leftK => .inl ⟨Node.A,.inr true⟩
  | .leftKV => .inl ⟨Node.K,.inr true⟩
  | .rightA => .inl ⟨Node.R,.inr true⟩
  | .rightB => .inl ⟨Node.A,.inl ()⟩
  | .rightL => .inl ⟨Node.B,.inl ()⟩
  | .rightV => .inl ⟨Node.L,.inr true⟩
  | .rightJ => .inl ⟨Node.B,.inr true⟩
  | .rightJV => .inl ⟨Node.J,.inr true⟩
  | .rightK => .inl ⟨Node.A,.inr true⟩
  | .rightKV => .inl ⟨Node.K,.inr true⟩

def toEnd : AccessCode → Endpoint net
  | .root => .inl ⟨Node.R,.inr false⟩
  | .leftA => .inl ⟨Node.A,.inr false⟩
  | .leftB => .inl ⟨Node.B,.inr false⟩
  | .leftL => .inl ⟨Node.L,.inl ()⟩
  | .leftV => .inl ⟨Node.L,.inr false⟩
  | .leftJ => .inl ⟨Node.J,.inl ()⟩
  | .leftJV => .inl ⟨Node.J,.inr false⟩
  | .leftK => .inl ⟨Node.K,.inl ()⟩
  | .leftKV => .inl ⟨Node.K,.inr false⟩
  | .rightA => .inl ⟨Node.A,.inr false⟩
  | .rightB => .inl ⟨Node.B,.inr false⟩
  | .rightL => .inl ⟨Node.L,.inl ()⟩
  | .rightV => .inl ⟨Node.L,.inr false⟩
  | .rightJ => .inl ⟨Node.J,.inl ()⟩
  | .rightJV => .inl ⟨Node.J,.inr false⟩
  | .rightK => .inl ⟨Node.K,.inl ()⟩
  | .rightKV => .inl ⟨Node.K,.inr false⟩

def parentCode : AccessCode → AccessCode
  | .root => .root
  | .leftA => .root
  | .leftB => .leftA
  | .leftL => .leftB
  | .leftV => .leftL
  | .leftJ => .leftB
  | .leftJV => .leftJ
  | .leftK => .leftA
  | .leftKV => .leftK
  | .rightA => .root
  | .rightB => .rightA
  | .rightL => .rightB
  | .rightV => .rightL
  | .rightJ => .rightB
  | .rightJV => .rightJ
  | .rightK => .rightA
  | .rightKV => .rightK

def lastStep : AccessCode → Step
  | .root => .fn
  | .leftA => .fn
  | .leftB => .fn
  | .leftL => .fn
  | .leftV => .body
  | .leftJ => .arg
  | .leftJV => .body
  | .leftK => .arg
  | .leftKV => .body
  | .rightA => .arg
  | .rightB => .fn
  | .rightL => .fn
  | .rightV => .body
  | .rightJ => .arg
  | .rightJV => .body
  | .rightK => .arg
  | .rightKV => .body

def before (c : AccessCode) : List (Endpoint net) :=
  if c=.root then [] else edges (parentCode c)

private theorem route_word (c : AccessCode) : accessWord net (edges c)=coordinate c := by
  cases c <;> rfl

private theorem route_split (c : AccessCode) (nonroot : c≠.root) :
    edges c=edges (parentCode c)++piece c := by
  cases c <;> first | exact False.elim (nonroot rfl) | rfl

private theorem coordinate_split (c : AccessCode) (nonroot : c≠.root) :
    coordinate c=coordinate (parentCode c)++[lastStep c] := by
  cases c <;> first | exact False.elim (nonroot rfl) | rfl

private theorem coordinate_nonempty (c : AccessCode) (nonroot : c≠.root) :
    coordinate c≠[] := by
  cases c <;> simp_all [coordinate]

private theorem piece_start (c : AccessCode) : (piece c).head?=some (fromEnd c) := by
  cases c <;> rfl

private theorem piece_finish (c : AccessCode) :
    (piece c).getLast?=some (net.wire (toEnd c)) := by
  cases c <;> rfl

private theorem singleton_append_injective {p q : Path} {s u : Step}
    (same : p++[s]=q++[u]) : p=q ∧ s=u := by
  have reverse := congrArg List.reverse same
  simp only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,
    List.cons_append] at reverse
  have parts := List.cons.inj reverse
  exact ⟨by simpa only [List.reverse_reverse] using congrArg List.reverse parts.2,parts.1⟩

private theorem actual_access (c : AccessCode)
    (fragment : OccurrenceFragment source net () (coordinate c)) :
    fragment.fragment.access.val=edges c := by
  have same : fragment.fragment.access=access c :=
    actual_matching.accessWord_injective (fragment.fragment.word.trans (route_word c).symm)
  exact congrArg Subtype.val same

private theorem actual_cut (c : AccessCode)
    (fragment : OccurrenceFragment source net () (coordinate c)) :
    fragment.fragment.before=before c ∧ fragment.fragment.segments=piece c := by
  have accessEq := actual_access c fragment
  have fromPort : (sourceEdge fragment.environment fragment.context fragment.term).fromPort=fragment.context := by
    cases fragment.term <;> rfl
  by_cases root : c=.root
  · subst c
    rcases fragment.occurrence.last_departure with ⟨_empty,external⟩ |
      ⟨parent,step,term,split,_lookup,_role⟩
    · have actualExternal : (sourceEdge fragment.environment fragment.context fragment.term).fromPort=.external :=
        fromPort.trans external
      have segmentsEq : fragment.fragment.segments=piece .root :=
        (fragment.fragment.external_segments actualExternal).trans accessEq
      have length := congrArg List.length fragment.fragment.literal
      rw [accessEq,segmentsEq] at length
      simp only [edges,piece,List.length_singleton,List.length_append] at length
      have zero : fragment.fragment.before.length=0 := by omega
      exact ⟨List.length_eq_zero_iff.mp zero,segmentsEq⟩
    · have length := congrArg List.length split
      simp only [coordinate,List.length_nil,List.length_append,List.length_singleton] at length
      omega
  · rcases fragment.occurrence.last_departure with ⟨empty,_external⟩ |
      ⟨parent,step,term,split,_lookup,role⟩
    · exact False.elim (coordinate_nonempty c root empty)
    · obtain ⟨sameParent,sameStep⟩ := singleton_append_injective
        (split.symm.trans (coordinate_split c root))
      subst parent; subst step
      have actualRole : SourceDeparture term (lastStep c)
          (sourceEdge fragment.environment fragment.context fragment.term).fromPort := by
        rw [fromPort]
        exact role
      have word : coordinate c=accessWord net (access (parentCode c)).val++[lastStep c] := by
        change coordinate c=accessWord net (edges (parentCode c))++[lastStep c]
        rw [route_word]
        exact coordinate_split c root
      have cut := fragment.fragment.child_prefix actual_matching actualRole (access (parentCode c)) word
      have segmentsEq : fragment.fragment.segments=piece c :=
        List.append_cancel_left ((cut.2.symm.trans accessEq).trans (route_split c root))
      have beforeEq : fragment.fragment.before=before c := by
        simp only [before,if_neg root]
        exact cut.1
      exact ⟨beforeEq,segmentsEq⟩

/-- All17 literal geometry rows, for an arbitrary genuine occurrence fragment.
Variables retain the actual SourceSubterm environment and end at the concrete
L/J/K binding port listed above; no equality of labels chooses the binder. -/
theorem literal_occurrence_fragment (c : AccessCode)
    (fragment : OccurrenceFragment source net () (coordinate c)) :
    fragment.fragment.before=before c ∧ fragment.fragment.segments=piece c ∧
    fragment.fragment.fromEndpoint=fromEnd c ∧ fragment.fragment.toEndpoint=toEnd c := by
  obtain ⟨beforeEq,segmentsEq⟩ := actual_cut c fragment
  refine ⟨beforeEq,segmentsEq,?_,?_⟩
  · have start := fragment.fragment.start
    rw [segmentsEq] at start
    exact Option.some.inj (start.symm.trans (piece_start c))
  · have finish := fragment.fragment.finish
    rw [segmentsEq] at finish
    have wires := Option.some.inj (finish.symm.trans (piece_finish c))
    have same := congrArg net.wire.mate wires
    simpa only [Pairing.involutive] using same

/-- The same supplied whole labelling a/b is cut at the real syntax-parent
seam; no canonical inhabitant is substituted for its original assignment. -/
theorem literal_occurrence_assignment (c : AccessCode)
    (fragment : OccurrenceFragment source net () (coordinate c))
    {a b : Context} (labels : Labelling net (edges c) a b) :
    ∃ middle,(before c=[] ∧middle=a ∨Labelling net (before c) a middle) ∧
      Labelling net (piece c) middle b := by
  obtain ⟨beforeEq,segmentsEq,_fromEq,_toEq⟩ := literal_occurrence_fragment c fragment
  have actualLabels : Labelling net fragment.fragment.access.val a b := by
    rw [actual_access c fragment]
    exact labels
  obtain ⟨middle,first,second⟩ := fragment.fragment.assignments a b actualLabels
  refine ⟨middle,?_,?_⟩
  · simpa only [beforeEq] using first
  · simpa only [segmentsEq] using second

#print axioms literal_occurrence_fragment
#print axioms literal_occurrence_assignment

end Lamping.Checks.Q0LocalModelFragments
