import Lamping.Lamping.ChainSyntaxIncidence
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
/-- A partial endpoint may have no prerequisite chain. External is not a
successful empty chain; proper endpoints retain their actual position. -/
def EndpointChain (current : LTerm) (vertex : SyntaxIncidence.Vertex current)
    (edges : List Path) : Prop :=
  match vertex with
  | none => False
  | some position => PrerequisiteChain current position.val edges

theorem EndpointChain.unique (first : EndpointChain current vertex es)
    (second : EndpointChain current vertex fs) : es=fs := by
  cases vertex with
  | none => exact False.elim first
  | some position => exact PrerequisiteChain.unique first second

def PartialEndpointIso (current : LTerm) (closed : Closed current.erase)
    (left right : SyntaxIncidence.Vertex current) : Prop :=
  (¬∃ es,EndpointChain current left es) ∧(¬∃ fs,EndpointChain current right fs) ∨
  ∃ es fs,EndpointChain current left es ∧EndpointChain current right fs ∧
    ChainIncidenceIsomorphic (chainSyntaxIncidence current closed es)
      (chainSyntaxIncidence current closed fs)

theorem PartialEndpointIso.refl (current : LTerm) (closed : Closed current.erase)
    (vertex : SyntaxIncidence.Vertex current) : PartialEndpointIso current closed vertex vertex := by
  classical
  by_cases available : ∃ es,EndpointChain current vertex es
  · obtain ⟨es,chain⟩ := available
    exact Or.inr ⟨es,es,chain,chain,⟨ChainIncidenceIso.refl _⟩⟩
  · exact Or.inl ⟨available,available⟩

theorem PartialEndpointIso.symm (relation : PartialEndpointIso current closed left right) :
    PartialEndpointIso current closed right left := by
  rcases relation with ⟨noLeft,noRight⟩ |⟨es,fs,leftChain,rightChain,⟨iso⟩⟩
  · exact Or.inl ⟨noRight,noLeft⟩
  · exact Or.inr ⟨fs,es,rightChain,leftChain,⟨iso.symm⟩⟩

theorem PartialEndpointIso.trans (first : PartialEndpointIso current closed left middle)
    (second : PartialEndpointIso current closed middle right) :
    PartialEndpointIso current closed left right := by
  rcases first with ⟨noLeft,noMiddle⟩ |⟨es,ms,leftChain,middleChain,⟨leftIso⟩⟩
  · rcases second with ⟨_,noRight⟩ |⟨ms,rs,middleChain,_,_⟩
    · exact Or.inl ⟨noLeft,noRight⟩
    · exact False.elim (noMiddle ⟨ms,middleChain⟩)
  · rcases second with ⟨noMiddle,_⟩ |⟨other,rs,otherMiddle,rightChain,⟨rightIso⟩⟩
    · exact False.elim (noMiddle ⟨ms,middleChain⟩)
    · have same := middleChain.unique otherMiddle
      subst other
      exact Or.inr ⟨es,rs,leftChain,rightChain,⟨leftIso.trans rightIso⟩⟩

theorem PartialEndpointIso.available_iff (relation : PartialEndpointIso current closed left right) :
    (∃ es,EndpointChain current left es) ↔∃ fs,EndpointChain current right fs := by
  rcases relation with ⟨noLeft,noRight⟩ |⟨es,fs,leftChain,rightChain,_⟩
  · exact ⟨fun h=>False.elim (noLeft h),fun h=>False.elim (noRight h)⟩
  · exact ⟨fun _=>⟨fs,rightChain⟩,fun _=>⟨es,leftChain⟩⟩
end Lamping.AG