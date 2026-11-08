import Lamping.Lamping.EndpointPrerequisites
namespace Lamping.AG
open Graph Lambda Lambda.Labelled

/-- Only two actual successful chains can witness this relation. No clause
identifies endpoints merely because both have no chain. -/
def SuccessfulEndpointIso (current : LTerm) (closed : Closed current.erase)
    (left right : SyntaxIncidence.Vertex current) : Prop :=
  ∃ es fs,EndpointChain current left es ∧EndpointChain current right fs ∧
    ChainIncidenceIsomorphic (chainSyntaxIncidence current closed es)
      (chainSyntaxIncidence current closed fs)

namespace SuccessfulEndpointIso

theorem left_available (relation : SuccessfulEndpointIso current closed left right) :
    ∃ es,EndpointChain current left es := by
  obtain ⟨es,fs,first,second,iso⟩ := relation
  exact ⟨es,first⟩

theorem right_available (relation : SuccessfulEndpointIso current closed left right) :
    ∃ fs,EndpointChain current right fs := by
  obtain ⟨es,fs,first,second,iso⟩ := relation
  exact ⟨fs,second⟩

theorem refl_of_chain (chain : EndpointChain current vertex es) :
    SuccessfulEndpointIso current closed vertex vertex :=
  ⟨es,es,chain,chain,⟨ChainIncidenceIso.refl _⟩⟩

theorem refl_of_available (available : ∃ es,EndpointChain current vertex es) :
    SuccessfulEndpointIso current closed vertex vertex := by
  obtain ⟨es,chain⟩ := available
  exact refl_of_chain chain

theorem symm (relation : SuccessfulEndpointIso current closed left right) :
    SuccessfulEndpointIso current closed right left := by
  obtain ⟨es,fs,first,second,⟨iso⟩⟩ := relation
  exact ⟨fs,es,second,first,⟨iso.symm⟩⟩

theorem trans (first : SuccessfulEndpointIso current closed left middle)
    (second : SuccessfulEndpointIso current closed middle right) :
    SuccessfulEndpointIso current closed left right := by
  obtain ⟨es,ms,leftChain,middleChain,⟨leftIso⟩⟩ := first
  obtain ⟨other,rs,otherMiddle,rightChain,⟨rightIso⟩⟩ := second
  have same := middleChain.unique otherMiddle
  subst other
  exact ⟨es,rs,leftChain,rightChain,⟨leftIso.trans rightIso⟩⟩

theorem to_partial (relation : SuccessfulEndpointIso current closed left right) :
    PartialEndpointIso current closed left right := Or.inr relation

/-- A real left chain already excludes the old both-undefined alternative;
right availability is then a consequence, not an extra assumption. -/
theorem iff_partial_of_left_available (available : ∃ es,EndpointChain current left es) :
    SuccessfulEndpointIso current closed left right ↔PartialEndpointIso current closed left right := by
  constructor
  · exact to_partial
  · intro relation
    rcases relation with ⟨noLeft,noRight⟩ |success
    · exact False.elim (noLeft available)
    · exact success
end SuccessfulEndpointIso
end Lamping.AG
