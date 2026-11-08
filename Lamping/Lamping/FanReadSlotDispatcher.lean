import Lamping.Lamping.FanProperSlotDispatcher
import Lamping.Lamping.FanVariableReadDispatcher
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {current : LTerm} {g : Net signature N B W} {root : B}

private theorem position_cases (position : Position current.erase) :
    ((∃stamp fn arg,current.subterm position.val=some (.app stamp fn arg)) ∨
      (∃stamp body,current.subterm position.val=some (.lam stamp body))) ∨
      (∃stamp index,current.subterm position.val=some (.var stamp index)) := by
  have valid := position.property
  cases lookup : current.subterm position.val with
  | none => rw [←LTerm.erase_subterm,lookup] at valid;cases valid
  | some term =>
    cases term with
    | app stamp fn arg => exact Or.inl (Or.inl ⟨stamp,fn,arg,rfl⟩)
    | lam stamp body => exact Or.inl (Or.inr ⟨stamp,body,rfl⟩)
    | var stamp index => exact Or.inr ⟨stamp,index,rfl⟩

private theorem proper_variable_ne (matching : Matches g root current.erase)
    (first : OccurrenceFragment current g root p) (second : OccurrenceFragment current g root q)
    (proper : (∃stamp fn arg,current.subterm p=some (.app stamp fn arg)) ∨
      (∃stamp body,current.subterm p=some (.lam stamp body)))
    (lookup : current.subterm q=some (.var stamp index)) :
    first.fragment.segments≠second.fragment.segments := by
  intro pieces
  have kinds := first.fragment.access_kind_eq_of_segments_eq second.fragment pieces
  rcases proper with ⟨a,fn,arg,actual⟩|⟨a,body,actual⟩
  · rw [matching.app_access_typed actual first.fragment.access first.fragment.word,
      matching.variable_access_typed lookup second.fragment.access second.fragment.word] at kinds
    cases kinds
  · rw [matching.lambda_access_typed actual first.fragment.access first.fragment.word,
      matching.variable_access_typed lookup second.fragment.access second.fragment.word] at kinds
    cases kinds
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.fanAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))

/-- Actual successful READ slots, classified from valid CURRENT lookup. -/
theorem PathSite.fan_read_same_slot_forward
    {current : LTerm} {root : B} {boundary : B→Bool} {n : Nat}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (oldT : Transparency site.net root)
    (principal : SiteActionPrincipal site) (selection : OccurrenceFragmentSelection current site.net root)
    (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right)
    (physical : SameChainRepresentation selection first second)
    (leftPosition rightPosition : Position current.erase)
    (leftSlot : left[n]?=some leftPosition.val) (rightSlot : right[n]?=some rightPosition.val)
    (targetFirst : OccurrenceFragment current site.reduce root leftPosition.val)
    (targetSecond : OccurrenceFragment current site.reduce root rightPosition.val) :
    targetFirst.fragment.segments=targetSecond.fragment.segments := by
  have pieces := same_chain_representation_slot selection first second physical leftPosition rightPosition leftSlot rightSlot
  rcases position_cases leftPosition with leftProper|⟨la,li,leftLookup⟩
  · rcases position_cases rightPosition with rightProper|⟨ra,ri,rightLookup⟩
    · exact site.fan_proper_same_slot_forward sourceMatches targetMatches flow positive principal selection
        first second physical leftPosition rightPosition leftSlot rightSlot leftProper rightProper targetFirst targetSecond
    · exact False.elim (proper_variable_ne sourceMatches (selection leftPosition) (selection rightPosition) leftProper rightLookup pieces)
  · rcases position_cases rightPosition with rightProper|⟨ra,ri,rightLookup⟩
    · exact False.elim (proper_variable_ne sourceMatches (selection rightPosition) (selection leftPosition) rightProper leftLookup pieces.symm)
    · exact site.fan_variable_read_same_slot_forward sourceMatches targetMatches flow positive oldT principal selection
        first second physical leftPosition rightPosition leftSlot rightSlot leftLookup rightLookup targetFirst targetSecond

/-- Actual successful READ slots, classified from valid CURRENT lookup. -/
theorem PathSite.fan_read_same_slot_reflect
    {current : LTerm} {root : B} {boundary : B→Bool} {n : Nat}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (principal : SiteActionPrincipal site) (selection : OccurrenceFragmentSelection current site.reduce root)
    (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right)
    (physical : SameChainRepresentation selection first second)
    (leftPosition rightPosition : Position current.erase)
    (leftSlot : left[n]?=some leftPosition.val) (rightSlot : right[n]?=some rightPosition.val)
    (sourceFirst : OccurrenceFragment current site.net root leftPosition.val)
    (sourceSecond : OccurrenceFragment current site.net root rightPosition.val) :
    sourceFirst.fragment.segments=sourceSecond.fragment.segments := by
  have pieces := same_chain_representation_slot selection first second physical leftPosition rightPosition leftSlot rightSlot
  rcases position_cases leftPosition with leftProper|⟨la,li,leftLookup⟩
  · rcases position_cases rightPosition with rightProper|⟨ra,ri,rightLookup⟩
    · exact site.fan_proper_same_slot_reflect sourceMatches targetMatches flow positive principal selection
        first second physical leftPosition rightPosition leftSlot rightSlot leftProper rightProper sourceFirst sourceSecond
    · exact False.elim (proper_variable_ne targetMatches (selection leftPosition) (selection rightPosition) leftProper rightLookup pieces)
  · rcases position_cases rightPosition with rightProper|⟨ra,ri,rightLookup⟩
    · exact False.elim (proper_variable_ne targetMatches (selection rightPosition) (selection leftPosition) rightProper leftLookup pieces.symm)
    · exact site.fan_variable_read_same_slot_reflect sourceMatches targetMatches flow positive principal selection
        first second physical leftPosition rightPosition leftSlot rightSlot leftLookup rightLookup sourceFirst sourceSecond
end
end Lamping.AG
#print axioms Lamping.AG.PathSite.fan_read_same_slot_forward
#print axioms Lamping.AG.PathSite.fan_read_same_slot_reflect
