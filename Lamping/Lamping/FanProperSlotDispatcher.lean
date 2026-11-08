import Lamping.Lamping.FanAppReadDispatcher
import Lamping.Lamping.FragmentChildStepSeparation
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {current : LTerm}
/-- Actual successful readings exclude root arrival and expose the true
incoming syntax case. No desired BODY/APP profile is supplied. -/
theorem OccurrenceFragment.read_incoming_cases (occurrence : OccurrenceFragment current g root position)
    (chain : PrerequisiteChain current start edges) (member : position∈edges) :
    (∃stamp,occurrence.context=.lamBody stamp) ∨
      (∃stamp,occurrence.context=.appFn stamp ∨occurrence.context=.appArg stamp) := by
  rcases occurrence with ⟨sub,env,ctx,actual,fragment⟩
  rcases actual.last_departure with ⟨empty,_external⟩|⟨parent,step,term,_split,_lookup,role⟩
  · exact False.elim (chain.reading_ne_nil member empty)
  · cases role with
    | fn => exact Or.inr ⟨_,Or.inl rfl⟩
    | arg => exact Or.inr ⟨_,Or.inr rfl⟩
    | body => exact Or.inl ⟨_,rfl⟩

private theorem app_lambda_ne (matching : Matches g root current.erase)
    (first : OccurrenceFragment current g root p) (second : OccurrenceFragment current g root q)
    (leftLookup : current.subterm p=some (.app stamp fn arg))
    (rightLookup : current.subterm q=some (.lam origin body)) :
    first.fragment.segments≠second.fragment.segments := by
  intro pieces
  have kinds := first.fragment.access_kind_eq_of_segments_eq second.fragment pieces
  rw [matching.app_access_typed leftLookup first.fragment.access first.fragment.word,
    matching.lambda_access_typed rightLookup second.fragment.access second.fragment.word] at kinds
  cases kinds

private theorem body_app_ne (matching : Matches g root current.erase)
    (first : OccurrenceFragment current g root p) (second : OccurrenceFragment current g root q)
    (leftIncoming : ∃stamp,first.context=.lamBody stamp)
    (rightIncoming : ∃stamp,second.context=.appFn stamp ∨second.context=.appArg stamp) :
    first.fragment.segments≠second.fragment.segments := by
  obtain ⟨lp,lo,lb,lLookup,lSplit,lRole⟩ := first.lambda_body_parent leftIncoming
  obtain ⟨rp,rstep,ra,rfn,rarg,rLookup,rSplit,rsteps,rRole⟩ := second.app_incoming_parent rightIncoming
  let leftParentPosition : Position current.erase := ⟨lp,by rw [←LTerm.erase_subterm,lLookup];rfl⟩
  let rightParentPosition : Position current.erase := ⟨rp,by rw [←LTerm.erase_subterm,rLookup];rfl⟩
  obtain ⟨leftParent,leftWord,_⟩ := Matches.observation g matching leftParentPosition
  obtain ⟨rightParent,rightWord,_⟩ := Matches.observation g matching rightParentPosition
  exact first.fragment.ne_of_child_steps matching second.fragment lRole rRole leftParent rightParent
    (by rw [leftWord];exact lSplit) (by rw [rightWord];exact rSplit)
    (by rcases rsteps with rfl|rfl <;> decide)
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.fanAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
theorem PathSite.fan_proper_same_slot_forward
    {current : LTerm} {root : B} {boundary : B→Bool} {n : Nat}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (principal : SiteActionPrincipal site) (selection : OccurrenceFragmentSelection current site.net root)
    (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right)
    (physical : SameChainRepresentation selection first second)
    (leftPosition rightPosition : Position current.erase)
    (leftSlot : left[n]?=some leftPosition.val) (rightSlot : right[n]?=some rightPosition.val)
    (leftProper : (∃stamp fn arg,current.subterm leftPosition.val=some (.app stamp fn arg)) ∨
      (∃stamp body,current.subterm leftPosition.val=some (.lam stamp body)))
    (rightProper : (∃stamp fn arg,current.subterm rightPosition.val=some (.app stamp fn arg)) ∨
      (∃stamp body,current.subterm rightPosition.val=some (.lam stamp body)))
    (targetFirst : OccurrenceFragment current site.reduce root leftPosition.val)
    (targetSecond : OccurrenceFragment current site.reduce root rightPosition.val)
    : targetFirst.fragment.segments=targetSecond.fragment.segments := by
  have pieces := same_chain_representation_slot selection first second physical leftPosition rightPosition leftSlot rightSlot
  let sourceFirst := selection leftPosition
  let sourceSecond := selection rightPosition
  rcases leftProper with ⟨la,lfn,larg,leftLookup⟩|⟨la,lb,leftLookup⟩
  · rcases rightProper with ⟨ra,rfn,rarg,rightLookup⟩|⟨ra,rb,rightLookup⟩
    · exact site.fan_app_read_same_slot_forward sourceMatches targetMatches flow positive principal selection first second physical leftPosition rightPosition leftSlot rightSlot leftLookup rightLookup targetFirst targetSecond
    · exact False.elim (app_lambda_ne sourceMatches sourceFirst sourceSecond leftLookup rightLookup pieces)
  · rcases rightProper with ⟨ra,rfn,rarg,rightLookup⟩|⟨ra,rb,rightLookup⟩
    · exact False.elim (app_lambda_ne sourceMatches sourceSecond sourceFirst rightLookup leftLookup pieces.symm)
    · rcases sourceFirst.read_incoming_cases first (List.mem_of_getElem? leftSlot) with leftBody|leftApp
      · rcases sourceSecond.read_incoming_cases second (List.mem_of_getElem? rightSlot) with rightBody|rightApp
        · exact site.fan_body_lambda_same_slot_forward sourceMatches targetMatches flow positive principal selection first second physical leftPosition rightPosition leftSlot rightSlot leftLookup rightLookup leftBody rightBody targetFirst targetSecond
        · exact False.elim (body_app_ne sourceMatches sourceFirst sourceSecond leftBody rightApp pieces)
      · rcases sourceSecond.read_incoming_cases second (List.mem_of_getElem? rightSlot) with rightBody|rightApp
        · exact False.elim (body_app_ne sourceMatches sourceSecond sourceFirst rightBody leftApp pieces.symm)
        · exact site.fan_app_lambda_same_slot_forward sourceMatches targetMatches flow positive principal selection first second physical leftPosition rightPosition leftSlot rightSlot leftLookup rightLookup leftApp rightApp targetFirst targetSecond

theorem PathSite.fan_proper_same_slot_reflect
    {current : LTerm} {root : B} {boundary : B→Bool} {n : Nat}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (principal : SiteActionPrincipal site) (selection : OccurrenceFragmentSelection current site.reduce root)
    (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right)
    (physical : SameChainRepresentation selection first second)
    (leftPosition rightPosition : Position current.erase)
    (leftSlot : left[n]?=some leftPosition.val) (rightSlot : right[n]?=some rightPosition.val)
    (leftProper : (∃stamp fn arg,current.subterm leftPosition.val=some (.app stamp fn arg)) ∨
      (∃stamp body,current.subterm leftPosition.val=some (.lam stamp body)))
    (rightProper : (∃stamp fn arg,current.subterm rightPosition.val=some (.app stamp fn arg)) ∨
      (∃stamp body,current.subterm rightPosition.val=some (.lam stamp body)))
    (sourceFirst : OccurrenceFragment current site.net root leftPosition.val)
    (sourceSecond : OccurrenceFragment current site.net root rightPosition.val)
    : sourceFirst.fragment.segments=sourceSecond.fragment.segments := by
  have pieces := same_chain_representation_slot selection first second physical leftPosition rightPosition leftSlot rightSlot
  let targetFirst := selection leftPosition
  let targetSecond := selection rightPosition
  rcases leftProper with ⟨la,lfn,larg,leftLookup⟩|⟨la,lb,leftLookup⟩
  · rcases rightProper with ⟨ra,rfn,rarg,rightLookup⟩|⟨ra,rb,rightLookup⟩
    · exact site.fan_app_read_same_slot_reflect sourceMatches targetMatches flow positive principal selection first second physical leftPosition rightPosition leftSlot rightSlot leftLookup rightLookup sourceFirst sourceSecond
    · exact False.elim (app_lambda_ne targetMatches targetFirst targetSecond leftLookup rightLookup pieces)
  · rcases rightProper with ⟨ra,rfn,rarg,rightLookup⟩|⟨ra,rb,rightLookup⟩
    · exact False.elim (app_lambda_ne targetMatches targetSecond targetFirst rightLookup leftLookup pieces.symm)
    · rcases targetFirst.read_incoming_cases first (List.mem_of_getElem? leftSlot) with leftBody|leftApp
      · rcases targetSecond.read_incoming_cases second (List.mem_of_getElem? rightSlot) with rightBody|rightApp
        · exact site.fan_body_lambda_same_slot_reflect sourceMatches targetMatches flow positive principal selection first second physical leftPosition rightPosition leftSlot rightSlot leftLookup rightLookup leftBody rightBody sourceFirst sourceSecond
        · exact False.elim (body_app_ne targetMatches targetFirst targetSecond leftBody rightApp pieces)
      · rcases targetSecond.read_incoming_cases second (List.mem_of_getElem? rightSlot) with rightBody|rightApp
        · exact False.elim (body_app_ne targetMatches targetSecond targetFirst rightBody leftApp pieces.symm)
        · exact site.fan_app_lambda_same_slot_reflect sourceMatches targetMatches flow positive principal selection first second physical leftPosition rightPosition leftSlot rightSlot leftLookup rightLookup leftApp rightApp sourceFirst sourceSecond

end
end Lamping.AG
#print axioms Lamping.AG.OccurrenceFragment.read_incoming_cases
#print axioms Lamping.AG.PathSite.fan_proper_same_slot_forward
#print axioms Lamping.AG.PathSite.fan_proper_same_slot_reflect
