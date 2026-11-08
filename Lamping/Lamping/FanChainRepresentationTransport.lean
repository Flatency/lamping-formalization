import Lamping.Lamping.FanReadSlotDispatcher
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {current : LTerm}

/-- Construct only an actually read edge's valid CURRENT position. -/
private def actualReadPosition (chain : PrerequisiteChain current p edges)
    (edge : Path) (member : edge∈edges) : Position current.erase :=
  ⟨edge,by
    rcases chain.eligible member with ⟨parent,a,fn,arg,equal,lookup⟩|⟨a,body,lookup⟩
    · have actual : current.subterm edge=some fn := by
        rw [equal,LTerm.subterm_append,lookup];cases fn <;> rfl
      rw [←LTerm.erase_subterm,actual];rfl
    · rw [←LTerm.erase_subterm,lookup];rfl⟩
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.fanAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))

/-- Whole ordered images are transported using their OWN equality at each
actual ordinal. No arbitrary-occurrence comparison premise is used. -/
theorem PathSite.fan_lambda_chain_representation_forward
    {current : LTerm} {root : B} {boundary : B→Bool}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (oldT : Transparency site.net root)
    (principal : SiteActionPrincipal site)
    (source : OccurrenceFragmentSelection current site.net root)
    (target : OccurrenceFragmentSelection current site.reduce root)
    (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right)
    (physical : SameChainRepresentation source first second) :
    SameChainRepresentation target first second := by
  have lengths := congrArg List.length physical
  change (canonicalChainImage source first).length=(canonicalChainImage source second).length at lengths
  rw [canonicalChainImage_length,canonicalChainImage_length] at lengths
  apply List.ext_getElem (by simpa only [canonicalChainImage_length] using lengths)
  intro n leftBound rightBound
  have lb : n<left.length := by simpa only [canonicalChainImage_length] using leftBound
  have rb : n<right.length := by simpa only [canonicalChainImage_length] using rightBound
  let lp := actualReadPosition first left[n] (List.getElem_mem lb)
  let rp := actualReadPosition second right[n] (List.getElem_mem rb)
  have ls : left[n]?=some lp.val := List.getElem?_eq_getElem lb
  have rs : right[n]?=some rp.val := List.getElem?_eq_getElem rb
  have pieces := site.fan_read_same_slot_forward sourceMatches targetMatches flow positive oldT principal
    source first second physical lp rp ls rs (target lp) (target rp)
  have lSlot := canonical_chain_slot target first lp ls
  have rSlot := canonical_chain_slot target second rp rs
  rw [List.getElem?_eq_getElem leftBound] at lSlot
  rw [List.getElem?_eq_getElem rightBound] at rSlot
  exact (Option.some.inj lSlot).trans (pieces.trans (Option.some.inj rSlot).symm)

/-- Whole ordered images are transported using their OWN equality at each
actual ordinal. No arbitrary-occurrence comparison premise is used. -/
theorem PathSite.fan_lambda_chain_representation_reflect
    {current : LTerm} {root : B} {boundary : B→Bool}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (principal : SiteActionPrincipal site)
    (source : OccurrenceFragmentSelection current site.net root)
    (target : OccurrenceFragmentSelection current site.reduce root)
    (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right)
    (physical : SameChainRepresentation target first second) :
    SameChainRepresentation source first second := by
  have lengths := congrArg List.length physical
  change (canonicalChainImage target first).length=(canonicalChainImage target second).length at lengths
  rw [canonicalChainImage_length,canonicalChainImage_length] at lengths
  apply List.ext_getElem (by simpa only [canonicalChainImage_length] using lengths)
  intro n leftBound rightBound
  have lb : n<left.length := by simpa only [canonicalChainImage_length] using leftBound
  have rb : n<right.length := by simpa only [canonicalChainImage_length] using rightBound
  let lp := actualReadPosition first left[n] (List.getElem_mem lb)
  let rp := actualReadPosition second right[n] (List.getElem_mem rb)
  have ls : left[n]?=some lp.val := List.getElem?_eq_getElem lb
  have rs : right[n]?=some rp.val := List.getElem?_eq_getElem rb
  have pieces := site.fan_read_same_slot_reflect sourceMatches targetMatches flow positive principal
    target first second physical lp rp ls rs (source lp) (source rp)
  have lSlot := canonical_chain_slot source first lp ls
  have rSlot := canonical_chain_slot source second rp rs
  rw [List.getElem?_eq_getElem leftBound] at lSlot
  rw [List.getElem?_eq_getElem rightBound] at rSlot
  exact (Option.some.inj lSlot).trans (pieces.trans (Option.some.inj rSlot).symm)

/-- SAME current syntax, ordered canonical blocks, and actual successful chains. -/
theorem PathSite.fan_lambda_chain_representation
    {current : LTerm} {root : B} {boundary : B→Bool}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (oldT : Transparency site.net root) (principal : SiteActionPrincipal site)
    (source : OccurrenceFragmentSelection current site.net root)
    (target : OccurrenceFragmentSelection current site.reduce root)
    (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right) :
    SameChainRepresentation target first second ↔SameChainRepresentation source first second :=
  ⟨site.fan_lambda_chain_representation_reflect sourceMatches targetMatches flow positive principal source target first second,
    site.fan_lambda_chain_representation_forward sourceMatches targetMatches flow positive oldT principal source target first second⟩

/-- Only the chain clause is transported. No Aux or Joint truth is asserted. -/
theorem PathSite.fan_lambda_chain_invariant
    {current : LTerm} {root : B} {boundary : B→Bool}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (oldT : Transparency site.net root) (principal : SiteActionPrincipal site)
    (closed : Closed current.erase)
    (source : OccurrenceFragmentSelection current site.net root)
    (target : OccurrenceFragmentSelection current site.reduce root) :
    ChainRepresentationInvariant closed target ↔ChainRepresentationInvariant closed source := by
  constructor
  · intro invariant p q left right first second
    exact (site.fan_lambda_chain_representation sourceMatches targetMatches flow positive oldT principal source target first second).symm.trans
      (invariant first second)
  · intro invariant p q left right first second
    exact (site.fan_lambda_chain_representation sourceMatches targetMatches flow positive oldT principal source target first second).trans
      (invariant first second)
end
end Lamping.AG
#print axioms Lamping.AG.PathSite.fan_lambda_chain_representation_forward
#print axioms Lamping.AG.PathSite.fan_lambda_chain_representation_reflect
#print axioms Lamping.AG.PathSite.fan_lambda_chain_representation
#print axioms Lamping.AG.PathSite.fan_lambda_chain_invariant
