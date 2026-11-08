import Lamping.Lamping.FanAppAllReadSlotDispatcher
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
variable (site : PathSite (.fanAction .app i j lt) kept (B:=B) (W:=W) (V:=V))

/-- Complete ordered forward only. It is assembled at true bounded slots
of the supplied chains, not arbitrary nonroot occurrences or flattened labels. -/
theorem PathSite.fan_app_chain_representation_forward
    {current : LTerm} {root : B} {boundary : B→Bool}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (inputs : RootInputs site.net root)
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
  have pieces := site.fan_app_all_read_same_slot_forward sourceMatches targetMatches flow positive inputs principal
    source first second physical lp rp ls rs (target lp) (target rp)
  have lSlot := canonical_chain_slot target first lp ls
  have rSlot := canonical_chain_slot target second rp rs
  rw [List.getElem?_eq_getElem leftBound] at lSlot
  rw [List.getElem?_eq_getElem rightBound] at rSlot
  exact (Option.some.inj lSlot).trans (pieces.trans (Option.some.inj rSlot).symm)

end
end Lamping.AG
#print axioms Lamping.AG.PathSite.fan_app_chain_representation_forward
