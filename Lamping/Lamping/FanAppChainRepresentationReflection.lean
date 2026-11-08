import Lamping.Lamping.FanAppAllReadSlotReflection
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

/-- Complete ordered reflection. It is assembled at true bounded slots
of the supplied chains, not arbitrary nonroot occurrences or flattened labels. -/
theorem PathSite.fan_app_chain_representation_reflect
    {current : LTerm} {root : B} {boundary : B→Bool}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (inputs : RootInputs site.net root)
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
  have pieces := site.fan_app_all_read_same_slot_reflect sourceMatches targetMatches flow positive inputs principal
    target first second physical lp rp ls rs (source lp) (source rp)
  have lSlot := canonical_chain_slot source first lp ls
  have rSlot := canonical_chain_slot source second rp rs
  rw [List.getElem?_eq_getElem leftBound] at lSlot
  rw [List.getElem?_eq_getElem rightBound] at rSlot
  exact (Option.some.inj lSlot).trans (pieces.trans (Option.some.inj rSlot).symm)

/-- The actual SOURCE chain invariant is a legitimate explicit IH. This
consequence proves neither its truth nor any auxiliary/Joint clause. -/
theorem PathSite.fan_app_chain_invariant_preserve
    {current : LTerm} {root : B} {boundary : B→Bool}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (inputs : RootInputs site.net root) (principal : SiteActionPrincipal site)
    (closed : Closed current.erase)
    (source : OccurrenceFragmentSelection current site.net root)
    (target : OccurrenceFragmentSelection current site.reduce root)
    (sourceInvariant : ChainRepresentationInvariant closed source) :
    ChainRepresentationInvariant closed target := by
  intro p q left right first second
  constructor
  · intro targetSame
    exact (sourceInvariant first second).mp (site.fan_app_chain_representation_reflect
      sourceMatches targetMatches flow positive inputs principal source target first second targetSame)
  · intro iso
    exact site.fan_app_chain_representation_forward sourceMatches targetMatches flow positive inputs principal
      source target first second ((sourceInvariant first second).mpr iso)
end
end Lamping.AG
#print axioms Lamping.AG.PathSite.fan_app_chain_representation_reflect
#print axioms Lamping.AG.PathSite.fan_app_chain_invariant_preserve
