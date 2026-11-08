import Lamping.Lamping.BetaOldChainImages
namespace Lamping.AG
open Graph Lambda Lambda.Labelled

/-- Pointwise comparison on the actual finite slots is enough; no list
induction or alternate canonical image definition is introduced. -/
private theorem map_compare_slots {A B X Y : Type}
    (f : A→X) (g : B→X) (h : A→Y) (k : B→Y)
    (xs : List A) (ys : List B)
    (compare : ∀a∈xs,∀b∈ys,f a=g b ↔h a=k b) :
    xs.map f=ys.map g ↔xs.map h=ys.map k := by
  constructor
  · intro same
    have lengths := congrArg List.length same
    simp only [List.length_map] at lengths
    apply List.ext_getElem (by simpa only [List.length_map] using lengths)
    intro i firstBound secondBound
    have ix : i<xs.length := by simpa only [List.length_map] using firstBound
    have iy : i<ys.length := by simpa only [List.length_map] using secondBound
    have sameAt := congrArg (fun zs=>zs[i]?) same
    change (xs.map f)[i]?=(ys.map g)[i]? at sameAt
    rw [List.getElem?_eq_getElem (by simpa only [List.length_map] using ix),
      List.getElem?_eq_getElem (by simpa only [List.length_map] using iy)] at sameAt
    simp only [List.getElem_map] at sameAt ⊢
    exact (compare xs[i] (List.getElem_mem ix) ys[i] (List.getElem_mem iy)).mp (Option.some.inj sameAt)
  · intro same
    have lengths := congrArg List.length same
    simp only [List.length_map] at lengths
    apply List.ext_getElem (by simpa only [List.length_map] using lengths)
    intro i firstBound secondBound
    have ix : i<xs.length := by simpa only [List.length_map] using firstBound
    have iy : i<ys.length := by simpa only [List.length_map] using secondBound
    have sameAt := congrArg (fun zs=>zs[i]?) same
    change (xs.map h)[i]?=(ys.map k)[i]? at sameAt
    rw [List.getElem?_eq_getElem (by simpa only [List.length_map] using ix),
      List.getElem?_eq_getElem (by simpa only [List.length_map] using iy)] at sameAt
    simp only [List.getElem_map] at sameAt ⊢
    exact (compare xs[i] (List.getElem_mem ix) ys[i] (List.getElem_mem iy)).mpr (Option.some.inj sameAt)

section
variable {N B W M C V : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    [FiniteNames M] [FiniteNames C] [FiniteNames V]
variable {current : LTerm} {sourceNet : Net signature N B W} {targetNet : Net signature M C V}
    {sourceRoot : B} {targetRoot : C}

theorem successful_chain_representation_transport
    (source : OccurrenceFragmentSelection current sourceNet sourceRoot)
    (target : OccurrenceFragmentSelection current targetNet targetRoot)
    (compare : ∀a b : Position current.erase,a.val≠[]→b.val≠[]→
      ((target a).fragment.segments=(target b).fragment.segments ↔
       (source a).fragment.segments=(source b).fragment.segments))
    (first : PrerequisiteChain current p left) (second : PrerequisiteChain current q right) :
    SameChainRepresentation target first second ↔SameChainRepresentation source first second := by
  unfold SameChainRepresentation canonicalChainImage
  apply map_compare_slots
  intro a _ b _
  exact compare _ _ (first.reading_ne_nil a.property) (second.reading_ne_nil b.property)

theorem successful_chain_invariant_transport
    (closed : Closed current.erase)
    (source : OccurrenceFragmentSelection current sourceNet sourceRoot)
    (target : OccurrenceFragmentSelection current targetNet targetRoot)
    (compare : ∀a b : Position current.erase,a.val≠[]→b.val≠[]→
      ((target a).fragment.segments=(target b).fragment.segments ↔
       (source a).fragment.segments=(source b).fragment.segments)) :
    ChainRepresentationInvariant closed target ↔ChainRepresentationInvariant closed source := by
  constructor
  · intro invariant p q left right first second
    exact (successful_chain_representation_transport source target compare first second).symm.trans
      (invariant first second)
  · intro invariant p q left right first second
    exact (successful_chain_representation_transport source target compare first second).trans
      (invariant first second)
end
end Lamping.AG
