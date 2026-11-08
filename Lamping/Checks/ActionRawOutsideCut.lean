import Lamping.Lamping.ActionRawOutsideCut
namespace Lamping.Checks.RawOutsideCut
open AG Graph
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed

/-- A structural ordinal regression, conditional on a supplied real whole
labelling. It does not assert reachability or existence of such a loop.
The same endpoint at ordinal zero and one gives different literal suffixes. -/
theorem repeated_outside_ordinals (principal : SiteActionPrincipal site) (pivot : Endpoint cut)
    {a b : Context} (labels : PlugLabelling cut s.right.net [.inl pivot,.inl pivot,.inl pivot] a b) :
    ∃ firstSeam middleSeam,
      ActionCanonicalBlocks site principal [.inl pivot,.inl pivot,.inl pivot]
        [site.outsideEnd pivot,site.outsideEnd pivot,site.outsideEnd pivot] ∧
      ActionCanonicalBlocks site principal [.inl pivot,.inl pivot]
        [site.outsideEnd pivot,site.outsideEnd pivot] ∧
      PlugLabelling cut s.right.net [.inl pivot,.inl pivot,.inl pivot] firstSeam b ∧
      PlugLabelling cut s.right.net [.inl pivot,.inl pivot] middleSeam b := by
  have one : ActionCanonicalBlocks site principal [.inl pivot] [site.outsideEnd pivot] := .single pivot
  have two := ActionCanonicalBlocks.outside (e:=pivot) one
  have three := ActionCanonicalBlocks.outside (e:=pivot) two
  obtain ⟨firstTail,firstSeam,firstSplit,firstRelation,_firstPrefix,firstLabels⟩ :=
    three.cut_at_raw_parent site one labels (newPiece:=[.inl pivot,.inl pivot]) rfl pivot rfl
  change site.outsideEnd pivot::site.outsideEnd pivot::site.outsideEnd pivot::[]=
    site.outsideEnd pivot::firstTail at firstSplit
  have firstEq := (List.cons.inj firstSplit).2.symm
  subst firstTail
  obtain ⟨middleTail,middleSeam,middleSplit,middleRelation,_middlePrefix,middleLabels⟩ :=
    three.cut_at_raw_parent site two labels (newPiece:=[.inl pivot]) rfl pivot rfl
  change site.outsideEnd pivot::site.outsideEnd pivot::site.outsideEnd pivot::[]=
    site.outsideEnd pivot::site.outsideEnd pivot::middleTail at middleSplit
  have middleEq := (List.cons.inj (List.cons.inj middleSplit).2).2.symm
  subst middleTail
  exact ⟨firstSeam,middleSeam,firstRelation,middleRelation,firstLabels,middleLabels⟩

#print axioms ActionCanonicalBlocks.split_at_raw_outside
#print axioms ActionCanonicalBlocks.cut_at_raw_parent
#print axioms repeated_outside_ordinals
end
end Lamping.Checks.RawOutsideCut
