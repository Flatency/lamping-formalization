import Lamping.Lambda.RegionProjectionHead
import Lamping.Lambda.NoTagTransport
namespace Lamping.Lambda

/-- In a disjoint ordinary projection the actual horizontal programs have
 identical paths, including their order and multiplicity. -/
theorem StepProjection.disjoint_paths (R : BetaAt t p u)
    (row : StepProjection (singleContraction R) σ τ last)
    (ha : Atomic σ) (hb : Atomic τ) (apart : DisjointPositions p site)
    (inside : Internal site σ) : σ.derivation.paths=τ.derivation.paths := by
  induction ha generalizing u with
  | nil =>
    cases hb with
    | nil => rfl
    | cons B ht => have len := row.length; simp only [ParallelHistory.length] at len; omega
  | @cons t a v upperEnd upper A hu ih =>
    cases hb with
    | nil => have len := row.length; simp only [ParallelHistory.length] at len; omega
    | @cons u b w lowerEnd lower B hl =>
      have aInside : ∃q,a=site++q := inside a
        (by change a∈a::upper.derivation.paths; exact List.mem_cons_self)
      obtain ⟨q,hq⟩ := aInside
      have headApart : DisjointPositions p a := by
        exact ⟨apart.descendant_outside ⟨q,hq⟩,
          (show ExtractionRegion p site from .inl apart).not_above ⟨q,hq⟩⟩
      have old := row.head_singleton_residual A B
      have fixed : b=a := ((R.disjoint_residual_iff ⟨a,A.redex⟩ headApart ⟨b,B.redex⟩).mp old).symm
      obtain ⟨R1,_,tailRow⟩ := row.region_head R A B (.inl apart) ⟨q,hq⟩
      have upperInside : Internal site upper := by
        intro name hp
        exact inside name (by change name∈a::upper.derivation.paths; exact List.mem_cons_of_mem _ hp)
      have tailPaths := ih R1 tailRow hl upperInside
      change a::upper.derivation.paths=b::lower.derivation.paths
      rw [fixed,tailPaths]

end Lamping.Lambda
