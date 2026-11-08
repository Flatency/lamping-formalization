import Lamping.Lambda.CopyProtectedExtraction
namespace Lamping.Lambda

/-- The first function/argument divergence selects a whole right sibling.
Every position right of the cut is either inside that sibling or disjoint. -/
theorem LeftOf.right_sibling (before : LeftOf cut p) (apart : DisjointPositions cut p) :
    ∃ site q, p=site++q ∧ DisjointPositions cut site ∧
      ∀ r,LeftOf cut r → (∃s,r=site++s) ∨ DisjointPositions r site := by
  induction before with
  | outer s p => exact False.elim (DisjointPositions.nil_left apart)
  | @child cut p e before ih =>
    obtain ⟨site,q,eq,separate,geometry⟩ := ih apart.child
    refine ⟨e::site,q,congrArg (e::·) eq,separate.cons e,?_⟩
    intro r later
    cases later with
    | child _ later =>
      rcases geometry _ later with ⟨s,eq⟩ | separate
      · exact .inl ⟨s,congrArg (e::·) eq⟩
      · exact .inr (separate.cons e)
    | branch p r => exact .inr (DisjointPositions.head_ne (by intro eq; cases eq))
  | branch cut p =>
    refine ⟨[.arg],p,rfl,DisjointPositions.head_ne (by intro eq; cases eq),?_⟩
    intro r later
    cases later with
    | child _ later => exact .inr (DisjointPositions.head_ne (by intro eq; cases eq))
    | branch cut r => exact .inl ⟨r,rfl⟩

/-- Filter a real ordinary pointed history to a subtree whenever every
actual contraction is internal or disjoint. Outside steps are removed by
inverse residual rows, while internal steps are retained literally. -/
theorem Atomic.extract_local_program {ρ : ParallelHistory t u} (ordinary : Atomic ρ)
    (last : BetaAt u p v) (atSite : p=site++q)
    (geometry : ∀ r∈ρ.derivation.paths,(∃s,r=site++s) ∨ DisjointPositions r site) :
    ∃ w, ∃ source : ParallelHistory t w, ∃ sourceAtomic : Atomic source,
      0<source.length ∧ Internal site source ∧
      Extraction (.of (ρ.append (.single (singleContraction last))) (ordinary.append (.single last)))
        (.of source sourceAtomic) := by
  induction ordinary with
  | nil t =>
    refine ⟨v,.single (singleContraction last), .single last,(by simp [ParallelHistory.single,ParallelHistory.length]),?_,.refl _⟩
    intro r hr
    have eq : r=p := by simpa [ParallelHistory.single_derivation,ParallelStep.derivation,singleContraction] using hr
    exact ⟨q,eq.trans atSite⟩
  | @cons t r mid u tail R atomic ih =>
    have tailGeometry : ∀ s∈tail.derivation.paths,(∃a,s=site++a) ∨ DisjointPositions s site := by
      intro s hs; exact geometry s (by simp [ParallelHistory.derivation,Derivation.append,hs])
    obtain ⟨w,middle,middleAtomic,positive,inside,removed⟩ := ih last tailGeometry
    have headGeometry := geometry r (by
      simp [ParallelHistory.derivation,Derivation.append,ParallelStep.derivation,singleContraction])
    have first := removed.prepend (.single (singleContraction R)) (.single R)
    rcases headGeometry with atHead | separate
    · refine ⟨w,.cons (singleContraction R) middle,.cons R middleAtomic,?_,?_,?_⟩
      · simp only [ParallelHistory.length]; omega
      · intro s hs
        change s∈r::middle.derivation.paths at hs
        rcases List.mem_cons.mp hs with eq | later
        · obtain ⟨a,eq'⟩ := atHead
          exact ⟨a,eq.trans eq'⟩
        · exact inside s later
      · simpa only [ExtractionRun.prepend,ExtractionRun.of,ParallelHistory.single,ParallelHistory.append] using first
    · obtain ⟨z,source,sourceAtomic,paths,sourceInside,second⟩ := (Atomic.single R).extract_disjoint_prefix
        middle middleAtomic inside positive (by
          intro s hs
          have eq : s=r := by simpa [ParallelHistory.single_derivation,ParallelStep.derivation,singleContraction] using hs
          simpa [eq] using separate)
      have sourcePositive : 0<source.length := by
        have eq := congrArg List.length paths
        rw [sourceAtomic.paths_length,middleAtomic.paths_length] at eq
        omega
      refine ⟨z,source,sourceAtomic,sourcePositive,sourceInside,?_⟩
      exact .trans (by simpa only [ExtractionRun.prepend,ExtractionRun.of,ParallelHistory.single,ParallelHistory.append] using first) second

/-- AG5.2.9's right-disjoint source region is an actual single sibling
program, selected from the final occurrence rather than assumed for the
whole outside forest. -/
theorem RightHistory.extract_right_pointed {ρ : ParallelHistory t u}
    (right : RightHistory cut ρ) (ordinary : Atomic ρ) (last : BetaAt u p v)
    (before : LeftOf cut p) (apart : DisjointPositions cut p) :
    ∃ site, DisjointPositions cut site ∧
      ∃ w, ∃ source : ParallelHistory t w, ∃ sourceAtomic : Atomic source,
        0<source.length ∧ Internal site source ∧
        Extraction (.of (ρ.append (.single (singleContraction last))) (ordinary.append (.single last)))
          (.of source sourceAtomic) := by
  obtain ⟨site,q,atSite,separate,geometry⟩ := before.right_sibling apart
  obtain ⟨w,source,sourceAtomic,positive,inside,removed⟩ := ordinary.extract_local_program last atSite (by
    intro r hr; exact geometry r (right.paths_right r hr))
  exact ⟨site,separate,w,source,sourceAtomic,positive,inside,removed⟩

end Lamping.Lambda

