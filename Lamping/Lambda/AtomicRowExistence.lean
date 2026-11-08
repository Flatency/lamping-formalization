import Lamping.Lambda.AtomicProjection
namespace Lamping.Lambda

/-- The two source regions used in extraction (ii) and (iii). -/
def ExtractionRegion (p site : Path) : Prop :=
  DisjointPositions p site ∨ site=p++[.fn]

private theorem region_not_above (h : ExtractionRegion p site)
    (inside : ∃ s, q=site++s) : ¬∃ s, p=q++s := by
  obtain ⟨s,hs⟩ := inside
  rintro ⟨r,hr⟩
  rcases h with hd | he
  · exact hd.2 ⟨s++r,by simpa only [List.append_assoc] using hr.trans (congrArg (·++r) hs)⟩
  · have lengths := congrArg List.length (hr.trans (congrArg (·++r) (hs.trans (congrArg (·++s) he))))
    simp only [List.length_append,List.length_singleton] at lengths
    omega

private theorem disjoint_descendant_outside (hd : DisjointPositions p site)
    (inside : ∃ s, q=site++s) : ¬∃ r, q=p++r := by
  obtain ⟨s,hs⟩ := inside
  rintro ⟨r,hr⟩
  rcases List.prefix_or_prefix_of_prefix (show p <+: q from ⟨r,hr.symm⟩)
      (show site <+: q from ⟨s,hs.symm⟩) with ⟨a,ha⟩ | ⟨a,ha⟩
  · exact hd.1 ⟨a,ha.symm⟩
  · exact hd.2 ⟨a,ha.symm⟩

private theorem residual_member_redex (h : ParallelStep F t u)
    (hp : p∈h.residualSet G) : ∃ z, subtermAt u p=some z ∧ IsRedex z := by
  have valid := ((Marked.completeOld_iff F t).mp h.complete).1.general.valid (Marked.valid_mark F t)
  have redex := Marked.setResidualPositions_sound valid hp
  rw [h.target_eq] at redex
  exact redex

private theorem atomic_single_selection (h : ParallelStep F t u) (he : F=[p])
    (r : RedexOcc t) (hr : r.val=p) : Atomic (.single h) := by
  subst F
  obtain ⟨R,hR⟩ := h.eq_single_contraction r hr
  rw [hR]
  exact .single R

/-- Internal ordinary histories in the two source regions have actual
ordinary projected histories. Atomicity is constructed tile by tile. -/
theorem Atomic.region_projection {σ : ParallelHistory t v} (ha : Atomic σ)
    (vertical : ParallelStep F t u) (selected : F=[p])
    (root : RedexOcc t) (rootPath : root.val=p)
    (region : ExtractionRegion p site) (inside : Internal site σ) :
    ∃ (w : Term) (G : List Path) (σ' : ParallelHistory u w)
      (last : ParallelStep G v w), Atomic σ' ∧ StepProjection vertical σ σ' last := by
  induction ha generalizing F p u with
  | nil => exact ⟨_,_,.nil _,vertical,.nil _,.nil _⟩
  | @cons t q v target tail S htail ih =>
    subst F
    obtain ⟨R,verticalEq⟩ := vertical.eq_single_contraction root rootPath
    subst vertical
    have sourceInside : ∃ s, q=site++s := inside q (by
      simp [ParallelHistory.derivation,Derivation.append,ParallelStep.derivation,singleContraction])
    have tailInside : Internal site tail := by
      intro z hz
      exact inside z (by simp [ParallelHistory.derivation,Derivation.append,hz])
    have leftSelection : ∃ q', (singleContraction R).residualSet [q]=[q'] := by
      rcases region with hd | he
      · exact ⟨q,R.outside_residualSet_singleton ⟨q,S.redex⟩ (disjoint_descendant_outside hd sourceInside)⟩
      · have functionInside : ∃ s, q=(p++[.fn])++s := by simpa only [he] using sourceInside
        obtain ⟨s,_,hs⟩ := R.function_residualSet_singleton ⟨q,S.redex⟩ functionInside
        exact ⟨p++s,hs⟩
    have rightSelection : (singleContraction S).residualSet [p]=[p] :=
      S.outside_residualSet_singleton ⟨p,R.redex⟩ (region_not_above region sourceInside)
    obtain ⟨mid,left,right,_⟩ := parallel_moves (singleContraction R) (singleContraction S)
    obtain ⟨q',leftSelected⟩ := leftSelection
    let projectedRedex : RedexOcc u := ⟨q',residual_member_redex (singleContraction R)
      (by rw [leftSelected]; simp)⟩
    let remainingRedex : RedexOcc v := ⟨p,residual_member_redex (singleContraction S)
      (by rw [rightSelection]; simp)⟩
    have atomicLeft := atomic_single_selection left leftSelected projectedRedex rfl
    obtain ⟨w,G,projected,last,atomicTail,rowTail⟩ :=
      ih right rightSelection remainingRedex rfl region tailInside
    exact ⟨w,G,.cons left projected,last,atomicLeft.append atomicTail,
      .cons ⟨singleContraction R,singleContraction S,left,right⟩ rowTail⟩

theorem Atomic.disjoint_projection {σ : ParallelHistory t v} (ha : Atomic σ)
    (R : BetaAt t p u) (apart : DisjointPositions p site) (inside : Internal site σ) :
    ∃ (w : Term) (G : List Path) (σ' : ParallelHistory u w)
      (last : ParallelStep G v w), Atomic σ' ∧
      StepProjection (singleContraction R) σ σ' last :=
  ha.region_projection (singleContraction R) rfl ⟨p,R.redex⟩ rfl (.inl apart) inside

theorem Atomic.function_projection {σ : ParallelHistory t v} (ha : Atomic σ)
    (R : BetaAt t p u) (inside : Internal (p++[.fn]) σ) :
    ∃ (w : Term) (G : List Path) (σ' : ParallelHistory u w)
      (last : ParallelStep G v w), Atomic σ' ∧
      StepProjection (singleContraction R) σ σ' last :=
  ha.region_projection (singleContraction R) rfl ⟨p,R.redex⟩ rfl (.inr rfl) inside

end Lamping.Lambda
