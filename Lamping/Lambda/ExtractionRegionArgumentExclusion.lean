import Lamping.Lambda.ExtractionArgumentResidualPeak
import Lamping.Lambda.AtomicRowExistence
import Lamping.Lambda.StepProjectionHead
import Lamping.Lambda.ResidualOrigins
import Lamping.Lambda.ExtractionInternal
namespace Lamping.Lambda

/-- A nonempty chosen argument-copy schedule cannot simultaneously be an
 ordinary projection from a disjoint or function region of the same redex.
 Its first contraction would then have two distinct old origins. -/
theorem ArgumentLift.no_region_projection (R : BetaAt t p u)
    {σ : ParallelHistory t a} {copy : ParallelHistory u b} {original : ParallelHistory t c}
    {last : ParallelStep F a b}
    (lift : ArgumentLift R copy original)
    (row : StepProjection (singleContraction R) σ copy last)
    (ha : Atomic σ) (hb : Atomic copy) (hc : Atomic original)
    (region : ExtractionRegion p site) (inside : Internal site σ) (positive : 0 < copy.length) : False := by
  cases hb with
  | nil => change 0 < 0 at positive; omega
  | @cons u s v b rest S hrest =>
    cases ha with
    | nil =>
      have len := row.length
      simp only [ParallelHistory.length] at len
      omega
    | @cons t s' v' a tail U htail =>
      cases hc with
      | nil =>
        have len := lift.length (.cons S hrest) (.nil t)
        simp only [ParallelHistory.length] at len
        omega
      | @cons t originalPath c' c originalTail A horiginal =>
        have argument := lift.head_residual R S A rest originalTail
        obtain ⟨sq, hfirst, htop, _, hside, _⟩ := row.head_square
        cases sq with
        | mk first top side vertical =>
          cases hfirst
          cases htop
          have other := (singleContraction R).singleton_projection_residual
            ⟨s', U.redex⟩ ⟨s, S.redex⟩ side (congrArg Derivation.paths hside)
          have origin := (singleContraction R).derivation.residual_unique_source
            ⟨originalPath, A.redex⟩ ⟨s', U.redex⟩ ⟨s, S.redex⟩ argument other
          have names : originalPath = s' := congrArg Subtype.val origin
          obtain ⟨localArgument, originalName⟩ := lift.original_internal originalPath
            (by change originalPath ∈ originalPath :: _; exact List.mem_cons_self)
          obtain ⟨localOther, otherName⟩ := inside s'
            (by change s' ∈ s' :: _; exact List.mem_cons_self)
          rcases region with apart | function
          · have shared : s' = p ++ ([.arg] ++ localArgument) := by
              rw [← names, originalName, List.append_assoc]
            rcases List.prefix_or_prefix_of_prefix
              (show p <+: s' from ⟨[.arg] ++ localArgument, shared.symm⟩)
              (show site <+: s' from ⟨localOther, otherName.symm⟩) with ⟨q,hq⟩ | ⟨q,hq⟩
            · exact apart.1 ⟨q,hq.symm⟩
            · exact apart.2 ⟨q,hq.symm⟩
          · have impossible : ([Step.arg] ++ localArgument) = [.fn] ++ localOther := by
              apply List.append_cancel_left (as := p)
              simpa only [function, List.append_assoc] using originalName.symm.trans (names.trans otherName)
            cases impossible

end Lamping.Lambda
