import Lamping.Lambda.ProjectionOrder
namespace Lamping.Lambda
private theorem projection_uncons {first : ParallelStep F t u} {top : ParallelStep H t v}
    {rest : ParallelHistory v x} {full : ParallelHistory u z} {last : ParallelStep G x z}
    (row : StepProjection first (.cons top rest) full last) :
    ∃ (mid : Term) (tail : ParallelHistory mid z) (sq : ParallelMovesSquare F H t u v mid),
      sq.first=first ∧ sq.second=top ∧ full=.cons sq.afterFirst tail ∧
      StepProjection sq.afterSecond rest tail last := by
  cases row with | cons sq tail => exact ⟨_,_,sq,rfl,rfl,rfl,tail⟩

/-- Reflect ordinary standardness through the actual disjoint/function-part
projection row. The source region supplies unique order-preserving old images;
any forbidden return would be a genuine forbidden return in the projected row. -/
theorem Atomic.region_standard_reflect {original : ParallelHistory t v} (ordinary : Atomic original)
    (vertical : ParallelStep F t u) (selected : F=[p]) (root : RedexOcc t) (rootAt : root.val=p)
    (region : ExtractionRegion p site) (inside : Internal site original)
    {full : ParallelHistory u z} {last : ParallelStep G v z}
    (row : StepProjection vertical original full last) (copyAtomic : Atomic full) (standard : Standard full) :
    Standard original := by
  induction ordinary generalizing F u p z G with
  | nil => exact .nil _
  | @cons t s mid v original S oldAtomic ih =>
    subst F
    obtain ⟨R,verticalEq⟩ := vertical.eq_single_contraction root rootAt
    subst vertical
    have sourceInside : ∃ q,s=site++q := inside s (by
      simp [ParallelHistory.derivation,Derivation.append,ParallelStep.derivation,singleContraction])
    have tailInside : Internal site original := by
      intro r hr; exact inside r (by simp [ParallelHistory.derivation,Derivation.append,hr])
    have rootOutside : ¬∃ q,p=s++q := by
      obtain ⟨tail,atSite⟩ := sourceInside
      rintro ⟨suffix,eq⟩
      rcases region with apart | function
      · exact apart.2 ⟨tail++suffix,by simpa only [List.append_assoc] using eq.trans (congrArg (·++suffix) atSite)⟩
      · rw [function] at atSite
        have lengths := congrArg List.length (eq.trans (congrArg (·++suffix) atSite))
        simp only [List.length_append,List.length_singleton] at lengths
        omega
    have rootSelection : (singleContraction S).residualSet [p]=[p] :=
      S.outside_residualSet_singleton ⟨p,R.redex⟩ rootOutside
    let nextRoot : RedexOcc mid := ⟨p,(singleContraction S).residualSet_valid p (by rw [rootSelection]; simp)⟩
    obtain ⟨fullMid,fullTail,square,firstEq,secondEq,fullEq,tailRow⟩ := projection_uncons row
    rcases square with ⟨firstVertical,firstOriginal,projected,remainingRoot⟩
    simp only at firstEq secondEq fullEq tailRow
    subst firstVertical
    subst firstOriginal
    have projectedAtomic : Atomic (.single projected) := by
      rw [fullEq] at copyAtomic
      exact (copyAtomic.split_append (ρ:=.single projected) (σ:=fullTail)).1
    have tailAtomic : Atomic fullTail := by
      rw [fullEq] at copyAtomic
      exact (copyAtomic.split_append (ρ:=.single projected) (σ:=fullTail)).2
    obtain ⟨q,T,paths⟩ := projectedAtomic.single_step
    have singleEq : ParallelHistory.single projected=.single (singleContraction T) :=
      projectedAtomic.paths_injective (.single T) (by simpa only [ParallelHistory.single_derivation] using paths)
    have canonicalStandard : Standard ((ParallelHistory.single (singleContraction T)).append fullTail) := by
      rw [←singleEq]
      rw [fullEq] at standard
      exact standard
    cases canonicalStandard with
    | cons _ witness lo noReturn restStandard =>
      have noReturnSource : DoesNotReturnLeft ⟨s,S.redex⟩ (.cons (singleContraction S) original) := by
        apply DoesNotReturnLeft.of_no_used
        intro old before used
        have sourceOld := used.internal (.cons S oldAtomic) inside
        have projectedResidual : (singleContraction R).derivation.Residual ⟨s,S.redex⟩ ⟨q,T.redex⟩ :=
          (singleContraction R).singleton_projection_residual ⟨s,S.redex⟩ ⟨q,T.redex⟩ projected paths
        obtain ⟨image,leftImage,unique⟩ := R.region_left_image region ⟨s,S.redex⟩ sourceInside
          ⟨q,T.redex⟩ projectedResidual old sourceOld before
        have projectedUsed := UsedSource.project_unique row (.cons S oldAtomic) copyAtomic old image unique used
        rw [fullEq] at projectedUsed
        change UsedSource ((ParallelHistory.single projected).append fullTail) image at projectedUsed
        rw [singleEq] at projectedUsed
        have witnessAt : witness.val=q := List.mem_singleton.mp lo.1
        exact noReturn.no_used_left ((Atomic.single T).append tailAtomic) image
          (by rw [witnessAt]; exact leftImage) projectedUsed
      exact .cons (singleContraction S) ⟨s,S.redex⟩ (leftmost_singleton _) noReturnSource
        (ih remainingRoot rootSelection nextRoot rfl region tailInside tailRow tailAtomic restStandard)
end Lamping.Lambda
