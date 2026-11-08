import Lamping.Lambda.CreationIntersection
import Lamping.Lambda.UsedSourceContexts
import Lamping.Lambda.ProjectionOrder
import Lamping.Lambda.ExtractionRegionGeometry
namespace Lamping.Lambda

private theorem row_uncons {first : ParallelStep F t u} {top : ParallelStep H t v}
    {rest : ParallelHistory v x} {full : ParallelHistory u z} {last : ParallelStep G x z}
    (row : StepProjection first (.cons top rest) full last) :
    ∃ (mid : Term) (tail : ParallelHistory mid z) (sq : ParallelMovesSquare F H t u v mid),
      sq.first=first ∧ sq.second=top ∧ full=.cons sq.afterFirst tail ∧
      StepProjection sq.afterSecond rest tail last := by
  cases row with | cons sq tail => exact ⟨_,_,sq,rfl,rfl,rfl,tail⟩

/-- An initial bottom redex actually used by a region projection has an
actual used initial source ancestor. The later-use case invokes the genuine
two-arm creation intersection of each tile, not ancestry of arbitrary newly
created target redexes. -/
theorem UsedSource.region_project_reflect {σ : ParallelHistory t v}
    (ordinary : Atomic σ) (vertical : ParallelStep F t u) (selected : F=[p])
    (root : RedexOcc t) (rootAt : root.val=p) (region : ExtractionRegion p site)
    (inside : Internal site σ) {τ : ParallelHistory u w} {last : ParallelStep G v w}
    (row : StepProjection vertical σ τ last) (r : RedexOcc u) (used : UsedSource τ r) :
    ∃ old : RedexOcc t, vertical.derivation.Residual old r ∧ UsedSource σ old := by
  induction ordinary generalizing F u p w G with
  | nil t =>
    cases row
    obtain ⟨a,b,H,pre,step,suffix,q,eq,_,_⟩ := used
    have lengths := congrArg ParallelHistory.length eq
    simp only [ParallelHistory.length,ParallelHistory.length_append] at lengths
    omega
  | @cons t q mid v tail S atomic ih =>
    subst F
    obtain ⟨R,eqVertical⟩ := vertical.eq_single_contraction root rootAt
    subst vertical
    have atSite : ∃a,q=site++a := inside q (by
      simp [ParallelHistory.derivation,Derivation.append,ParallelStep.derivation,singleContraction])
    have tailInside : Internal site tail := by
      intro s hs; exact inside s (by simp [ParallelHistory.derivation,Derivation.append,hs])
    have remainingSelection : (singleContraction S).residualSet [p]=[p] :=
      S.outside_residualSet_singleton ⟨p,R.redex⟩ (region.not_above atSite)
    let nextRoot : RedexOcc mid := ⟨p,(singleContraction S).residualSet_valid p (by rw [remainingSelection]; simp)⟩
    obtain ⟨bottomMid,bottomTail,square,firstEq,secondEq,bottomEq,tailRow⟩ := row_uncons row
    rcases square with ⟨firstVertical,firstTop,projected,remaining⟩
    simp only at firstEq secondEq bottomEq tailRow
    subst firstVertical
    subst firstTop
    rw [bottomEq] at used
    rcases (UsedSource.cons_iff projected bottomTail r).mp used with first | ⟨image,survives,later⟩
    · obtain ⟨old,headSelected,residual⟩ := ((singleContraction R).mem_residualSet_iff
        (by intro s hs; cases List.mem_singleton.mp hs; exact S.redex) r).mp first
      exact ⟨old,residual,(UsedSource.cons_iff (singleContraction S) tail old).mpr (.inl headSelected)⟩
    · obtain ⟨middle,fromMiddle,middleUsed⟩ := ih remaining remainingSelection nextRoot rfl region tailInside tailRow image later
      have distinct : p≠q := by
        intro same
        exact region.not_above atSite ⟨[],by simpa using same⟩
      obtain ⟨old,left,right⟩ := creation_common_ancestor R S distinct projected remaining r middle image survives fromMiddle
      obtain ⟨afterR,oldR,afterProjected⟩ := (Derivation.residual_append _ _ old image).mp left
      have sameR : afterR=r := Derivation.residual_unique_source projected.derivation afterR r image afterProjected survives
      subst afterR
      obtain ⟨afterS,oldS,afterRemaining⟩ := (Derivation.residual_append _ _ old image).mp right
      have sameS : afterS=middle := Derivation.residual_unique_source remaining.derivation afterS middle image afterRemaining fromMiddle
      subst afterS
      exact ⟨old,oldR,(UsedSource.cons_iff (singleContraction S) tail old).mpr (.inr ⟨middle,oldS,middleUsed⟩)⟩

theorem BetaAt.region_left_reflect (R : BetaAt t p u) (region : ExtractionRegion p site)
    (head old : RedexOcc t) (imageHead imageOld : RedexOcc u)
    (headInside : ∃q,head.val=site++q) (oldInside : ∃q,old.val=site++q)
    (headResidual : (singleContraction R).derivation.Residual head imageHead)
    (oldResidual : (singleContraction R).derivation.Residual old imageOld)
    (before : LeftOf imageOld.val imageHead.val) : LeftOf old.val head.val := by
  rcases region with apart | function
  · obtain ⟨h,headAt⟩ := headInside
    obtain ⟨o,oldAt⟩ := oldInside
    have headApart : DisjointPositions p head.val := by
      rw [headAt]; exact (apart.symm.descend_left h).symm
    have oldApart : DisjointPositions p old.val := by
      rw [oldAt]; exact (apart.symm.descend_left o).symm
    have headFixed := (R.disjoint_residual_iff head headApart imageHead).mp headResidual
    have oldFixed := (R.disjoint_residual_iff old oldApart imageOld).mp oldResidual
    simpa only [←headFixed,←oldFixed] using before
  · subst site
    obtain ⟨h,headAt,imageHeadAt⟩ := R.function_residual_coordinates head imageHead headInside headResidual
    obtain ⟨o,oldAt,imageOldAt⟩ := R.function_residual_coordinates old imageOld oldInside oldResidual
    rw [imageHeadAt,imageOldAt] at before
    rw [headAt,oldAt]
    exact before.strip_prefix.prefix_append (p++[.fn,.body])

private theorem standard_head_no_return (S : BetaAt t q mid) (tail : ParallelHistory mid v)
    (standard : Standard (.cons (singleContraction S) tail)) :
    DoesNotReturnLeft ⟨q,S.redex⟩ (.cons (singleContraction S) tail) := by
  cases standard with
  | cons _ witness lo nr rest =>
    have eq : witness=⟨q,S.redex⟩ := Subtype.ext (List.mem_singleton.mp lo.1)
    subst witness
    exact nr

/-- A given actual ordinary projection in a function or disjoint region
preserves standardness. Created bottom redexes are handled through the
proved used-source reflection, rather than assumed to have ancestors. -/
theorem Atomic.region_standard_project {σ : ParallelHistory t v} (ordinary : Atomic σ)
    (vertical : ParallelStep F t u) (selected : F=[p]) (root : RedexOcc t) (rootAt : root.val=p)
    (region : ExtractionRegion p site) (inside : Internal site σ)
    {τ : ParallelHistory u w} {last : ParallelStep G v w}
    (row : StepProjection vertical σ τ last) (targetAtomic : Atomic τ) (standard : Standard σ) :
    Standard τ := by
  induction ordinary generalizing F u p w G with
  | nil t => cases row; exact .nil _
  | @cons t q mid v tail S atomic ih =>
    subst F
    obtain ⟨R,eqVertical⟩ := vertical.eq_single_contraction root rootAt
    subst vertical
    have atSite : ∃a,q=site++a := inside q (by
      simp [ParallelHistory.derivation,Derivation.append,ParallelStep.derivation,singleContraction])
    have tailInside : Internal site tail := by
      intro s hs; exact inside s (by simp [ParallelHistory.derivation,Derivation.append,hs])
    have remainingSelection : (singleContraction S).residualSet [p]=[p] :=
      S.outside_residualSet_singleton ⟨p,R.redex⟩ (region.not_above atSite)
    let nextRoot : RedexOcc mid := ⟨p,(singleContraction S).residualSet_valid p (by rw [remainingSelection]; simp)⟩
    obtain ⟨bottomMid,bottomTail,square,firstEq,secondEq,bottomEq,tailRow⟩ := row_uncons row
    rcases square with ⟨firstVertical,firstTop,projected,remaining⟩
    simp only at firstEq secondEq bottomEq tailRow
    subst firstVertical
    subst firstTop
    have piecesAtomic : Atomic (.single projected) ∧ Atomic bottomTail := by
      rw [bottomEq] at targetAtomic
      exact targetAtomic.split_append (ρ:=.single projected) (σ:=bottomTail)
    obtain ⟨h,T,paths⟩ := piecesAtomic.1.single_step
    have headResidual := (singleContraction R).singleton_projection_residual ⟨q,S.redex⟩ ⟨h,T.redex⟩ projected paths
    have oneImage : ∃r,(singleContraction R).residualSet [q]=[r] := by
      rcases region with apart | function
      · exact ⟨q,R.outside_residualSet_singleton ⟨q,S.redex⟩ (apart.descendant_outside atSite)⟩
      · obtain ⟨r,_,image⟩ := R.function_residualSet_singleton ⟨q,S.redex⟩ (by simpa only [function] using atSite)
        exact ⟨p++r,image⟩
    obtain ⟨h',image⟩ := oneImage
    have selectedHead := (singleContraction R).residual_image_target ⟨q,S.redex⟩ ⟨h,T.redex⟩ image headResidual
    have targetNoReturn : DoesNotReturnLeft ⟨h,T.redex⟩ τ := by
      apply DoesNotReturnLeft.of_no_used
      intro old before used
      obtain ⟨original,residual,usedSource⟩ := UsedSource.region_project_reflect (.cons S atomic)
        (singleContraction R) rfl ⟨p,R.redex⟩ rfl region inside row old used
      have originalInside := usedSource.internal (.cons S atomic) inside
      have originalBefore := R.region_left_reflect region ⟨q,S.redex⟩ original ⟨h,T.redex⟩ old
        atSite originalInside headResidual residual before
      exact (standard_head_no_return S tail standard).no_used_left (.cons S atomic) original originalBefore usedSource
    rw [bottomEq]
    refine .cons projected ⟨h,T.redex⟩ ?_ (by rw [←bottomEq]; exact targetNoReturn) ?_
    · rw [selectedHead]; exact leftmost_singleton _
    · exact ih remaining remainingSelection nextRoot rfl region tailInside tailRow piecesAtomic.2
        (standard.suffix (ρ:=.single (singleContraction S)) (σ:=tail))

/-- The whole actual outer-beta/function projection is standard as well as
its suffix, exactly the standard source interface used in AG5.2.9(ii). -/
theorem Atomic.function_projection_standard {σ : ParallelHistory t v} (ordinary : Atomic σ)
    (R : BetaAt t p u) (inside : Internal (p++[.fn]) σ)
    {τ : ParallelHistory u w} {last : ParallelStep G v w}
    (row : StepProjection (singleContraction R) σ τ last) (targetAtomic : Atomic τ)
    (standard : Standard σ) :
    Standard ((ParallelHistory.single (singleContraction R)).append τ) ∧ Standard τ := by
  have targetStandard := ordinary.region_standard_project (singleContraction R) rfl ⟨p,R.redex⟩ rfl
    (.inr rfl) inside row targetAtomic standard
  refine ⟨.cons (singleContraction R) ⟨p,R.redex⟩ (leftmost_singleton _) ?_ targetStandard,targetStandard⟩
  apply DoesNotReturnLeft.of_no_used
  intro old before used
  rcases (UsedSource.cons_iff (singleContraction R) τ old).mp used with selected | ⟨image,residual,later⟩
  · have same : old.val=p := List.mem_singleton.mp selected
    exact LeftOf.irrefl p (by simpa only [same] using before)
  · obtain ⟨original,oldResidual,usedSource⟩ := UsedSource.region_project_reflect ordinary
      (singleContraction R) rfl ⟨p,R.redex⟩ rfl (.inr rfl) inside row image later
    have same : original=old := Derivation.residual_unique_source (singleContraction R).derivation original old image oldResidual residual
    subst original
    obtain ⟨q,atFunction⟩ := usedSource.internal ordinary inside
    exact before.not_inside_right ⟨[.fn]++q,by simpa only [List.append_assoc] using atFunction⟩

end Lamping.Lambda

