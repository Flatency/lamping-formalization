import Lamping.Lambda.AtomicRowExistence
import Lamping.Lambda.FunctionResidualGeometry
namespace Lamping.Lambda

theorem DisjointPositions.prefix_iff (pre r site : Path) :
    DisjointPositions (pre ++ r) (pre ++ site) ↔ DisjointPositions r site := by
  constructor
  · rintro ⟨h1,h2⟩
    constructor
    · rintro ⟨q,hq⟩; exact h1 ⟨q,by rw [hq,List.append_assoc]⟩
    · rintro ⟨q,hq⟩; exact h2 ⟨q,by rw [hq,List.append_assoc]⟩
  · rintro ⟨h1,h2⟩
    constructor
    · rintro ⟨q,hq⟩
      exact h1 ⟨q,List.append_cancel_left (by simpa only [List.append_assoc] using hq)⟩
    · rintro ⟨q,hq⟩
      exact h2 ⟨q,List.append_cancel_left (by simpa only [List.append_assoc] using hq)⟩

theorem DisjointPositions.descendant_outside (apart : DisjointPositions p site)
    (inside : ∃q,r=site++q) : ¬∃q,r=p++q := by
  obtain ⟨localPath,hr⟩ := inside
  rintro ⟨q,hq⟩
  rcases List.prefix_or_prefix_of_prefix
    (show p <+: r from ⟨q,hq.symm⟩) (show site <+: r from ⟨localPath,hr.symm⟩)
      with ⟨s,hs⟩ | ⟨s,hs⟩
  · exact apart.1 ⟨s,hs.symm⟩
  · exact apart.2 ⟨s,hs.symm⟩

theorem ExtractionRegion.prefix_iff (pre r site : Path) :
    ExtractionRegion (pre ++ r) (pre ++ site) ↔ ExtractionRegion r site := by
  unfold ExtractionRegion
  rw [DisjointPositions.prefix_iff]
  have function : pre ++ site = (pre ++ r) ++ [.fn] ↔ site = r ++ [.fn] := by
    rw [List.append_assoc]
    exact ⟨List.append_cancel_left,congrArg (pre ++ ·)⟩
  rw [function]

theorem ExtractionRegion.root_outside (region : ExtractionRegion p site) : ¬∃q,p=site++q := by
  rcases region with apart | function
  · exact apart.2
  · rintro ⟨q,hq⟩
    rw [function] at hq
    have len := congrArg List.length hq
    simp only [List.length_append,List.length_singleton] at len
    omega

theorem ExtractionRegion.not_above (region : ExtractionRegion p site)
    (inside : ∃ q,r=site++q) : ¬∃q,p=r++q := by
  obtain ⟨localPath,hr⟩ := inside
  rintro ⟨q,hq⟩
  exact region.root_outside ⟨localPath++q,by simpa only [hr,List.append_assoc] using hq⟩

/-- A source region containing an occurrence below p cannot straddle p when
 its excluded contraction is itself below p. -/
theorem ExtractionRegion.site_inside (region : ExtractionRegion s site)
    (first : ∃q,s=p++q) (inside : ∃q,r=p++q) (scope : ∃q,r=site++q) :
    ∃q,site=p++q := by
  obtain ⟨a,ha⟩ := inside
  obtain ⟨b,hb⟩ := scope
  rcases List.prefix_or_prefix_of_prefix
    (show p <+: r from ⟨a,ha.symm⟩) (show site <+: r from ⟨b,hb.symm⟩)
      with ⟨q,hq⟩ | ⟨q,hq⟩
  · exact ⟨q,hq.symm⟩
  · obtain ⟨c,hc⟩ := first
    exact False.elim (region.root_outside ⟨q++c,by simpa only [←hq,List.append_assoc] using hc⟩)

theorem BetaAt.function_site_reflect (R : BetaAt t p u)
    (r : RedexOcc t) (s : RedexOcc u) (inside : ∃q,r.val=(p++[.fn])++q)
    (residual : (singleContraction R).derivation.Residual r s)
    (scope : ∃q,s.val=(p++site)++q) :
    ∃q,r.val=((p++[.fn,.body])++site)++q := by
  obtain ⟨q,source,target⟩ := R.function_residual_coordinates r s inside residual
  obtain ⟨tail,ht⟩ := scope
  have localName : q=site++tail := List.append_cancel_left (as := p) (by
    simpa only [target,List.append_assoc] using ht)
  exact ⟨tail,by rw [source,localName]; simp only [List.append_assoc]⟩

theorem BetaAt.region_residual_image (R : BetaAt t p u) (r : RedexOcc t) (s : RedexOcc u)
    (region : ExtractionRegion p site) (inside : ∃q,r.val=site++q)
    (residual : (singleContraction R).derivation.Residual r s) :
    (singleContraction R).residualSet [r.val] = [s.val] := by
  rcases region with apart | function
  · exact (singleContraction R).residual_image_target r s
      (R.outside_residualSet_singleton r (apart.descendant_outside inside)) residual
  · have functionInside : ∃q,r.val=(p++[.fn])++q := by simpa only [function] using inside
    obtain ⟨q,_,image⟩ := R.function_residualSet_singleton r functionInside
    exact (singleContraction R).residual_image_target r s image residual

end Lamping.Lambda
