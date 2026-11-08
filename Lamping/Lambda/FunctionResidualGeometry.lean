import Lamping.Lambda.RootResidualSet
import Lamping.Lambda.StepProjectionHead
import Lamping.Lambda.ProjectionFamilies
namespace Lamping.Lambda

theorem StepProjection.head_singleton_residual
    {first : ParallelStep F t u} (A : BetaAt t a v) (B : BetaAt u b w)
    (row : StepProjection first (.cons (singleContraction A) σ)
      (.cons (singleContraction B) τ) last) : first.derivation.Residual ⟨a,A.redex⟩ ⟨b,B.redex⟩ := by
  obtain ⟨sq,hfirst,htop,_,hside,_⟩ := row.head_square
  cases sq with
  | mk start top side vertical =>
    cases hfirst
    cases htop
    exact start.singleton_projection_residual ⟨a,A.redex⟩ ⟨b,B.redex⟩ side
      (congrArg Derivation.paths hside)

theorem ParallelStep.residual_image_target (h : ParallelStep F t u)
    (r : RedexOcc t) (s : RedexOcc u) (image : h.residualSet [r.val] = [q])
    (residual : h.derivation.Residual r s) : h.residualSet [r.val] = [s.val] := by
  have member : s.val ∈ h.residualSet [r.val] :=
    (Marked.mem_setResidualPositions _ _ _).mpr
      ⟨r.val,List.mem_singleton_self _,(h.residual_iff r s).mp residual⟩
  rw [image] at member
  rw [image, List.mem_singleton.mp member]

/-- Coordinates of every actual old function-part residual. The implicit
 function lambda is removed; the body suffix itself is unchanged. -/
theorem BetaAt.function_residual_coordinates (R : BetaAt t p u)
    (r : RedexOcc t) (s : RedexOcc u) (inside : ∃ q,r.val=(p++[.fn])++q)
    (residual : (singleContraction R).derivation.Residual r s) :
    ∃ q, r.val=(p++[.fn,.body])++q ∧ s.val=p++q := by
  obtain ⟨q,source,image⟩ := R.function_residualSet_singleton r inside
  have selected := (singleContraction R).residual_image_target r s image residual
  have target : s.val=p++q := (List.cons.inj (selected.symm.trans image)).1
  exact ⟨q,source,target⟩

theorem BetaAt.function_disjoint_reflect (R : BetaAt t p u)
    (r a : RedexOcc t) (s b : RedexOcc u)
    (hr : ∃ q,r.val=(p++[.fn])++q) (ha : ∃ q,a.val=(p++[.fn])++q)
    (rs : (singleContraction R).derivation.Residual r s)
    (ab : (singleContraction R).derivation.Residual a b)
    (apart : DisjointPositions s.val b.val) : DisjointPositions r.val a.val := by
  obtain ⟨qr,sourceR,targetR⟩ := R.function_residual_coordinates r s hr rs
  obtain ⟨qa,sourceA,targetA⟩ := R.function_residual_coordinates a b ha ab
  constructor
  · rintro ⟨q,hq⟩
    have suffix : qa=qr++q := List.append_cancel_left (as := p ++ [.fn,.body]) (by
      simpa only [sourceA,sourceR,List.append_assoc] using hq)
    exact apart.1 ⟨q,by rw [targetA,targetR,suffix,List.append_assoc]⟩
  · rintro ⟨q,hq⟩
    have suffix : qr=qa++q := List.append_cancel_left (as := p ++ [.fn,.body]) (by
      simpa only [sourceA,sourceR,List.append_assoc] using hq)
    exact apart.2 ⟨q,by rw [targetA,targetR,suffix,List.append_assoc]⟩

theorem BetaAt.function_internal_reflect (R : BetaAt t p u)
    (r a : RedexOcc t) (s b : RedexOcc u)
    (hr : ∃ q,r.val=(p++[.fn])++q) (ha : ∃ q,a.val=(p++[.fn])++q)
    (rs : (singleContraction R).derivation.Residual r s)
    (ab : (singleContraction R).derivation.Residual a b)
    (inside : ∃ q,b.val=(s.val++[.fn])++q) : ∃ q,a.val=(r.val++[.fn])++q := by
  obtain ⟨qr,sourceR,targetR⟩ := R.function_residual_coordinates r s hr rs
  obtain ⟨qa,sourceA,targetA⟩ := R.function_residual_coordinates a b ha ab
  obtain ⟨q,hq⟩ := inside
  have suffix : qa=(qr++[.fn])++q := List.append_cancel_left (by
    simpa only [targetA,targetR,List.append_assoc] using hq)
  exact ⟨q,by rw [sourceA,sourceR,suffix]; simp only [List.append_assoc]⟩

end Lamping.Lambda
