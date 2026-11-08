import Lamping.Lambda.Needed
import Lamping.Lambda.OccurrenceOrder
import Lamping.Lambda.StandardizationNoReturn
import Lamping.Lambda.StandardizationGeneral

namespace Lamping.Lambda

/-- A proposition about an actual finite history, with each singleton head
selected by the computable leftmost-outermost search. -/
inductive LOHistory : {t u : Term} → ParallelHistory t u → Prop where
  | nil (t : Term) : LOHistory (.nil t)
  | cons {t v u : Term} {p : Path} {tail : ParallelHistory v u}
      (head : BetaAt t p v) : loRedex t = some p → LOHistory tail →
      LOHistory (.cons (singleContraction head) tail)

theorem loRedex_eq_of_leftmost {t : Term} (r : RedexOcc t)
    (leftmost : ∀ s : RedexOcc t, ¬LeftOf s.val r.val) :
    loRedex t = some r.val := by
  cases hit : loRedex t with
  | none => exact False.elim ((loRedex_none_iff t).mp hit r)
  | some p =>
    let chosen : RedexOcc t := ⟨p,loRedex_sound hit⟩
    have same : chosen = r := by
      rcases chosen.compare r with equal | earlier | later
      · exact equal
      · exact False.elim (leftmost chosen earlier)
      · exact False.elim (loRedex_leftmost hit r later)
    exact congrArg some (congrArg Subtype.val same)

theorem Standard.atomic_head_leftmost {t v u : Term} {p : Path}
    (head : BetaAt t p v) (tail : ParallelHistory v u) (atomic : Atomic tail)
    (standard : Standard (.cons (singleContraction head) tail))
    (normal : BetaNF u) : ∀ s : RedexOcc t, ¬LeftOf s.val p := by
  cases standard with
  | cons _ r selected noReturn _ =>
    have atHead : r.val = p := List.mem_singleton.mp selected.1
    intro s earlier
    have right : RightHistory s.val (.cons (singleContraction head) tail) :=
      (ParallelHistory.cons (singleContraction head) tail).right_of_no_used s (by
        intro q before
        apply noReturn.no_used_left (.cons head atomic) q
        rw [atHead]
        rcases before with same | left
        · rw [same]
          exact earlier
        · exact left.trans earlier)
    obtain ⟨q,_position,_residual⟩ :=
      (ParallelHistory.cons (singleContraction head) tail).derivation.left_survives
        s right.paths_right
    exact normal q

theorem Standard.lo_of_normal {t u : Term} {rho : ParallelHistory t u}
    (standard : Standard rho) (atomic : Atomic rho) (normal : BetaNF u) :
    LOHistory rho := by
  revert standard normal
  induction atomic with
  | nil t =>
    intro _standard _normal
    exact .nil t
  | @cons source path mid target rest head restAtomic ih =>
    intro standard normal
    have leftmost := Standard.atomic_head_leftmost head rest restAtomic standard normal
    cases standard with
    | cons _ _ _ _ restStandard =>
      exact .cons head (loRedex_eq_of_leftmost ⟨path,head.redex⟩ leftmost)
        (ih restStandard normal)

private theorem betas_atomic_exists {t u : Term} (steps : Betas t u) :
    ∃ rho : ParallelHistory t u, Atomic rho := by
  induction steps with
  | refl t => exact ⟨.nil t,.nil t⟩
  | cons step _ ih =>
    obtain ⟨p,head⟩ := beta_iff_betaAt.mp step
    obtain ⟨tail,atomic⟩ := ih
    exact ⟨.cons (singleContraction head) tail,.cons head atomic⟩

theorem HasNF.exists_lo {t : Term} (normalizable : HasNF t) :
    ∃ (n : Term) (rho : ParallelHistory t n), LOHistory rho ∧ BetaNF n := by
  obtain ⟨n,steps,normal⟩ := normalizable
  obtain ⟨rho,_atomic⟩ := betas_atomic_exists steps
  obtain ⟨sigma,atomic,standard,_permutation⟩ := atomic_standardization_exists rho
  exact ⟨n,sigma,standard.lo_of_normal atomic normal,normal⟩

#print axioms LOHistory
#print axioms loRedex_eq_of_leftmost
#print axioms Standard.atomic_head_leftmost
#print axioms Standard.lo_of_normal
#print axioms HasNF.exists_lo

end Lamping.Lambda
