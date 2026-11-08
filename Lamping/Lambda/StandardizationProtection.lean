import Lamping.Lambda.StandardizationExtraction
import Lamping.Lambda.StandardizationCreation
import Lamping.Lambda.StandardizationExistence
namespace Lamping.Lambda
/-- An original redex actually contributes to a selected contraction somewhere
in the history, with the real prefix residual and intermediate selection. -/
def UsedSource (ρ : ParallelHistory t u) (r : RedexOcc t) : Prop :=
  ∃ (v w : Term) (F : List Path) (pre : ParallelHistory t v)
    (step : ParallelStep F v w) (suffix : ParallelHistory w u) (q : RedexOcc v),
    ρ=pre.append (.cons step suffix) ∧ q.val∈F ∧ pre.derivation.Residual r q

theorem UsedSource.prepend {ρ : ParallelHistory t u} {r : RedexOcc t}
    (used : UsedSource ρ r) (pre : ParallelHistory s t) (old : RedexOcc s)
    (ancestor : pre.derivation.Residual old r) : UsedSource (pre.append ρ) old := by
  obtain ⟨v,w,F,prefixHistory,step,suffix,q,eq,selected,residual⟩ := used
  refine ⟨v,w,F,pre.append prefixHistory,step,suffix,q,?_,selected,?_⟩
  · rw [eq,ParallelHistory.append_assoc]
  · rw [ParallelHistory.derivation_append,Derivation.residual_append]
    exact ⟨r,ancestor,residual⟩

theorem ParallelStep.no_selected_residual (h : ParallelStep F t u) (r : RedexOcc t)
    (selected : r.val∈F) (q : RedexOcc u) : ¬h.derivation.Residual r q := by
  intro residual
  have member := (Marked.mem_setResidualPositions F h.markedTarget q.val).mpr
    ⟨r.val,selected,(h.residual_iff r q).mp residual⟩
  rw [h.complete.2] at member
  exact List.not_mem_nil member

theorem BetaHistory.reflect_left (h : BetaHistory ps t u)
    (right : ∀ p∈ps, LeftOf cut p) (earlier : LeftOf q cut)
    (redex : ∃ z, subtermAt u q=some z ∧ IsRedex z) :
    ∃ z, subtermAt t q=some z ∧ IsRedex z := by
  induction h with
  | nil => exact redex
  | cons first tail ih =>
    apply first.redex_reflect_before (right _ (List.mem_cons_self ..)) earlier
    exact ih (fun p hp => right p (List.mem_cons_of_mem _ hp)) redex

theorem ParallelStep.reflect_left (h : ParallelStep F t u) (r : RedexOcc t)
    (right : ∀ q : RedexOcc t, q.val∈F → LeftOf r.val q.val)
    (before : LeftOf p r.val) (redex : ∃ z, subtermAt u p=some z ∧ IsRedex z) :
    ∃ z, subtermAt t p=some z ∧ IsRedex z := by
  have paths : ∀ p∈h.paths, LeftOf r.val p := by
    apply ((Marked.completeOld_iff F t).mp h.complete).1.right_paths
    intro p hp
    obtain ⟨selected,valid⟩ := (Marked.active_mark F t p).mp hp
    exact right ⟨p,(mem_redexPositions t p).mp valid⟩ selected
  exact h.derivation.valid.reflect_left paths before redex
end Lamping.Lambda
namespace Lamping.Lambda
theorem RightHistory.append (h : RightHistory cut ρ) (k : RightHistory cut σ) :
    RightHistory cut (ρ.append σ) := by
  induction h with
  | nil => exact k
  | cons first tail right rest ih => exact .cons first _ right (ih k)

def RightUsedSource (ρ : ParallelHistory t u) (r : RedexOcc t) (cut : Path) : Prop :=
  ∃ (v w : Term) (F : List Path) (pre : ParallelHistory t v)
    (step : ParallelStep F v w) (suffix : ParallelHistory w u) (q : RedexOcc v),
    ρ=pre.append (.cons step suffix) ∧ RightHistory cut pre ∧ q.val∈F ∧ pre.derivation.Residual r q

theorem RightUsedSource.used (h : RightUsedSource ρ r cut) : UsedSource ρ r := by
  obtain ⟨v,w,F,pre,step,suffix,q,eq,_,selected,residual⟩ := h
  exact ⟨v,w,F,pre,step,suffix,q,eq,selected,residual⟩

theorem RightUsedSource.prepend {ρ : ParallelHistory t u} {r : RedexOcc t}
    (used : RightUsedSource ρ r cut) (pre : ParallelHistory s t) (old : RedexOcc s)
    (ancestor : pre.derivation.Residual old r) (right : RightHistory cut pre) :
    RightUsedSource (pre.append ρ) old cut := by
  obtain ⟨v,w,F,prefixHistory,step,suffix,q,eq,prefixRight,selected,residual⟩ := used
  refine ⟨v,w,F,pre.append prefixHistory,step,suffix,q,?_,right.append prefixRight,selected,?_⟩
  · rw [eq,ParallelHistory.append_assoc]
  · rw [ParallelHistory.derivation_append,Derivation.residual_append]
    exact ⟨r,ancestor,residual⟩
/-- Either the entire history respects a protected left cut, or it selects an
original redex at/before that cut and eliminates all its original residuals.
Fresh creation cannot be used as a hidden left contraction. -/
theorem ParallelHistory.right_or_kills_left (ρ : ParallelHistory t u) (s : RedexOcc t) :
    RightHistory s.val ρ ∨ ∃ r : RedexOcc t,
      (r.val=s.val ∨ LeftOf r.val s.val) ∧ RightUsedSource ρ r s.val ∧
      ∀ q : RedexOcc u, ¬ρ.derivation.Residual r q := by
  classical
  induction ρ with
  | nil t => exact Or.inl (.nil t)
  | @cons t v u F step tail ih =>
    by_cases allRight : ∀ r : RedexOcc t, r.val∈F → LeftOf s.val r.val
    · obtain ⟨s',same,alive,_⟩ := step.left_residual_exists s allRight
      rcases ih s' with tailRight | ⟨r,earlier,used,dead⟩
      · rw [same] at tailRight
        exact Or.inl (.cons step tail allRight tailRight)
      · have original : ∃ z, subtermAt t r.val=some z ∧ IsRedex z := by
          rcases earlier with eq | left
          · rw [eq,same]; exact s.property
          · apply step.reflect_left s allRight
            · rw [←same]; exact left
            · exact r.property
        let old : RedexOcc t := ⟨r.val,original⟩
        have oldEarlier : old.val=s.val ∨ LeftOf old.val s.val := by
          rcases earlier with eq | left
          · exact Or.inl (eq.trans same)
          · exact Or.inr (by rw [←same]; exact left)
        have oldRight : ∀ q : RedexOcc t, q.val∈F → LeftOf old.val q.val := by
          intro q member
          rcases oldEarlier with eq | left
          · rw [eq]; exact allRight q member
          · exact left.trans (allRight q member)
        have firstResidual : step.derivation.Residual old r := (step.left_residual_iff old oldRight r).mpr rfl
        rw [same] at used
        have oldUsed := used.prepend (.single step) old (by simpa only [ParallelHistory.single_derivation] using firstResidual) (.cons step (.nil _) allRight (.nil _))
        refine Or.inr ⟨old,oldEarlier,oldUsed,?_⟩
        intro q residual
        change (step.derivation.append tail.derivation).Residual old q at residual
        rw [Derivation.residual_append] at residual
        obtain ⟨mid,first,last⟩ := residual
        have fixed : mid=r := Subtype.ext ((step.left_residual_iff old oldRight mid).mp first)
        subst mid
        exact dead q last
    · simp only [Classical.not_forall] at allRight
      obtain ⟨r,selected,notRight⟩ := allRight
      have earlier : r.val=s.val ∨ LeftOf r.val s.val := by
        rcases r.compare s with same | left | right
        · exact Or.inl (congrArg Subtype.val same)
        · exact Or.inr left
        · exact False.elim (notRight right)
      refine Or.inr ⟨r,earlier,?_,?_⟩
      · exact ⟨t,v,F,.nil t,step,tail,r,rfl,.nil t,selected,(Derivation.residual_nil r r).mpr rfl⟩
      · intro q residual
        change (step.derivation.append tail.derivation).Residual r q at residual
        rw [Derivation.residual_append] at residual
        obtain ⟨mid,first,_⟩ := residual
        exact step.no_selected_residual r selected mid first
end Lamping.Lambda

namespace Lamping.Lambda
/-- Residuals at a protected cut keep their physical occurrence path. -/
theorem Derivation.left_fixed (h : Derivation t u) (s : RedexOcc t)
    (right : ∀ p∈h.paths, LeftOf s.val p) (q : RedexOcc u) :
    h.Residual s q ↔ q.val=s.val := by
  obtain ⟨target,tracked,erase⟩ := h.tracked
  have fixed := tracked.trace_fixed_right right (fun p hp => (Marked.initial_residual [] t s p).mp hp)
  constructor
  · rintro ⟨other,history,_,trace⟩
    have otherFixed := history.trace_fixed_right right (fun p hp => (Marked.initial_residual [] t s p).mp hp)
    rw [otherFixed] at trace
    exact (Marked.initial_residual [] t s q.val).mp trace
  · intro same
    refine ⟨target,tracked,erase,?_⟩
    rw [fixed]
    exact (Marked.initial_residual [] t s q.val).mpr same

theorem RightHistory.permutation {ρ σ : ParallelHistory t u} (s : RedexOcc t)
    (right : RightHistory s.val ρ) (perm : PermEq ρ σ) : RightHistory s.val σ := by
  rcases σ.right_or_kills_left s with safe | ⟨r,before,_,dead⟩
  · exact safe
  · have paths : ∀ p∈ρ.derivation.paths, LeftOf r.val p := by
      intro p hp
      rcases before with same | left
      · rw [same]; exact right.paths_right p hp
      · exact left.trans (right.paths_right p hp)
    obtain ⟨q,_,alive⟩ := ρ.derivation.left_survives r paths
    exact False.elim (dead q ((perm.residual r q).mp alive))

theorem ParallelHistory.right_of_no_used (ρ : ParallelHistory t u) (s : RedexOcc t)
    (unused : ∀ r : RedexOcc t, r.val=s.val ∨ LeftOf r.val s.val → ¬UsedSource ρ r) :
    RightHistory s.val ρ := by
  rcases ρ.right_or_kills_left s with safe | ⟨r,before,used,_⟩
  · exact safe
  · exact False.elim (unused r before used.used)

theorem RightHistory.append_left {ρ : ParallelHistory t u} {σ : ParallelHistory u v}
    (h : RightHistory cut (ρ.append σ)) : RightHistory cut ρ := by
  induction ρ with
  | nil => exact .nil _
  | cons first tail ih =>
    cases h with
    | cons _ _ right rest => exact .cons first _ right (ih rest)

theorem RightHistory.append_right {ρ : ParallelHistory t u} {σ : ParallelHistory u v}
    (h : RightHistory cut (ρ.append σ)) : RightHistory cut σ := by
  induction ρ with
  | nil => exact h
  | cons first tail ih => cases h with | cons _ _ _ rest => exact ih rest

theorem RightHistory.not_used_self {ρ : ParallelHistory t u} (s : RedexOcc t)
    (right : RightHistory s.val ρ) : ¬UsedSource ρ s := by
  rintro ⟨v,w,F,pre,step,suffix,q,eq,selected,residual⟩
  rw [eq] at right
  have prefixRight := right.append_left
  have fixed := (pre.derivation.left_fixed s prefixRight.paths_right q).mp residual
  have rest := right.append_right
  cases rest with
  | cons _ _ selectedRight _ =>
    have impossible := selectedRight q selected
    rw [fixed] at impossible
    exact LeftOf.irrefl _ impossible

/-- An actual right-cut invariant supplies the source no-return clause for
all decompositions, independently of a proposed standard representative. -/
theorem DoesNotReturnLeft.of_right {ρ : ParallelHistory t u} (r : RedexOcc t)
    (right : ∀ s : RedexOcc t, LeftOf s.val r.val → RightHistory s.val ρ) :
    DoesNotReturnLeft r ρ := by
  intro s before v w F pre step suffix eq q lo residual
  have whole := right s before
  rw [eq] at whole
  have fixed := (pre.derivation.left_fixed s whole.append_left.paths_right q).mp residual
  have rest := whole.append_right
  cases rest with
  | cons _ _ selectedRight _ =>
    have impossible := selectedRight q lo.1
    rw [fixed] at impossible
    exact LeftOf.irrefl _ impossible
end Lamping.Lambda

