import Lamping.Lambda.StandardizationFactorization
import Lamping.Lambda.CreationDisjointResidual
import Lamping.Lambda.NoTagTransport
import Lamping.Lambda.TraceNoDup
namespace Lamping.Lambda

theorem DisjointPositions.cons (h : DisjointPositions p q) (s : Step) :
    DisjointPositions (s::p) (s::q) := by
  constructor
  · rintro ⟨r,eq⟩; exact h.1 ⟨r,(List.cons.inj eq).2⟩
  · rintro ⟨r,eq⟩; exact h.2 ⟨r,(List.cons.inj eq).2⟩
theorem DisjointPositions.symm (h : DisjointPositions p q) : DisjointPositions q p := ⟨h.2,h.1⟩
theorem DisjointPositions.nil_left : ¬DisjointPositions [] q := fun h => h.1 ⟨q,rfl⟩
theorem DisjointPositions.nil_right : ¬DisjointPositions p [] := fun h => h.2 ⟨p,rfl⟩
end Lamping.Lambda
namespace Lamping.Lambda.Marked
private theorem active_child_lam (apart : ∀ q∈activePositions (.lam b), DisjointPositions (.body::cut) q) :
    ∀ q∈activePositions b, DisjointPositions cut q := by
  intro q hq
  exact (apart (.body::q) (List.mem_map.mpr ⟨q,hq,rfl⟩)).child
private theorem active_child_fn (apart : ∀ q∈activePositions (.app l f a), DisjointPositions (.fn::cut) q) :
    ∀ q∈activePositions f, DisjointPositions cut q := by
  intro q hq
  exact (apart (.fn::q) (List.mem_append_left _ (List.mem_map.mpr ⟨q,hq,rfl⟩))).child
private theorem active_child_arg (apart : ∀ q∈activePositions (.app l f a), DisjointPositions (.arg::cut) q) :
    ∀ q∈activePositions a, DisjointPositions cut q := by
  intro q hq
  exact (apart (.arg::q) (List.mem_append_right _ (List.mem_map.mpr ⟨q,hq,rfl⟩))).child

/-- A real active contraction cannot move other active residuals into a
protected, disjoint subtree. This is a source active-set invariant. -/
theorem StepAt.apart_cut (h : StepAt p t u)
    (apart : ∀ q∈activePositions t, DisjointPositions cut q) :
    ∀ q∈activePositions u, DisjointPositions cut q := by
  induction h generalizing cut with
  | root l b a => exact False.elim (DisjointPositions.nil_right (apart [] (by simp [activePositions])))
  | @lam p b b' h ih =>
    cases cut with
    | nil => exact False.elim (DisjointPositions.nil_left (apart (.body::p) (by simp [activePositions,h.active])))
    | cons s cut =>
      intro q hq
      obtain ⟨q,inner,rfl⟩ := List.mem_map.mp hq
      by_cases same : s=.body
      · subst s; exact (ih (active_child_lam apart) q inner).cons _
      · exact DisjointPositions.head_ne same
  | @appL p f f' l a h ih =>
    cases cut with
    | nil => exact False.elim (DisjointPositions.nil_left (apart (.fn::p) (by simp [activePositions,h.active])))
    | cons s cut =>
      intro q hq
      rcases List.mem_append.mp hq with hf | ha
      · obtain ⟨q,inner,rfl⟩ := List.mem_map.mp hf
        by_cases same : s=.fn
        · subst s; exact (ih (active_child_fn apart) q inner).cons _
        · exact DisjointPositions.head_ne same
      · exact apart q (List.mem_append_right _ ha)
  | @appR p a a' l f h ih =>
    cases cut with
    | nil => exact False.elim (DisjointPositions.nil_left (apart (.arg::p) (by simp [activePositions,h.active])))
    | cons s cut =>
      intro q hq
      rcases List.mem_append.mp hq with hf | ha
      · exact apart q (List.mem_append_left _ hf)
      · obtain ⟨q,inner,rfl⟩ := List.mem_map.mp ha
        by_cases same : s=.arg
        · subst s; exact (ih (active_child_arg apart) q inner).cons _
        · exact DisjointPositions.head_ne same
  | redL h ih => exact False.elim (DisjointPositions.nil_right (apart [] (by simp [activePositions])))
  | redR h ih => exact False.elim (DisjointPositions.nil_right (apart [] (by simp [activePositions])))

theorem RelativeHistory.apart_paths (h : RelativeHistory ps t u)
    (apart : ∀ q∈activePositions t, DisjointPositions cut q) :
    ∀ q∈ps, DisjointPositions cut q := by
  induction h with
  | nil => simp
  | cons first tail ih =>
    intro q hq
    rcases List.mem_cons.mp hq with same | later
    · subst q; exact apart _ first.active
    · exact ih (first.apart_cut apart) q later
end Lamping.Lambda.Marked
namespace Lamping.Lambda
/-- Actual complete-development schedules inherit disjointness of source
actual selections, without validity or schedule assumptions on F. -/
theorem ParallelStep.paths_apart (h : ParallelStep F t u)
    (apart : ∀ r : RedexOcc t, r.val∈F → DisjointPositions cut r.val) :
    ∀ q∈h.paths, DisjointPositions cut q := by
  apply ((Marked.completeOld_iff F t).mp h.complete).1.apart_paths
  intro q hq
  obtain ⟨member,valid⟩ := (Marked.active_mark F t q).mp hq
  exact apart ⟨q,(mem_redexPositions t q).mp valid⟩ member
end Lamping.Lambda

namespace Lamping.Lambda
/-- Descending within one of two disjoint subtrees preserves disjointness. -/
theorem DisjointPositions.descend_left (h : DisjointPositions p q) (tail : Path) :
    DisjointPositions (p++tail) q := by
  constructor
  · rintro ⟨r,eq⟩
    exact h.1 ⟨tail++r,by simpa only [List.append_assoc] using eq⟩
  · rintro ⟨r,eq⟩
    rcases List.prefix_or_prefix_of_prefix (show p <+: p++tail from ⟨tail,rfl⟩)
        (show q <+: p++tail from ⟨r,eq.symm⟩) with ⟨a,ha⟩ | ⟨a,ha⟩
    · exact h.1 ⟨a,ha.symm⟩
    · exact h.2 ⟨a,ha.symm⟩

/-- A genuine selected contraction inside the chosen copy leaves a complete
remaining development entirely in other disjoint copies. -/
theorem ParallelStep.selected_factor_apart (h : ParallelStep F t u) (s : RedexOcc t)
    (selected : s.val∈F) (inside : ∃ q, s.val=site++q)
    (valid : ∀ p∈F, ∃ z, subtermAt t p=some z ∧ IsRedex z)
    (scope : ∀ r : RedexOcc t, r.val∈F → r.val=s.val ∨ DisjointPositions site r.val) :
    ∃ (v : Term) (head : BetaAt t s.val v)
      (tail : ParallelStep ((singleContraction head).residualSet F) v u),
      PermEq (.single h) ((ParallelHistory.single (singleContraction head)).append (.single tail)) ∧
      ∀ p∈tail.paths, DisjointPositions site p := by
  obtain ⟨v,head,tail,perm⟩ := h.selected_factor s selected
  refine ⟨v,head,tail,perm,?_⟩
  apply tail.paths_apart
  intro q member
  obtain ⟨r,oldMember,trace⟩ := (Marked.mem_setResidualPositions F _ q.val).mp member
  let old : RedexOcc t := ⟨r,valid r oldMember⟩
  have residual : (singleContraction head).derivation.Residual old q :=
    ((singleContraction head).residual_iff old q).mpr trace
  rcases scope old oldMember with same | apart
  · have selectedOld : old.val∈[s.val] := by simp [same]
    have impossible := (Marked.mem_setResidualPositions [s.val] _ q.val).mpr
      ⟨old.val,selectedOld,((singleContraction head).residual_iff old q).mp residual⟩
    rw [(singleContraction head).complete.2] at impossible
    exact False.elim (List.not_mem_nil impossible)
  · obtain ⟨suffix,atSite⟩ := inside
    have separate : DisjointPositions s.val old.val := by
      rw [atSite]; exact apart.descend_left suffix
    have fixed := (head.disjoint_residual_iff old separate q).mp residual
    rw [←fixed]
    exact apart
end Lamping.Lambda
namespace Lamping.Lambda.Marked
/-- Actual old-name traces in a disjoint protected subtree do not move. -/
theorem History.trace_fixed_apart (h : History ps t u)
    (apart : ∀ q∈ps, DisjointPositions cut q)
    (atCut : ∀ q∈tracePositions name t, q=cut) :
    tracePositions name u=tracePositions name t := by
  induction h with
  | nil => rfl
  | @cons p t v ps u first tail ih =>
    have separate := apart p (List.mem_cons_self ..)
    have fixed := first.trace_outside (r:=name) (by
      intro suffix member
      exact separate.2 ⟨suffix,(atCut _ member).symm⟩)
    have last := ih (fun q hq => apart q (List.mem_cons_of_mem _ hq)) (by
      intro q hq; rw [fixed] at hq; exact atCut q hq)
    exact last.trans fixed
end Lamping.Lambda.Marked
namespace Lamping.Lambda
/-- A complete parallel step outside a subtree has literally the singleton
residual selection for an old redex inside the protected subtree. -/
theorem ParallelStep.apart_residualSet_singleton (h : ParallelStep F t u) (r : RedexOcc t)
    (apart : ∀ q∈h.paths, DisjointPositions r.val q) : h.residualSet [r.val]=[r.val] := by
  have fixed := h.tracked.trace_fixed_apart apart
    (fun p hp => (Marked.initial_residual [] t r p).mp hp)
  simp only [Marked.passive_trace] at fixed
  change Marked.setResidualPositions [r.val] _=_
  simp only [Marked.setResidualPositions,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rw [fixed,Marked.initial_trace_singleton]
end Lamping.Lambda
