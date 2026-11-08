import Lamping.Lambda.FamilyProjectionEvents
import Lamping.Lambda.StandardizationGeneral
import Lamping.Lambda.RightHistoryProjection
namespace Lamping.Lambda

theorem FamilyUsedAt.used_source {ρ : ParallelHistory t u} (pre : ParallelHistory m t)
    (used : UsedSource ρ r) : FamilyUsedAt pre ρ ⟨t,pre,r⟩ := by
  obtain ⟨v,w,F,before,step,suffix,q,eq,selected,residual⟩ := used
  rw [eq]
  apply (FamilyUsedAt.append_iff pre before (.cons step suffix) _).mpr
  exact .inr (.head selected (.symm (.copy ⟨before,.refl _,residual⟩)))

/-- Events in the actual bottom of a tile row are transported Copy events
of its top. Arbitrary invalid names in either initial selection are allowed. -/
theorem StepProjection.used_bottom {step : ParallelStep F t u}
    {σ : ParallelHistory t v} {σ' : ParallelHistory u w} {last : ParallelStep G v w}
    (row : StepProjection step σ σ' last) (pre : ParallelHistory m t)
    (used : FamilyUsedAt (pre.append (.single step)) σ' a) : FamilyUsedAt pre σ a := by
  induction row with
  | nil => cases used
  | cons sq tail ih =>
    cases used with
    | head selected family =>
      obtain ⟨p,hp,trace⟩ := (Marked.mem_setResidualPositions _ _ _).mp selected
      let r : RedexOcc _ := ⟨p,sq.first.trace_source_valid trace⟩
      have copy : Copy ⟨_,pre,r⟩ ⟨_,pre.append (.single sq.first),_⟩ :=
        ⟨.single sq.first,.refl _,by simpa only [ParallelHistory.single_derivation] using
          (sq.first.residual_iff _ _).mpr trace⟩
      exact .head hp (.trans (.copy copy) family)
    | tail rest =>
      have perm : PermEq ((pre.append (.single sq.second)).append (.single sq.afterSecond))
          ((pre.append (.single sq.first)).append (.single sq.afterFirst)) := by
        simpa only [ParallelHistory.append_assoc] using
          PermEq.prepend pre (PermEq.moves sq).symm
      exact .tail (ih (pre.append (.single sq.second)) (rest.prefix_permutation perm.symm))

theorem FamilyUsedAt.selected_factor {step : ParallelStep F t u} (pre : ParallelHistory m t)
    (head : BetaAt t p v) (selected : p∈F)
    (rest : ParallelStep ((singleContraction head).residualSet F) v u)
    (used : FamilyUsedAt pre ((ParallelHistory.single (singleContraction head)).append (.single rest)) a) :
    FamilyUsedAt pre (.single step) a := by
  cases used with
  | @head _ _ _ _ _ _ _ _ r hr family =>
    have eq : r.val=p := List.mem_singleton.mp hr
    exact .head (eq ▸ selected) family
  | tail later =>
    cases later with
    | @head _ _ _ _ _ _ _ _ s hs family =>
      obtain ⟨p,hp,trace⟩ := (Marked.mem_setResidualPositions _ _ _).mp hs
      let r : RedexOcc _ := ⟨p,(singleContraction head).trace_source_valid trace⟩
      have copy : Copy ⟨t,pre,r⟩ ⟨v,pre.append (.single (singleContraction head)),s⟩ :=
        ⟨.single (singleContraction head),.refl _,by simpa only [ParallelHistory.single_derivation] using
          ((singleContraction head).residual_iff r s).mpr trace⟩
      exact .head hp (.trans (.copy copy) family)
    | tail impossible => cases impossible

theorem FamilyUsedAt.support_append {ρ σ : ParallelHistory t u} (pre : ParallelHistory m t)
    (support : ∀ a, FamilyUsedAt pre σ a → FamilyUsedAt pre ρ a) (perm : PermEq ρ σ)
    (suffix : ParallelHistory u v) (used : FamilyUsedAt pre (σ.append suffix) a) :
    FamilyUsedAt pre (ρ.append suffix) a := by
  rcases (FamilyUsedAt.append_iff pre σ suffix a).mp used with first | last
  · exact (FamilyUsedAt.append_iff pre ρ suffix a).mpr (.inl (support a first))
  · exact (FamilyUsedAt.append_iff pre ρ suffix a).mpr
      (.inr (last.prefix_permutation (PermEq.prepend pre perm.symm)))

theorem FamilyUsedAt.pull_factor_support {ρ : ParallelHistory t u}
    (pre : ParallelHistory m t) (s : RedexOcc t) (source : BetaAt t s.val z)
    (later : BetaAt u s.val v) (step : ParallelStep G u w) (selected : s.val∈G)
    (survives : ρ.derivation.Residual s ⟨s.val,later.redex⟩)
    (rest : ParallelStep ((singleContraction later).residualSet G) v w)
    {rowHistory : ParallelHistory z v} {last : ParallelStep K u v}
    (row : StepProjection (singleContraction source) ρ rowHistory last)
    (lastPerm : PermEq (.single last) (.single (singleContraction later)))
    (used : FamilyUsedAt pre
      ((ParallelHistory.single (singleContraction source)).append (rowHistory.append (.single rest))) a) :
    FamilyUsedAt pre (ρ.append (.single step)) a := by
  have exchanged : PermEq ((pre.append (.single (singleContraction source))).append rowHistory)
      ((pre.append ρ).append (.single (singleContraction later))) := by
    have move := row.permutation.trans (PermEq.prepend ρ lastPerm)
    simpa only [ParallelHistory.append_assoc] using PermEq.prepend pre move
  cases used with
  | @head _ _ _ _ _ _ _ _ r hr family =>
    have same : r=s := Subtype.ext (List.mem_singleton.mp hr)
    subst r
    have oldUsed : UsedSource (ρ.append (.single step)) s :=
      ⟨u,w,G,ρ,step,.nil _,⟨s.val,later.redex⟩,rfl,selected,survives⟩
    exact (FamilyUsedAt.used_source pre oldUsed).family family
  | tail restUsed =>
    rcases (FamilyUsedAt.append_iff (pre.append (.single (singleContraction source))) rowHistory (.single rest) a).mp restUsed with middle | final
    · exact (FamilyUsedAt.append_iff pre ρ (.single step) a).mpr (.inl (row.used_bottom pre middle))
    · have changed := final.prefix_permutation exchanged
      have factored : FamilyUsedAt (pre.append ρ)
          ((ParallelHistory.single (singleContraction later)).append (.single rest)) a := .tail changed
      exact (FamilyUsedAt.append_iff pre ρ (.single step) a).mpr
        (.inr (factored.selected_factor (pre.append ρ) later selected rest))

/-- The actual pull-left construction additionally retains its family-event
support. This is directional support, not invariance under arbitrary PermEq. -/
theorem RightHistory.pull_selected_supported {ρ : ParallelHistory t u}
    (right : RightHistory cut ρ) (s : RedexOcc t) (atCut : s.val=cut)
    (step : ParallelStep G u v) (selected : cut∈G) (suffix : ParallelHistory v w)
    (pre : ParallelHistory m t) :
    ∃ (z : Term) (source : BetaAt t cut z) (tail : ParallelHistory z w),
      PermEq (ρ.append (.cons step suffix)) ((ParallelHistory.single (singleContraction source)).append tail) ∧
      tail.length=(ρ.append (.cons step suffix)).length ∧
      HistoryCost.ListLt tail.costs (ρ.append (.cons step suffix)).costs ∧
      ∀ a, FamilyUsedAt pre ((ParallelHistory.single (singleContraction source)).append tail) a →
        FamilyUsedAt pre (ρ.append (.cons step suffix)) a := by
  cases atCut
  obtain ⟨q,qAt,alive⟩ := ρ.derivation.left_survives s right.paths_right
  let chosen : RedexOcc u := ⟨s.val,by rw [←qAt]; exact q.property⟩
  have survives : ρ.derivation.Residual s chosen := by
    have eq : q=chosen := Subtype.ext qAt
    exact eq ▸ alive
  obtain ⟨mid,later,rest,factor⟩ := step.selected_factor chosen selected
  obtain ⟨z,source,rowHistory,K,last,row,length,_,lastPerm⟩ := right.pull_projection s rfl later
  have exchange := row.permutation.trans (PermEq.prepend ρ lastPerm)
  have blockPerm : PermEq (ρ.append (.single step))
      ((ParallelHistory.single (singleContraction source)).append (rowHistory.append (.single rest))) := by
    have first := PermEq.prepend ρ factor
    have second := exchange.symm.append (.single rest)
    simp only [ParallelHistory.append_assoc] at first second
    exact first.trans second
  have support : ∀ a, FamilyUsedAt pre
      ((ParallelHistory.single (singleContraction source)).append (rowHistory.append (.single rest))) a →
        FamilyUsedAt pre (ρ.append (.single step)) a := by
    intro a used
    exact FamilyUsedAt.pull_factor_support pre s source later step selected survives rest row lastPerm used
  refine ⟨z,source,(rowHistory.append (.single rest)).append suffix,?_,?_,?_,?_⟩
  · simpa only [ParallelHistory.append_assoc,ParallelHistory.single,ParallelHistory.append] using blockPerm.append suffix
  · simp only [ParallelHistory.length_append,ParallelHistory.single,ParallelHistory.length,length]
    omega
  · rw [ParallelHistory.costs_append,ParallelHistory.costs_append,ParallelHistory.costs_append]
    simp only [ParallelHistory.single,ParallelHistory.costs,List.nil_append,List.append_assoc]
    change HistoryCost.ListLt
      (suffix.costs ++ ([Marked.weight (fun _ => 1) (Marked.mark ((singleContraction later).residualSet G) mid)] ++ rowHistory.costs))
      (suffix.costs ++ ([Marked.weight (fun _ => 1) (Marked.mark G u)] ++ ρ.costs))
    exact HistoryCost.ListLt.prefix (.head _ _ (later.selected_residual_weight_lt selected (fun _ => 1))) _
  · intro a used
    have event : FamilyUsedAt pre
        ((((ParallelHistory.single (singleContraction source)).append (rowHistory.append (.single rest)))).append suffix) a := by
      simpa only [ParallelHistory.append_assoc] using used
    have result := FamilyUsedAt.support_append pre support blockPerm suffix event
    simpa only [ParallelHistory.append_assoc,ParallelHistory.single,ParallelHistory.append] using result

end Lamping.Lambda
