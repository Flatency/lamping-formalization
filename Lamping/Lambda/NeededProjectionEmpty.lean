import Lamping.Lambda.ProjectionUsedSources
import Lamping.Lambda.ObservableHistory

namespace Lamping.Lambda

private theorem actual_projection_uncons
    {first : ParallelStep F t u} {top : ParallelStep H t v}
    {rest : ParallelHistory v x} {full : ParallelHistory u z}
    {last : ParallelStep G x z}
    (row : StepProjection first (.cons top rest) full last) :
    ∃ (mid : Term) (tail : ParallelHistory mid z)
      (sq : ParallelMovesSquare F H t u v mid),
      sq.first=first ∧ sq.second=top ∧ full=.cons sq.afterFirst tail ∧
      StepProjection sq.afterSecond rest tail last := by
  cases row with
  | cons sq tail => exact ⟨_,_,sq,rfl,rfl,rfl,tail⟩

private theorem empty_boundary_index {F : List Path} {a b u w : Term}
    (step : ParallelStep F a b) (empty : F=[])
    (pre : ParallelHistory u a) (tail : ParallelHistory b w) :
    ∃ step0 : ParallelStep [] a b,
      pre.append (.cons step tail) = pre.append (.cons step0 tail) := by
  subst F
  exact ⟨step,rfl⟩

/-- A selected old source redex that is actually used by an ordinary history
produces a literal empty boundary in its given genuine projection. -/
theorem StepProjection.exists_empty_boundary_of_used_selected
    {t u v w : Term} {F G : List Path}
    {h : ParallelStep F t u} {rho : ParallelHistory t v}
    {tau : ParallelHistory u w} {last : ParallelStep G v w}
    (row : StepProjection h rho tau last) (sourceAtomic : Atomic rho)
    (r : RedexOcc t) (selected : r.val ∈ F) (used : UsedSource rho r) :
    ∃ (a b : Term) (pre : ParallelHistory u a)
      (step : ParallelStep [] a b) (tail : ParallelHistory b w),
      tau = pre.append (.cons step tail) := by
  obtain ⟨a,b,H,pre,step,suffix,q,eq,member,residual⟩ := used
  have whole : Atomic (pre.append (.cons step suffix)) := by
    rw [←eq]
    exact sourceAtomic
  have rest := whole.split_append.2
  cases rest with
  | @cons atSource headPath atTarget finalTarget actualSuffix head _restAtomic =>
    have qSame : q = ⟨headPath,head.redex⟩ :=
      Subtype.ext (List.mem_singleton.mp member)
    subst q
    rw [eq] at row
    obtain ⟨mid,K,bottomPre,mapped,atPre,preRow,restRow,fullEq⟩ :=
      row.split_append pre (.cons (singleContraction head) suffix)
    obtain ⟨next,bottomTail,square,firstEq,secondEq,mappedEq,_tailRow⟩ :=
      actual_projection_uncons restRow
    rcases square with ⟨firstVertical,firstTop,projected,afterTop⟩
    simp only at firstEq secondEq mappedEq
    subst firstVertical
    subst firstTop
    have noResidual (z : RedexOcc mid) :
        ¬atPre.derivation.Residual ⟨headPath,head.redex⟩ z := by
      intro alive
      have topComposite : (pre.append (.single atPre)).derivation.Residual r z := by
        rw [ParallelHistory.derivation_append,ParallelHistory.single_derivation,
          Derivation.residual_append]
        exact ⟨⟨headPath,head.redex⟩,residual,alive⟩
      have bottomComposite := (preRow.permutation.residual r z).mpr topComposite
      rw [ParallelHistory.derivation_append,ParallelHistory.single_derivation,
        Derivation.residual_append] at bottomComposite
      obtain ⟨old,first,_last⟩ := bottomComposite
      exact h.no_selected_residual r selected old first
    have noMember : ∀ x, x ∉ atPre.residualSet [headPath] := by
      intro x member
      let target : RedexOcc mid := ⟨x,atPre.residualSet_valid x member⟩
      have valid : ∀ p ∈ [headPath], ∃ z, subtermAt a p=some z ∧ IsRedex z := by
        intro p hp
        rcases List.mem_singleton.mp hp with rfl
        exact head.redex
      obtain ⟨origin,originMember,alive⟩ :=
        (atPre.mem_residualSet_iff valid target).mp member
      have same : origin = ⟨headPath,head.redex⟩ :=
        Subtype.ext (List.mem_singleton.mp originMember)
      rw [same] at alive
      exact noResidual target alive
    have empty : atPre.residualSet [headPath] = [] := by
      cases labels : atPre.residualSet [headPath] with
      | nil => rfl
      | cons x xs =>
        exact False.elim (noMember x (by rw [labels]; exact List.mem_cons_self))
    obtain ⟨step0,same⟩ := empty_boundary_index projected empty bottomPre bottomTail
    refine ⟨mid,next,bottomPre,step0,bottomTail,?_⟩
    calc
      tau = bottomPre.append mapped := fullEq
      _ = bottomPre.append (.cons projected bottomTail) := congrArg (bottomPre.append ·) mappedEq
      _ = bottomPre.append (.cons step0 bottomTail) := same

private inductive ContainsEmpty : {t u : Term} → ParallelHistory t u → Prop where
  | head {t v u : Term} {step : ParallelStep [] t v}
      {tail : ParallelHistory v u} : ContainsEmpty (.cons step tail)
  | tail {t v u : Term} {F : List Path} {step : ParallelStep F t v}
      {rest : ParallelHistory v u} : ContainsEmpty rest → ContainsEmpty (.cons step rest)

private theorem contains_empty_append {t a b u : Term}
    (pre : ParallelHistory t a) (step : ParallelStep [] a b)
    (tail : ParallelHistory b u) : ContainsEmpty (pre.append (.cons step tail)) := by
  induction pre with
  | nil => exact .head
  | cons first rest ih => exact .tail (ih step)

private theorem prune_with_length {t u : Term} (raw : ParallelHistory t u) :
    ∃ observed : ParallelHistory t u,
      ParallelHistory.Observable observed ∧ raw.derivation=observed.derivation ∧
      PermEq raw observed ∧ observed.length ≤ raw.length ∧
      (ContainsEmpty raw → observed.length < raw.length) := by
  induction raw with
  | nil t =>
    refine ⟨.nil t,.nil t,rfl,.refl _,Nat.le_refl _,?_⟩
    intro empty
    cases empty
  | @cons t middle target F step tail ih =>
    by_cases empty : F=[]
    · subst F
      have endpoint : middle=t := step.endpoint (ParallelStep.empty t)
      subst middle
      obtain ⟨observed,positive,same,permutation,bound,_strict⟩ := ih
      refine ⟨observed,positive,?_,?_,?_,?_⟩
      · apply Derivation.ext
        change step.paths++tail.derivation.paths=observed.derivation.paths
        rw [step.empty_paths,List.nil_append,same]
      · exact .trans (.comp (.empty step) (.refl tail)) permutation
      · change observed.length ≤ 1 + tail.length
        omega
      · intro _empty
        change observed.length < 1 + tail.length
        omega
    · obtain ⟨observed,positive,same,permutation,bound,strict⟩ := ih
      refine ⟨.cons step observed,.cons empty positive,?_,?_,?_,?_⟩
      · change step.derivation.append tail.derivation=step.derivation.append observed.derivation
        rw [same]
      · exact .comp (.refl (.single step)) permutation
      · change 1 + observed.length ≤ 1 + tail.length
        omega
      · intro hasEmpty
        cases hasEmpty with
        | head => exact False.elim (empty rfl)
        | tail inside =>
          have shorter := strict inside
          change 1 + observed.length < 1 + tail.length
          omega

/-- Delete only literal empty-selection events, preserving the actual beta
derivation and genuine permutation, with strict boundary loss when one occurs. -/
theorem ParallelHistory.exists_observable_length {t u : Term}
    (raw : ParallelHistory t u) :
    ∃ observed : ParallelHistory t u,
      ParallelHistory.Observable observed ∧ raw.derivation=observed.derivation ∧
      PermEq raw observed ∧ observed.length ≤ raw.length ∧
      ((∃ (a b : Term) (pre : ParallelHistory t a)
          (step : ParallelStep [] a b) (tail : ParallelHistory b u),
          raw=pre.append (.cons step tail)) → observed.length < raw.length) := by
  obtain ⟨observed,positive,same,permutation,bound,strict⟩ := prune_with_length raw
  refine ⟨observed,positive,same,permutation,bound,?_⟩
  rintro ⟨a,b,pre,step,tail,eq⟩
  apply strict
  rw [eq]
  exact contains_empty_append pre step tail

#print axioms StepProjection.exists_empty_boundary_of_used_selected
#print axioms ParallelHistory.exists_observable_length

end Lamping.Lambda
