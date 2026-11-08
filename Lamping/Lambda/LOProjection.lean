import Lamping.Lambda.LORightPreservation
import Lamping.Lambda.NeededProjectionEmpty
import Lamping.Lambda.AtomicProjection
import Lamping.Lambda.TraceNoDup

namespace Lamping.Lambda

/-- Literal old-name image of a global LO singleton through an arbitrary
complete step. Invalid or repeated names in F add no validity hypothesis. -/
theorem ParallelStep.lo_residual_singleton_cases {t u : Term} {F : List Path}
    (h : ParallelStep F t u) {q : Path} (hit : loRedex t=some q) :
    (q ∈ F ∧ h.residualSet [q]=[]) ∨
      (q ∉ F ∧ h.residualSet [q]=[q] ∧ loRedex u=some q) := by
  classical
  by_cases selected : q ∈ F
  · refine Or.inl ⟨selected,?_⟩
    have noMember : ∀ x, x ∉ h.residualSet [q] := by
      intro x member
      obtain ⟨origin,originMember,trace⟩ :=
        (Marked.mem_setResidualPositions [q] h.markedTarget x).mp member
      have same : origin=q := List.mem_singleton.mp originMember
      have full : x ∈ Marked.setResidualPositions F h.markedTarget :=
        (Marked.mem_setResidualPositions F h.markedTarget x).mpr
          ⟨q,selected,by simpa only [same] using trace⟩
      rw [h.complete.2] at full
      exact List.not_mem_nil full
    cases image : h.residualSet [q] with
    | nil => rfl
    | cons x xs =>
      exact False.elim (noMember x (by rw [image]; exact List.mem_cons_self))
  · let source : RedexOcc t := ⟨q,loRedex_sound hit⟩
    have allRight : ∀ r : RedexOcc t, r.val ∈ F → LeftOf q r.val := by
      intro r member
      rcases source.compare r with same | later | earlier
      · have atSource : q=r.val := congrArg Subtype.val same
        have sourceMember : q ∈ F := by
          rw [atSource]
          exact member
        exact False.elim (selected sourceMember)
      · exact later
      · exact False.elim (loRedex_leftmost hit r earlier)
    have pathsRight : ∀ p ∈ h.paths, LeftOf q p := by
      apply ((Marked.completeOld_iff F t).mp h.complete).1.right_paths
      intro p hp
      obtain ⟨member,valid⟩ := (Marked.active_mark F t p).mp hp
      exact allRight ⟨p,(mem_redexPositions t p).mp valid⟩ member
    have fixed := h.tracked.trace_fixed_right pathsRight
      (fun p hp => (Marked.initial_residual [] t source p).mp hp)
    have initial := Marked.initial_trace_singleton [] t source
    have image : h.residualSet [q]=[q] := by
      simp only [ParallelStep.residualSet,Marked.setResidualPositions,
        List.flatMap_cons,List.flatMap_nil,List.append_nil]
      rw [←Marked.passive_trace q h.markedTarget,fixed,initial]
    exact Or.inr ⟨selected,image,h.derivation.loRedex_preserved_of_right hit pathsRight⟩

/-- The actual projected boundaries: literal empty selections or genuine
singleton contractions selected by the global computed LO at that source. -/
inductive LOOrEmptyHistory : {t u : Term} → ParallelHistory t u → Prop where
  | nil (t : Term) : LOOrEmptyHistory (.nil t)
  | empty {t v u : Term} (step : ParallelStep [] t v)
      {tail : ParallelHistory v u} : LOOrEmptyHistory tail →
      LOOrEmptyHistory (.cons step tail)
  | cons {t v u : Term} {p : Path} (head : BetaAt t p v)
      {tail : ParallelHistory v u} : loRedex t=some p → LOOrEmptyHistory tail →
      LOOrEmptyHistory (.cons (singleContraction head) tail)

private theorem actual_lo_projection_uncons
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

private theorem lo_or_empty_empty {F : List Path} {t v u : Term}
    (step : ParallelStep F t v) (empty : F=[]) {tail : ParallelHistory v u}
    (rest : LOOrEmptyHistory tail) : LOOrEmptyHistory (.cons step tail) := by
  subst F
  exact .empty step rest

private theorem lo_or_empty_singleton {F : List Path} {t v u : Term} {q : Path}
    (step : ParallelStep F t v) (single : F=[q]) (hit : loRedex t=some q)
    {tail : ParallelHistory v u} (rest : LOOrEmptyHistory tail) :
    LOOrEmptyHistory (.cons step tail) := by
  subst F
  obtain ⟨head,same⟩ := step.eq_single_contraction ⟨q,loRedex_sound hit⟩ rfl
  rw [same]
  exact .cons head hit rest

/-- Preserve the given tile schedules. Target atomicity is constructed
locally where the actual transported selection is the literal singleton. -/
theorem StepProjection.lo_or_empty {t u v w : Term} {F G : List Path}
    {h : ParallelStep F t u} {rho : ParallelHistory t v}
    {tau : ParallelHistory u w} {last : ParallelStep G v w}
    (row : StepProjection h rho tau last) (lo : LOHistory rho) :
    LOOrEmptyHistory tau := by
  have main {t v : Term} {rho : ParallelHistory t v} (lo : LOHistory rho) :
      ∀ {F : List Path} {u w : Term} {G : List Path}
        {h : ParallelStep F t u} {tau : ParallelHistory u w}
        {last : ParallelStep G v w}, StepProjection h rho tau last →
        LOOrEmptyHistory tau := by
    induction lo with
    | nil t =>
      intro F u w G h tau last row
      cases row
      exact .nil _
    | @cons t x v p tail head hit _rest ih =>
      intro F u w G h tau last row
      obtain ⟨mid,bottomTail,square,firstEq,secondEq,fullEq,tailRow⟩ :=
        actual_lo_projection_uncons row
      rcases square with ⟨firstVertical,firstTop,projected,afterTop⟩
      simp only at firstEq secondEq fullEq tailRow
      subst firstVertical
      subst firstTop
      have rest : LOOrEmptyHistory bottomTail := ih tailRow
      rw [fullEq]
      rcases h.lo_residual_singleton_cases hit with ⟨_selected,empty⟩ |
          ⟨_unselected,single,targetHit⟩
      · exact lo_or_empty_empty projected empty rest
      · exact lo_or_empty_singleton projected single targetHit rest
  exact main lo row

private inductive HasEmpty : {t u : Term} → ParallelHistory t u → Prop where
  | head {t v u : Term} {step : ParallelStep [] t v} {tail : ParallelHistory v u} :
      HasEmpty (.cons step tail)
  | tail {t v u : Term} {F : List Path} {step : ParallelStep F t v}
      {rest : ParallelHistory v u} : HasEmpty rest → HasEmpty (.cons step rest)

private theorem has_empty_append {t a b u : Term} (pre : ParallelHistory t a)
    (step : ParallelStep [] a b) (tail : ParallelHistory b u) :
    HasEmpty (pre.append (.cons step tail)) := by
  induction pre with
  | nil => exact .head
  | cons first rest ih => exact .tail (ih step)

private theorem prune_lo_with_length {t u : Term} {raw : ParallelHistory t u}
    (mixed : LOOrEmptyHistory raw) :
    ∃ observed : ParallelHistory t u,
      LOHistory observed ∧ ParallelHistory.Observable observed ∧
      raw.derivation=observed.derivation ∧ PermEq raw observed ∧
      observed.length ≤ raw.length ∧ (HasEmpty raw → observed.length < raw.length) := by
  induction mixed with
  | nil t =>
    refine ⟨.nil t,.nil t,.nil t,rfl,.refl _,Nat.le_refl _,?_⟩
    intro empty
    cases empty
  | @empty t v u step tail _rest ih =>
    have endpoint : v=t := step.endpoint (ParallelStep.empty t)
    subst v
    obtain ⟨observed,lo,positive,same,permutation,bound,_strict⟩ := ih
    refine ⟨observed,lo,positive,?_,?_,?_,?_⟩
    · apply Derivation.ext
      change step.paths++tail.derivation.paths=observed.derivation.paths
      rw [step.empty_paths,List.nil_append,same]
    · exact .trans (.comp (.empty step) (.refl tail)) permutation
    · change observed.length ≤ 1 + tail.length
      omega
    · intro _empty
      change observed.length < 1 + tail.length
      omega
  | @cons t v u p head tail hit _rest ih =>
    obtain ⟨observed,lo,positive,same,permutation,bound,strict⟩ := ih
    refine ⟨.cons (singleContraction head) observed,.cons head hit lo,
      .cons (by simp) positive,?_,?_,?_,?_⟩
    · change (singleContraction head).derivation.append tail.derivation =
        (singleContraction head).derivation.append observed.derivation
      rw [same]
    · exact .comp (.refl (.single (singleContraction head))) permutation
    · change 1 + observed.length ≤ 1 + tail.length
      omega
    · intro empty
      cases empty with
      | tail inside =>
        have shorter := strict inside
        change 1 + observed.length < 1 + tail.length
        omega

/-- Delete actual empty constructors, retaining each actual LO contraction;
no inference from arbitrary Observable or PermEq to LO is used. -/
theorem LOOrEmptyHistory.exists_lo {t u : Term} {raw : ParallelHistory t u}
    (mixed : LOOrEmptyHistory raw) :
    ∃ observed : ParallelHistory t u,
      LOHistory observed ∧ ParallelHistory.Observable observed ∧
      raw.derivation=observed.derivation ∧ PermEq raw observed ∧
      observed.length ≤ raw.length ∧
      ((∃ (a b : Term) (pre : ParallelHistory t a)
          (step : ParallelStep [] a b) (tail : ParallelHistory b u),
          raw=pre.append (.cons step tail)) → observed.length < raw.length) := by
  obtain ⟨observed,lo,positive,same,permutation,bound,strict⟩ := prune_lo_with_length mixed
  refine ⟨observed,lo,positive,same,permutation,bound,?_⟩
  rintro ⟨a,b,pre,step,tail,eq⟩
  apply strict
  rw [eq]
  exact has_empty_append pre step tail

private theorem lo_atomic {t u : Term} {rho : ParallelHistory t u}
    (lo : LOHistory rho) : Atomic rho := by
  induction lo with
  | nil t => exact .nil t
  | cons head _hit _rest ih => exact .cons head ih

/-- Any selected needed redex removes at least one boundary from an actual
finite LO normalization when the supplied projection is pruned literally. -/
theorem StepProjection.exists_shorter_lo_of_needed_selected
    {t u v w : Term} {F G : List Path}
    {h : ParallelStep F t u} {rho : ParallelHistory t v}
    {tau : ParallelHistory u w} {last : ParallelStep G v w}
    (row : StepProjection h rho tau last) (sourceLO : LOHistory rho)
    (normal : BetaNF v) (r : RedexOcc t) (selected : r.val ∈ F) (needed : Needed r) :
    ∃ observed : ParallelHistory u w,
      LOHistory observed ∧ BetaNF w ∧ tau.derivation=observed.derivation ∧
      PermEq tau observed ∧ observed.length < rho.length := by
  have used : UsedSource rho r := needed rho normal
  have empty := row.exists_empty_boundary_of_used_selected (lo_atomic sourceLO) r selected used
  obtain ⟨observed,lo,_positive,same,permutation,_bound,strict⟩ :=
    (row.lo_or_empty sourceLO).exists_lo
  have shorter := strict empty
  rw [row.length] at shorter
  have endpoint : w=v := last.no_actual_endpoint (fun s _member => normal s)
  have targetNormal : BetaNF w := by
    cases endpoint
    exact normal
  exact ⟨observed,lo,targetNormal,same,permutation,shorter⟩

#print axioms ParallelStep.lo_residual_singleton_cases
#print axioms LOOrEmptyHistory
#print axioms StepProjection.lo_or_empty
#print axioms LOOrEmptyHistory.exists_lo
#print axioms StepProjection.exists_shorter_lo_of_needed_selected

end Lamping.Lambda
