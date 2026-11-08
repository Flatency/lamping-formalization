import Lamping.Lambda.PointedRuns
import Lamping.Lambda.DerivationProjection
namespace Lamping.Lambda

theorem Atomic.split_append {ρ : ParallelHistory t u} {σ : ParallelHistory u v}
    (ha : Atomic (ρ.append σ)) : Atomic ρ ∧ Atomic σ := by
  induction ρ with
  | nil => exact ⟨.nil _,ha⟩
  | cons h hs ih =>
    cases ha with
    | cons hb ht =>
      obtain ⟨hp,hq⟩ := ih ht
      exact ⟨.cons hb hp,hq⟩

theorem Atomic.single_step {h : ParallelStep F t u}
    (ha : Atomic (.single h)) : ∃ p, ∃ _hb : BetaAt t p u, h.paths = [p] := by
  cases ha with
  | cons hb hs => cases hs; exact ⟨_,hb,rfl⟩

/-- Split a genuine projection at its last input tile. This retains the
actual projected prefix and actual final development, including its chosen
contraction schedule. -/
theorem StepProjection.split_last {step : ParallelStep F t u}
    (pre : ParallelHistory t v) (h : ParallelStep H v v')
    {projected : ParallelHistory u w} {last : ParallelStep G v' w}
    (row : StepProjection step (pre.append (.single h)) projected last) :
    ∃ (w' : Term) (K : List Path) (prefix' : ParallelHistory u w')
      (vertical : ParallelStep K v w')
      (tail : ParallelStep (vertical.residualSet H) w' w),
      StepProjection step pre prefix' vertical ∧
      projected = prefix'.append (.single tail) := by
  induction pre generalizing F u w G with
  | nil =>
    cases row with
    | @cons _ _ _ _ _ _ _ _ _ projectedTail _ _ sq remaining =>
      have empty := remaining.length
      cases projectedTail with
      | nil => exact ⟨_,_,.nil _,sq.first,sq.afterFirst,.nil _,rfl⟩
      | cons => simp [ParallelHistory.length] at empty
  | cons first rest ih =>
    cases row with
    | cons sq remaining =>
      obtain ⟨w',K,rest',vertical,tail,hr,he⟩ := ih h remaining
      exact ⟨w',K,.cons sq.afterFirst rest',vertical,tail,.cons sq hr,
        by rw [he]; rfl⟩

/-- The first actual contraction of a complete development is selected in
its source. This reads the actual marked history, not the endpoint redexes. -/
theorem ParallelStep.first_selected (h : ParallelStep F t u)
    (hp : h.paths = p :: ps) : p ∈ F := by
  have hh := ((Marked.completeOld_iff F t).mp h.complete).1
  rw [hp] at hh
  cases hh with
  | cons first rest =>
    exact ((Marked.active_mark F t p).mp first.active).1

/-- A singleton actual development of the transported selection witnesses
an old residual of the source singleton. No endpoint-only identification is
used. -/
theorem ParallelStep.singleton_projection_residual (h : ParallelStep F t u)
    (r : RedexOcc t) (s : RedexOcc u)
    (k : ParallelStep (h.residualSet [r.val]) u v)
    (paths : k.paths = [s.val]) : h.derivation.Residual r s := by
  have hs := k.first_selected paths
  obtain ⟨a,ha,hs⟩ := (Marked.mem_setResidualPositions [r.val] h.markedTarget s.val).mp hs
  have he : a=r.val := List.mem_singleton.mp ha
  subst a
  exact (h.residual_iff r s).mpr hs

/-- The final singleton tile in a genuine projection row preserves the
pointed family. The pre-tile histories are related by the actual row, while
the extension is its actual transported vertical step. -/
theorem StepProjection.last_copy {step : ParallelStep F t u}
    {σ : ParallelHistory t v} {σ' : ParallelHistory u w}
    {last : ParallelStep G v w} (row : StepProjection step σ σ' last)
    (pre : ParallelHistory m t) (r : RedexOcc v) (s : RedexOcc w)
    (tail : ParallelStep (last.residualSet [r.val]) w z)
    (paths : tail.paths = [s.val]) :
    Copy ⟨v,pre.append σ,r⟩
      ⟨w,(pre.append (.single step)).append σ',s⟩ := by
  refine ⟨.single last,?_,?_⟩
  · simpa only [ParallelHistory.append_assoc] using
      (PermEq.prepend pre row.permutation).symm
  · simpa only [ParallelHistory.single_derivation] using
      last.singleton_projection_residual r s tail paths

/-- Nonempty ordinary histories on the two horizontal sides of a genuine
projection have final pointed redexes related by Copy. The construction
extracts both actual last contractions; it assumes no family statement. -/
theorem StepProjection.atomic_last_copy {step : ParallelStep F t u}
    {σ : ParallelHistory t v} {σ' : ParallelHistory u w}
    {last : ParallelStep G v w} (row : StepProjection step σ σ' last)
    (ha : Atomic σ) (hb : Atomic σ') (positive : 0 < σ.length)
    (pre : ParallelHistory m t) :
    ∃ (v₀ w₀ : Term) (p q : Path) (a : ParallelHistory t v₀)
      (b : ParallelHistory u w₀) (R : BetaAt v₀ p v) (S : BetaAt w₀ q w),
      σ = a.append (.single (singleContraction R)) ∧
      σ' = b.append (.single (singleContraction S)) ∧
      Copy ⟨v₀,pre.append a,⟨p,R.redex⟩⟩
        ⟨w₀,(pre.append (.single step)).append b,⟨q,S.redex⟩⟩ := by
  obtain ⟨v₀,p,a,R,ha₀,he⟩ := ha.last positive
  subst σ
  obtain ⟨w₀,K,b,vertical,tail,prefixRow,projected⟩ := row.split_last a (singleContraction R)
  have atom : Atomic (b.append (.single tail)) := by rw [← projected]; exact hb
  obtain ⟨hb₀,htail⟩ := atom.split_append
  obtain ⟨q,S,paths⟩ := htail.single_step
  have tailEq : ParallelHistory.single tail = .single (singleContraction S) :=
    htail.paths_injective (.single S) (by
      simpa only [ParallelHistory.single_derivation] using paths)
  refine ⟨v₀,w₀,p,q,a,b,R,S,rfl,?_,?_⟩
  · exact projected.trans (congrArg (b.append ·) tailEq)
  · exact prefixRow.last_copy pre ⟨p,R.redex⟩ ⟨q,S.redex⟩ tail paths

/-- A row with ordinary horizontal histories gives a genuine Copy relation
between the last pointed contractions of its two complete runs. -/
theorem StepProjection.pointed_copy (R : BetaAt t p u)
    {σ : ParallelHistory t v} {σ' : ParallelHistory u w}
    {last : ParallelStep G v w}
    (row : StepProjection (singleContraction R) σ σ' last)
    (ha : Atomic σ) (hb : Atomic σ') (positive : 0 < σ.length)
    (pre : ParallelHistory m t) (hpre : Atomic pre) :
    ∃ a b : RedexWithHistory m,
      RunRepresents (.of (pre.append σ) (hpre.append ha)) a ∧
      RunRepresents
        (.of ((pre.append (.single (singleContraction R))).append σ')
          ((hpre.append (.single R)).append hb)) b ∧ Copy a b := by
  obtain ⟨v₀,w₀,q,q',a,b,S,S',he,he',hc⟩ :=
    row.atomic_last_copy ha hb positive pre
  have atomA : Atomic a := by
    have hh : Atomic (a.append (.single (singleContraction S))) := by rw [← he]; exact ha
    exact hh.split_append.1
  have atomB : Atomic b := by
    have hh : Atomic (b.append (.single (singleContraction S'))) := by rw [← he']; exact hb
    exact hh.split_append.1
  refine ⟨⟨v₀,pre.append a,⟨q,S.redex⟩⟩,
    ⟨w₀,(pre.append (.single (singleContraction R))).append b,⟨q',S'.redex⟩⟩,
    ?_,?_,hc⟩
  · exact ⟨S,hpre.append atomA,by
      change pre.append σ = (pre.append a).append (.single (singleContraction S))
      rw [he,ParallelHistory.append_assoc]⟩
  · exact ⟨S',(hpre.append (.single R)).append atomB,by
      change (pre.append (.single (singleContraction R))).append σ' =
        ((pre.append (.single (singleContraction R))).append b).append
          (.single (singleContraction S'))
      simp only [he',ParallelHistory.append_assoc]⟩

end Lamping.Lambda
