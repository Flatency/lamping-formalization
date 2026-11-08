import Lamping.Lambda.LOProjection

namespace Lamping.Lambda

/-- Actual source t reduces to u by a complete parallel step containing at
least one needed source redex. Relation arguments follow accessibility order. -/
def NeededParallelNext (u t : Term) : Prop :=
  ∃ (F : List Path) (_step : ParallelStep F t u) (r : RedexOcc t),
    r.val ∈ F ∧ Needed r

/-- Strong induction on a supplied finite LO normalization witness. Every
actual needed-selected successor gets a strictly shorter actual LO witness. -/
theorem LOHistory.acc_neededParallelNext {t n : Term}
    {rho : ParallelHistory t n} (lo : LOHistory rho) (normal : BetaNF n) :
    Acc NeededParallelNext t := by
  have main : ∀ (k : Nat) {t n : Term} {rho : ParallelHistory t n},
      rho.length=k → LOHistory rho → BetaNF n → Acc NeededParallelNext t := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro t n rho length lo normal
      apply Acc.intro
      intro u next
      obtain ⟨F,step,r,selected,needed⟩ := next
      obtain ⟨w,G,tau,last,row⟩ := StepProjection.exists_projection step rho
      obtain ⟨observed,targetLO,targetNormal,_same,_permutation,shorter⟩ :=
        row.exists_shorter_lo_of_needed_selected lo normal r selected needed
      have decrease : observed.length < k := by
        rw [←length]
        exact shorter
      exact ih observed.length decrease (rho:=observed) rfl targetLO targetNormal
  exact main rho.length (rho:=rho) rfl lo normal

/-- Normalizability supplies only a finite witness in Prop. This theorem
does not select an evaluator, decide HasNF, or give physical rewrite costs. -/
theorem HasNF.acc_neededParallelNext {t : Term} (normalizable : HasNF t) :
    Acc NeededParallelNext t := by
  obtain ⟨n,rho,lo,normal⟩ := normalizable.exists_lo
  exact lo.acc_neededParallelNext normal

#print axioms NeededParallelNext
#print axioms LOHistory.acc_neededParallelNext
#print axioms HasNF.acc_neededParallelNext

end Lamping.Lambda
