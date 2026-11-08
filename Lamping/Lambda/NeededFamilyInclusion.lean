import Lamping.Lambda.Needed
import Lamping.Lambda.FamilyDevelopmentJoin
import Lamping.Lambda.FamilyStandardizationPull
import Lamping.Lambda.CompleteFamilies

namespace Lamping.Lambda

/-- A needed current redex, with its actual ORIGINAL-m prehistory, belongs to
every same-root history ending in beta normal form. No completeness of alpha
or sigma and no equality of FAM under arbitrary permutation are assumed. -/
theorem needed_family_used_by_normal_history
    {m t n : Term} (alpha : ParallelHistory m t) (r : RedexOcc t)
    (needed : Needed r) (sigma : ParallelHistory m n) (normal : BetaNF n) :
    FamilyUsed sigma (RedexWithHistory.mk t alpha r) := by
  obtain ⟨w,sigmaOverAlpha,alphaOverSigma,grid⟩ :=
    HistoryProjection.exists_projection sigma alpha
  have relative : ∀ a,FamilyUsedAt sigma alphaOverSigma a → True := fun _ _ => True.intro
  have absent : ∀ redex : RedexOcc n,¬(True : Prop) := fun redex _ => normal redex
  obtain ⟨same,_emptyPermutation⟩ :=
    FamilyUsedAt.empty_of_absent (X:=fun _ => True) sigma relative absent
  have normalW : BetaNF w := by rw [same];exact normal
  have actualUse : UsedSource sigmaOverAlpha r := needed sigmaOverAlpha normalW
  have projected : FamilyUsedAt alpha sigmaOverAlpha ⟨t,alpha,r⟩ :=
    FamilyUsedAt.used_source alpha actualUse
  have reflected := grid.used_left (.nil m) projected
  exact reflected

/-- Analysis property of an ACTUAL history: every actual step decomposition
selects at least one Needed redex. It is not an executable exposure oracle and
does not require every selected member of a batch to be needed. -/
def CallByNeedHistory {m u : Term} (rho : ParallelHistory m u) : Prop :=
  ∀ {t v : Term} {F : List Path} (pre : ParallelHistory m t)
    (step : ParallelStep F t v) (tail : ParallelHistory v u),
    rho=pre.append (.cons step tail) →
      ∃ r : RedexOcc t,r.val∈F ∧ Needed r

theorem CallByNeedHistory.prefix {m t u : Term}
    {rho : ParallelHistory m t} {tail : ParallelHistory t u}
    (needful : CallByNeedHistory (rho.append tail)) : CallByNeedHistory rho := by
  intro a b F pre step rest split
  apply needful pre step (rest.append tail)
  simp only [split,ParallelHistory.append_assoc,ParallelHistory.append]

theorem CallByNeedHistory.last_selected {m t u : Term} {F : List Path}
    {pre : ParallelHistory m t} {step : ParallelStep F t u}
    (needful : CallByNeedHistory (pre.append (.single step))) :
    ∃ r : RedexOcc t,r.val∈F ∧ Needed r :=
  needful pre step (.nil u) rfl

/-- Actual whole-family closure extends the one needed representative's
competitor event to every selected current member of that SAME family. -/
theorem CompleteFamilyStep.needed_member_used
    {m t u n : Term} {F : List Path} {pre : ParallelHistory m t}
    {step : ParallelStep F t u} (whole : CompleteFamilyStep pre step)
    (selectedNeeded : ∃ r : RedexOcc t,r.val∈F ∧ Needed r)
    (sigma : ParallelHistory m n) (normal : BetaNF n)
    (s : RedexOcc t) (selected : s.val∈F) :
    FamilyUsed sigma ⟨t,pre,s⟩ := by
  obtain ⟨r,chosen,needed⟩ := selectedNeeded
  have representative : FamilyUsedAt (.nil m) sigma ⟨t,pre,r⟩ :=
    needed_family_used_by_normal_history pre r needed sigma normal
  exact representative.family (whole.same_family r s chosen selected)

/-- A single actual complete+needed batch contributes only family events
already used by any normalizing competitor, at the original historical root. -/
theorem CompleteFamilyStep.needed_step_support
    {m t u n : Term} {F : List Path} {pre : ParallelHistory m t}
    {step : ParallelStep F t u} (whole : CompleteFamilyStep pre step)
    (selectedNeeded : ∃ r : RedexOcc t,r.val∈F ∧ Needed r)
    (sigma : ParallelHistory m n) (normal : BetaNF n)
    {a : RedexWithHistory m} (used : FamilyUsedAt pre (.single step) a) :
    FamilyUsed sigma a := by
  cases used with
  | head selected family =>
    have representative := whole.needed_member_used selectedNeeded sigma normal _ selected
    exact representative.family family
  | tail impossible => cases impossible

/-- Directional FAM inclusion for every finite complete call-by-need prefix.
The prefix itself need not end in normal form. A competitor can have arbitrary
step grouping and need not be complete, needed, Atomic or Standard. -/
theorem CompleteDerivation.needed_family_inclusion
    {m t n : Term} {rho : ParallelHistory m t}
    (complete : CompleteDerivation rho) (needful : CallByNeedHistory rho)
    (sigma : ParallelHistory m n) (normal : BetaNF n) :
    ∀ a : RedexWithHistory m,FamilyUsed rho a → FamilyUsed sigma a := by
  revert needful
  induction complete with
  | nil =>
    intro _needful a used
    cases used
  | @step v t pre F step previous whole ih =>
    intro needful a used
    have prefixNeeded : CallByNeedHistory pre :=
      CallByNeedHistory.prefix (tail:=ParallelHistory.single step) needful
    have selectedNeeded := CallByNeedHistory.last_selected (pre:=pre) (step:=step) needful
    change FamilyUsedAt (.nil m) (pre.append (.single step)) a at used
    rcases (FamilyUsedAt.append_iff (.nil m) pre (.single step) a).mp used with old | fresh
    · exact ih prefixNeeded a old
    · have localUse : FamilyUsedAt pre (.single step) a := fresh
      exact whole.needed_step_support selectedNeeded sigma normal localUse

#print axioms Lamping.Lambda.needed_family_used_by_normal_history
#print axioms Lamping.Lambda.CallByNeedHistory
#print axioms Lamping.Lambda.CallByNeedHistory.prefix
#print axioms Lamping.Lambda.CallByNeedHistory.last_selected
#print axioms Lamping.Lambda.CompleteFamilyStep.needed_member_used
#print axioms Lamping.Lambda.CompleteFamilyStep.needed_step_support
#print axioms Lamping.Lambda.CompleteDerivation.needed_family_inclusion

end Lamping.Lambda
