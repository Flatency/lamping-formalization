import Lamping.Checks.Q0BodyLabelCounterexample
import Lamping.Lambda.SingleContraction
import Lamping.Lambda.CompleteFamilies
import Lamping.Lambda.LabelFamilyDegreeEquivalence

namespace Lamping.Checks.Q0CompleteBodyLabelCounterexample
open Lambda Lambda.Labelled Q0BodyLabelCounterexample

private theorem singleton_family_of_computed_degree_fiber
    {original current next : LTerm}
    (initial : INIT original)
    (prior : ParallelHistory original.erase current.erase)
    (labels : History prior.derivation.paths original current)
    {p : Path} {alpha : Label}
    (beta : BetaAt current.erase p next.erase)
    (atDegree : current.degreeAt p = some alpha)
    (fiber : (redexPositions current.erase).filter
      (fun q => decide (current.degreeAt q = some alpha)) = [p]) :
    CompleteFamilyStep prior (singleContraction beta) := by
  let r : RedexOcc current.erase := ⟨p,beta.redex⟩
  refine ⟨?_,r,List.mem_singleton_self _,?_⟩
  · intro q member
    have same := List.mem_singleton.mp member
    subst q
    exact beta.redex
  · intro s
    have iffDegree := family_iff_degree original initial
      (⟨current.erase,prior,r⟩ : RedexWithHistory original.erase)
      (⟨current.erase,prior,s⟩ : RedexWithHistory original.erase)
    change FamilyEq _ _ ↔ degreeAlong original prior.derivation.paths p =
      degreeAlong original prior.derivation.paths s.val at iffDegree
    rw [degreeAlong_witness labels,degreeAlong_witness labels] at iffDegree
    constructor
    · intro member
      have same : s=r := Subtype.ext (List.mem_singleton.mp member)
      subst s
      exact .copy (Copy.refl _)
    · intro family
      have degree : current.degreeAt s.val = some alpha :=
        (iffDegree.mp family).symm.trans atDegree
      have member : s.val ∈ (redexPositions current.erase).filter
          (fun q => decide (current.degreeAt q = some alpha)) := by
        exact List.mem_filter.mpr ⟨(mem_redexPositions current.erase s.val).mpr s.property,
          by simpa using degree⟩
      rw [fiber] at member
      exact member

private def labelStep1 : StepAt [] original t1 := .root _ _ _ _
private def labelStep2 : StepAt [.fn] t1 t2 := .fn (.root _ _ _ _)
private def labelStep3 : StepAt [.arg] t2 t3 := .arg (.root _ _ _ _)
private def labelStep4 : StepAt [.fn,.fn,.fn,.body] t3 t4 :=
  .fn (.fn (.fn (.body (.root _ _ _ _))))
private def labelStep5 : StepAt [.arg,.fn,.fn,.body] t4 target :=
  .arg (.fn (.fn (.body (.root _ _ _ _))))
private def step1 := singleContraction labelStep1.betaAt
private def step2 := singleContraction labelStep2.betaAt
private def step3 := singleContraction labelStep3.betaAt
private def step4 := singleContraction labelStep4.betaAt
private def step5 := singleContraction labelStep5.betaAt
private def prior0 := ParallelHistory.nil original.erase
private def prior1 := prior0.append (.single step1)
private def prior2 := prior1.append (.single step2)
private def prior3 := prior2.append (.single step3)
private def prior4 := prior3.append (.single step4)
private def prior5 := prior4.append (.single step5)

private def labels0 : History prior0.derivation.paths original original := .nil _
private def labels1 : History prior1.derivation.paths original t1 :=
  .cons labelStep1 (.nil _)
private def labels2 : History prior2.derivation.paths original t2 :=
  .cons labelStep1 (.cons labelStep2 (.nil _))
private def labels3 : History prior3.derivation.paths original t3 :=
  .cons labelStep1 (.cons labelStep2 (.cons labelStep3 (.nil _)))
private def labels4 : History prior4.derivation.paths original t4 :=
  .cons labelStep1 (.cons labelStep2 (.cons labelStep3 (.cons labelStep4 (.nil _))))

theorem actual_complete_prior :
    ∃ prior : ParallelHistory original.erase target.erase,
      prior.derivation.paths = schedule ∧
      History prior.derivation.paths original target ∧ CompleteDerivation prior := by
  have complete0 : CompleteDerivation prior0 := .nil _
  have complete1 : CompleteDerivation prior1 := .step complete0
    (singleton_family_of_computed_degree_fiber actual_initial.1 prior0 labels0
      (alpha:=.atom 1) labelStep1.betaAt rfl (by decide))
  have complete2 : CompleteDerivation prior2 := .step complete1
    (singleton_family_of_computed_degree_fiber actual_initial.1 prior1 labels1
      (alpha:=a) labelStep2.betaAt rfl (by decide))
  have complete3 : CompleteDerivation prior3 := .step complete2
    (singleton_family_of_computed_degree_fiber actual_initial.1 prior2 labels2
      (alpha:=b) labelStep3.betaAt rfl (by decide))
  have complete4 : CompleteDerivation prior4 := .step complete3
    (singleton_family_of_computed_degree_fiber actual_initial.1 prior3 labels3
      (alpha:=c) labelStep4.betaAt rfl (by decide))
  have complete5 : CompleteDerivation prior5 := .step complete4
    (singleton_family_of_computed_degree_fiber actual_initial.1 prior4 labels4
      (alpha:=d) labelStep5.betaAt rfl (by decide))
  exact ⟨prior5,rfl,actualHistory,complete5⟩

#print axioms actual_complete_prior

end Lamping.Checks.Q0CompleteBodyLabelCounterexample
