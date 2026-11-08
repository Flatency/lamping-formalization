import Lamping.Lambda.ProjectionFamilyEvents
import Lamping.Lambda.ArgumentPointedPrefix
import Lamping.Lambda.PointedPrefixOperations
import Lamping.Lambda.ExtractionTermination
namespace Lamping.Lambda

/-- The specified copy contains every family event of the mirrored original
argument program. The ambient prefix may itself contain parallel steps. -/
theorem ArgumentLift.family_used_forward {R : BetaAt t p u}
    {copy : ParallelHistory u v} {original : ParallelHistory t w}
    (lift : ArgumentLift R copy original) (hc : Atomic copy) (ho : Atomic original)
    (pre : ParallelHistory m t) (used : FamilyUsedAt pre original a) :
    FamilyUsedAt (pre.append (.single (singleContraction R))) copy a := by
  generalize lengthEq : original.length=n
  induction n using Nat.strongRecOn generalizing v w with
  | ind n ih =>
    by_cases positive : 0<original.length
    · obtain ⟨w0,q,opre,S,hopre,oeq⟩ := ho.last positive
      have copyPositive : 0<copy.length := by have := lift.length hc ho; omega
      obtain ⟨v0,q',cpre,S',hcpre,ceq⟩ := hc.last copyPositive
      let sourcePoint : RedexWithHistory u := ⟨v0,cpre,⟨q',S'.redex⟩⟩
      let targetPoint : RedexWithHistory t := ⟨w0,opre,⟨q,S.redex⟩⟩
      have sourceRep : RunRepresents (.of copy hc) sourcePoint := ⟨S',hcpre,ceq⟩
      have targetRep : RunRepresents (.of original ho) targetPoint := ⟨S,hopre,oeq⟩
      obtain ⟨prefixLift,_⟩ := lift.pointed_prefix hc ho sourcePoint targetPoint sourceRep targetRep
      have used' := used
      rw [oeq] at used'
      rcases (FamilyUsedAt.append_iff pre opre (.single (singleContraction S)) a).mp used' with earlier | finalEvent
      · have smaller : opre.length<n := by
          have le := congrArg ParallelHistory.length oeq
          simp only [ParallelHistory.length_append,ParallelHistory.single,ParallelHistory.length] at le
          omega
        have copied := ih opre.length smaller prefixLift hcpre hopre earlier rfl
        rw [ceq]
        exact (FamilyUsedAt.append_iff _ cpre (.single (singleContraction S')) a).mpr (.inl copied)
      · have family : FamilyEq ⟨w0,pre.append opre,⟨q,S.redex⟩⟩ a := by
          cases finalEvent with
          | head selected family =>
            have ep := List.mem_singleton.mp selected
            have er : _ = (⟨q,S.redex⟩ : RedexOcc w0) := Subtype.ext ep
            subst er
            exact family
          | tail impossible => cases impossible
        have corresponding := lift.pointed_family hc ho copyPositive (.nil t) (.nil t)
          targetPoint (sourcePoint.prepend (.single (singleContraction R))) targetRep
          (sourceRep.prepend (.single (singleContraction R)) (.single R))
        have globalFamily := corresponding.prepend pre
        have family' : FamilyEq
            ⟨v0,(pre.append (.single (singleContraction R))).append cpre,⟨q',S'.redex⟩⟩ a := by
          apply FamilyEq.trans (FamilyEq.symm (by
            simpa only [RedexWithHistory.prepend,ParallelHistory.append,ParallelHistory.append_assoc] using globalFamily)) family
        rw [ceq]
        apply (FamilyUsedAt.append_iff _ cpre (.single (singleContraction S')) a).mpr
        exact .inr (.head (by simp) family')
    · have zero : original.length=0 := by omega
      cases original with
      | nil => cases used
      | cons => simp only [ParallelHistory.length] at zero; omega

end Lamping.Lambda
