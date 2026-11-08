import Lamping.Checks.WrappedLambdaParent
set_option maxHeartbeats 4000000
namespace Lamping.Checks.WrappedOuterParent
open AG Graph Lambda Lambda.Labelled FunctionWrappedReachable WrappedLambdaParent

theorem source_root_wire : croApp.site.net.wire (.inr (.inl (.inl ())))=
    .inl ⟨.inl outerKept4,appCtx⟩ := by
  apply croApp.sourceIso.symm.ends.injective
  rw [croApp.sourceIso.symm.wiring]
  exact third_root
theorem sourceFinish : ([.inr (.inl (.inl ()))] : List (Endpoint croApp.site.net)).getLast?=
    some (croApp.site.net.wire (.inl ⟨.inl outerKept4,appCtx⟩)) := by
  have inverse := congrArg croApp.site.net.wire source_root_wire
  simp only [Pairing.involutive] at inverse
  exact congrArg some inverse
theorem targetFinish : ([.inr (.inl (.inl ()))] : List (Endpoint croApp.site.reduce)).getLast?=
    some (croApp.site.reduce.wire (.inl ⟨.inl outerKept4,appCtx⟩)) := by
  have inverse := congrArg croApp.site.reduce.wire final_root
  simp only [Pairing.involutive] at inverse
  exact congrArg some inverse
noncomputable def sourceParent : RootAccess croApp.site.net (.inl ()) :=
  ⟨[.inr (.inl (.inl ()))],⟨⟨⟨Context.empty,Context.empty,.single _ _⟩,.single _⟩,
    rfl,⟨.app,by
      unfold accessKind;rw [sourceFinish]
      simp only [Option.bind_some,Pairing.involutive];rfl⟩⟩⟩
noncomputable def targetParent : RootAccess croApp.site.reduce (.inl ()) :=
  ⟨[.inr (.inl (.inl ()))],⟨⟨⟨Context.empty,Context.empty,.single _ _⟩,.single _⟩,
    rfl,⟨.app,by
      unfold accessKind;rw [targetFinish]
      simp only [Option.bind_some,Pairing.involutive];rfl⟩⟩⟩
theorem sourceWord : accessWord croApp.site.net sourceParent.val=[] := rfl
theorem targetWord : accessWord croApp.site.reduce targetParent.val=[] := rfl
#print axioms sourceParent
#print axioms targetParent
end Lamping.Checks.WrappedOuterParent
