import Lamping.Checks.FunctionWrappedBodyParent
set_option maxHeartbeats 4000000
namespace Lamping.Checks.WrappedLambdaParent
open AG Graph Lambda Lambda.Labelled FunctionWrappedReachable FunctionWrappedBodyParent

def outerKept : concrete.Kept := ⟨outerApp,by constructor <;> intro h <;> cases h⟩
def oldBodyWire : (encode 0 term).W := .inl (.inr (.inl (.inl (.inr (.inl (.inr (.inl ())))))))
def outerOutside : concrete.Outside := ⟨outerFnWire,by
  rintro ⟨d,h⟩;simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h <;> cases h⟩
def oldBodyOutside : concrete.Outside := ⟨oldBodyWire,by
  rintro ⟨d,h⟩;simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h <;> cases h⟩
theorem beta_root : concrete.site.reduce.wire (.inr (.inl (.inl ())))=
    .inl ⟨.inl outerKept,appCtx⟩ :=
  beta_lift_wire (.inr (.inl (.inl (.inl ())))) (.inl ⟨outerKept,appCtx⟩) rfl
theorem beta_outer : concrete.site.reduce.wire (.inl ⟨.inl outerKept,.inl ()⟩)=
    .inr (.inr (.inl (.inl outerOutside),false)) :=
  beta_lift_wire (.inl ⟨outerKept,.inl ()⟩) (.inr (.inr (outerOutside,false))) rfl
theorem beta_outer_finish : concrete.site.reduce.wire (.inr (.inr (.inl (.inl outerOutside),true)))=
    .inr (.inr (.inr (.inl false),false)) :=
  beta_lift_wire (.inr (.inr (outerOutside,true))) (.inr (.inl (.inr (.inl false)))) rfl
theorem beta_context : concrete.site.reduce.wire (.inr (.inr (.inr (.inl false),true)))=
    .inr (.inr (.inr (.inr true),true)) := rfl
theorem beta_body : concrete.site.reduce.wire (.inr (.inr (.inr (.inr true),false)))=
    .inr (.inr (.inl (.inl oldBodyOutside),false)) :=
  beta_lift_wire (.inr (.inl (.inr (.inr true)))) (.inr (.inr (oldBodyOutside,false))) rfl
theorem beta_body_finish : concrete.site.reduce.wire (.inr (.inr (.inl (.inl oldBodyOutside),true)))=
    .inl ⟨rhsCro,.inr ()⟩ :=
  beta_lift_wire (.inr (.inr (oldBodyOutside,true))) (.inl ⟨croKept,.inr ()⟩) rfl

def outerKept2 : croLambda.Kept := ⟨.inl outerKept,by
  constructor <;> intro h
  · have same:=congrArg Subtype.val (Sum.inl.inj h);cases same
  · have same:=congrArg Subtype.val (Sum.inl.inj h);cases same⟩
def outerOutside2 : croLambda.Outside := ⟨.inl (.inl outerOutside),by
  rintro ⟨d,h⟩;simp only [actualCroLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h <;> cases h⟩
def contextOutside2 : croLambda.Outside := ⟨.inr (.inl false),by
  rintro ⟨d,h⟩;simp only [actualCroLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h <;> cases h⟩
def bodyOutside2 : croLambda.Outside := ⟨.inr (.inr true),by
  rintro ⟨d,h⟩;simp only [actualCroLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h <;> cases h⟩
def oldBodyOutside2 : croLambda.Outside := ⟨.inl (.inl oldBodyOutside),by
  rintro ⟨d,h⟩;simp only [actualCroLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h <;> cases h⟩

theorem lambda_root : croLambda.site.reduce.wire (.inr (.inl (.inl ())))=
    .inl ⟨.inl outerKept2,appCtx⟩ :=
  action2_lift_wire (.inr (.inl (.inl (.inl ())))) (.inl ⟨outerKept2,appCtx⟩) beta_root
theorem lambda_outer : croLambda.site.reduce.wire (.inl ⟨.inl outerKept2,.inl ()⟩)=
    .inr (.inr (.inl (.inl outerOutside2),false)) :=
  action2_lift_wire (.inl ⟨outerKept2,.inl ()⟩) (.inr (.inr (outerOutside2,false))) beta_outer
theorem lambda_outer_finish : croLambda.site.reduce.wire (.inr (.inr (.inl (.inl outerOutside2),true)))=
    .inr (.inr (.inl (.inl contextOutside2),false)) :=
  action2_lift_wire (.inr (.inr (outerOutside2,true))) (.inr (.inr (contextOutside2,false))) beta_outer_finish
theorem lambda_context : croLambda.site.reduce.wire (.inr (.inr (.inl (.inl contextOutside2),true)))=
    .inr (.inr (.inl (.inl bodyOutside2),true)) :=
  action2_lift_wire (.inr (.inr (contextOutside2,true))) (.inr (.inr (bodyOutside2,true))) beta_context
theorem lambda_body : croLambda.site.reduce.wire (.inr (.inr (.inl (.inl bodyOutside2),false)))=
    .inr (.inr (.inl (.inl oldBodyOutside2),false)) :=
  action2_lift_wire (.inr (.inr (bodyOutside2,false))) (.inr (.inr (oldBodyOutside2,false))) beta_body
theorem lambda_body_finish : croLambda.site.reduce.wire (.inr (.inr (.inl (.inl oldBodyOutside2),true)))=
    .inr (.inr (.inr (.inl ()),false)) :=
  action2_lift_wire (.inr (.inr (oldBodyOutside2,true))) (.inr (.inl (.inr (.inl ())))) beta_body_finish
theorem lambda_context_finish : croLambda.site.reduce.wire (.inr (.inr (.inr (.inl ()),true)))=
    .inl ⟨.inr (.inl ()),.inl ()⟩ := rfl

def outerKept3 : croCro.Kept := ⟨.inl outerKept2,by constructor <;> intro h <;> cases h⟩
def outerOutside3 : croCro.Outside := ⟨.inl (.inl outerOutside2),by
  rintro ⟨d,h⟩;simp only [actualCroCroCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h <;> cases h⟩
def contextOutside3 : croCro.Outside := ⟨.inl (.inl contextOutside2),by
  rintro ⟨d,h⟩;simp only [actualCroCroCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h <;> cases h⟩
def bodyOutside3 : croCro.Outside := ⟨.inl (.inl bodyOutside2),by
  rintro ⟨d,h⟩;simp only [actualCroCroCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h <;> cases h⟩
def oldBodyOutside3 : croCro.Outside := ⟨.inl (.inl oldBodyOutside2),by
  rintro ⟨d,h⟩;simp only [actualCroCroCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h <;> cases h⟩
def controlContextOutside3 : croCro.Outside := ⟨.inr (.inl ()),by
  rintro ⟨d,h⟩;simp only [actualCroCroCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h <;> cases h⟩
theorem third_root : croCro.site.reduce.wire (.inr (.inl (.inl ())))=
    .inl ⟨.inl outerKept3,appCtx⟩ :=
  action3_lift_wire (.inr (.inl (.inl (.inl ())))) (.inl ⟨outerKept3,appCtx⟩) lambda_root
theorem third_outer : croCro.site.reduce.wire (.inl ⟨.inl outerKept3,.inl ()⟩)=
    .inr (.inr (.inl (.inl outerOutside3),false)) :=
  action3_lift_wire (.inl ⟨outerKept3,.inl ()⟩) (.inr (.inr (outerOutside3,false))) lambda_outer
theorem third_outer_finish : croCro.site.reduce.wire (.inr (.inr (.inl (.inl outerOutside3),true)))=
    .inr (.inr (.inl (.inl contextOutside3),false)) :=
  action3_lift_wire (.inr (.inr (outerOutside3,true))) (.inr (.inr (contextOutside3,false))) lambda_outer_finish
theorem third_context : croCro.site.reduce.wire (.inr (.inr (.inl (.inl contextOutside3),true)))=
    .inr (.inr (.inl (.inl bodyOutside3),true)) :=
  action3_lift_wire (.inr (.inr (contextOutside3,true))) (.inr (.inr (bodyOutside3,true))) lambda_context
theorem third_body : croCro.site.reduce.wire (.inr (.inr (.inl (.inl bodyOutside3),false)))=
    .inr (.inr (.inl (.inl oldBodyOutside3),false)) :=
  action3_lift_wire (.inr (.inr (bodyOutside3,false))) (.inr (.inr (oldBodyOutside3,false))) lambda_body
theorem third_body_finish : croCro.site.reduce.wire (.inr (.inr (.inl (.inl oldBodyOutside3),true)))=
    .inr (.inr (.inl (.inl controlContextOutside3),false)) :=
  action3_lift_wire (.inr (.inr (oldBodyOutside3,true))) (.inr (.inr (controlContextOutside3,false))) lambda_body_finish
theorem third_context_finish : croCro.site.reduce.wire (.inr (.inr (.inl (.inl controlContextOutside3),true)))=
    .inl ⟨.inl copiedLambda3,.inl ()⟩ :=
  action3_lift_wire (.inr (.inr (controlContextOutside3,true))) (.inl ⟨copiedLambda3,.inl ()⟩) lambda_context_finish

noncomputable def thirdEdges : List (Endpoint croCro.site.reduce) := [
  .inr (.inl (.inl ())),.inl ⟨.inl outerKept3,.inl ()⟩,
  .inr (.inr (.inl (.inl outerOutside3),true)),
  .inr (.inr (.inl (.inl contextOutside3),true)),
  .inr (.inr (.inl (.inl bodyOutside3),false)),
  .inr (.inr (.inl (.inl oldBodyOutside3),true)),
  .inr (.inr (.inl (.inl controlContextOutside3),true))]
theorem thirdLabels (a : Context) : Labelling croCro.site.reduce thirdEdges a a := by
  apply Labelling.cons (by rw [third_root];exact LabelledTurn.node (g:=croCro.site.reduce) (.inl outerKept3) appCtx (.inl ()) (.direct (.appFun a)))
  apply Labelling.cons (by rw [third_outer];exact .transparent _ false a)
  apply Labelling.cons (by rw [third_outer_finish];exact .transparent _ false a)
  apply Labelling.cons (by rw [third_context];exact .transparent _ true a)
  apply Labelling.cons (by rw [third_body];exact .transparent _ false a)
  exact .cons (by rw [third_body_finish];exact .transparent _ false a) (.single _ a)
theorem thirdWord : accessWord croCro.site.reduce thirdEdges=[.fn] := rfl
theorem thirdFinish : thirdEdges.getLast?=some (croCro.site.reduce.wire (.inl ⟨.inl copiedLambda3,.inl ()⟩)) := by
  have inverse:=congrArg croCro.site.reduce.wire third_context_finish
  simp only [Pairing.involutive] at inverse
  simpa only [thirdEdges,List.getLast?_cons_cons,List.getLast?_singleton] using congrArg some inverse
noncomputable def thirdParent : RootAccess croCro.site.reduce (.inl ()) := by
  let flow := Classical.choose cro_certified
  exact ⟨thirdEdges,⟨⟨⟨Context.empty,Context.empty,thirdLabels _⟩,
    (thirdLabels Context.empty).root_forward_of_flow flow (.inl ()) rfl rfl⟩,rfl,⟨.lam,by
      unfold accessKind;rw [thirdFinish]
      simp only [Option.bind_some,Pairing.involutive];rfl⟩⟩⟩

def outerKept4 : croApp.Kept := ⟨.inl outerKept3,by constructor <;> intro h <;> cases h⟩
def outerOutside4 : croApp.Outside := ⟨.inl (.inl outerOutside3),by
  rintro ⟨d,h⟩;simp only [actualCroAppCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h <;> cases h⟩
def contextOutside4 : croApp.Outside := ⟨.inl (.inl contextOutside3),by
  rintro ⟨d,h⟩;simp only [actualCroAppCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h <;> cases h⟩
def bodyOutside4 : croApp.Outside := ⟨.inl (.inl bodyOutside3),by
  rintro ⟨d,h⟩;simp only [actualCroAppCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h <;> cases h⟩
def oldBodyOutside4 : croApp.Outside := ⟨.inl (.inl oldBodyOutside3),by
  rintro ⟨d,h⟩;simp only [actualCroAppCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h <;> cases h⟩
def controlContextOutside4 : croApp.Outside := ⟨.inl (.inl controlContextOutside3),by
  rintro ⟨d,h⟩;simp only [actualCroAppCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h <;> cases h⟩
theorem final_root : croApp.site.reduce.wire (.inr (.inl (.inl ())))=
    .inl ⟨.inl outerKept4,appCtx⟩ :=
  action4_lift_wire (.inr (.inl (.inl (.inl ())))) (.inl ⟨outerKept4,appCtx⟩) third_root
theorem final_outer : croApp.site.reduce.wire (.inl ⟨.inl outerKept4,.inl ()⟩)=
    .inr (.inr (.inl (.inl outerOutside4),false)) :=
  action4_lift_wire (.inl ⟨outerKept4,.inl ()⟩) (.inr (.inr (outerOutside4,false))) third_outer
theorem final_outer_finish : croApp.site.reduce.wire (.inr (.inr (.inl (.inl outerOutside4),true)))=
    .inr (.inr (.inl (.inl contextOutside4),false)) :=
  action4_lift_wire (.inr (.inr (outerOutside4,true))) (.inr (.inr (contextOutside4,false))) third_outer_finish
theorem final_context : croApp.site.reduce.wire (.inr (.inr (.inl (.inl contextOutside4),true)))=
    .inr (.inr (.inl (.inl bodyOutside4),true)) :=
  action4_lift_wire (.inr (.inr (contextOutside4,true))) (.inr (.inr (bodyOutside4,true))) third_context
theorem final_body : croApp.site.reduce.wire (.inr (.inr (.inl (.inl bodyOutside4),false)))=
    .inr (.inr (.inl (.inl oldBodyOutside4),false)) :=
  action4_lift_wire (.inr (.inr (bodyOutside4,false))) (.inr (.inr (oldBodyOutside4,false))) third_body
theorem final_body_finish : croApp.site.reduce.wire (.inr (.inr (.inl (.inl oldBodyOutside4),true)))=
    .inr (.inr (.inl (.inl controlContextOutside4),false)) :=
  action4_lift_wire (.inr (.inr (oldBodyOutside4,true))) (.inr (.inr (controlContextOutside4,false))) third_body_finish
theorem final_context_finish : croApp.site.reduce.wire (.inr (.inr (.inl (.inl controlContextOutside4),true)))=
    .inl ⟨.inl copiedLambda4,.inl ()⟩ :=
  action4_lift_wire (.inr (.inr (controlContextOutside4,true))) (.inl ⟨copiedLambda4,.inl ()⟩) third_context_finish

noncomputable def finalEdges : List (Endpoint croApp.site.reduce) := [
  .inr (.inl (.inl ())),.inl ⟨.inl outerKept4,.inl ()⟩,
  .inr (.inr (.inl (.inl outerOutside4),true)),
  .inr (.inr (.inl (.inl contextOutside4),true)),
  .inr (.inr (.inl (.inl bodyOutside4),false)),
  .inr (.inr (.inl (.inl oldBodyOutside4),true)),
  .inr (.inr (.inl (.inl controlContextOutside4),true))]
theorem finalLabels (a : Context) : Labelling croApp.site.reduce finalEdges a a := by
  apply Labelling.cons (by rw [final_root];exact LabelledTurn.node (g:=croApp.site.reduce) (.inl outerKept4) appCtx (.inl ()) (.direct (.appFun a)))
  apply Labelling.cons (by rw [final_outer];exact .transparent _ false a)
  apply Labelling.cons (by rw [final_outer_finish];exact .transparent _ false a)
  apply Labelling.cons (by rw [final_context];exact .transparent _ true a)
  apply Labelling.cons (by rw [final_body];exact .transparent _ false a)
  exact .cons (by rw [final_body_finish];exact .transparent _ false a) (.single _ a)
theorem finalWord : accessWord croApp.site.reduce finalEdges=[.fn] := rfl
theorem finalFinish : finalEdges.getLast?=some (croApp.site.reduce.wire (.inl ⟨.inl copiedLambda4,.inl ()⟩)) := by
  have inverse:=congrArg croApp.site.reduce.wire final_context_finish
  simp only [Pairing.involutive] at inverse
  simpa only [finalEdges,List.getLast?_cons_cons,List.getLast?_singleton] using congrArg some inverse
noncomputable def finalParent : RootAccess croApp.site.reduce (.inl ()) := by
  let flow := Classical.choose app_certified
  exact ⟨finalEdges,⟨⟨⟨Context.empty,Context.empty,finalLabels _⟩,
    (finalLabels Context.empty).root_forward_of_flow flow (.inl ()) rfl rfl⟩,rfl,⟨.lam,by
      unfold accessKind;rw [finalFinish]
      simp only [Option.bind_some,Pairing.involutive];rfl⟩⟩⟩
end Lamping.Checks.WrappedLambdaParent
