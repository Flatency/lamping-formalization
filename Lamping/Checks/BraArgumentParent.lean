import Lamping.Checks.BraFunctionBodyParent
set_option maxHeartbeats 4000000
namespace Lamping.Checks.BraArgumentParent
open AG Graph Lambda Lambda.Labelled BraFunctionReachable BraFunctionBodyParent

def oldRootApp : (encode 0 term).N := .inr (.inl (.inr (.inl (.inl ()))))
def oldReader : (encode 0 term).N := .inr (.inl (.inr (.inr (.inr ()))) )
def oldBodyWire : (encode 0 term).W := .inl (.inr (.inl (.inr (.inl ()))))
def oldArgRootWire : (encode 0 term).W := .inl (.inr (.inl (.inl (.inr (.inr (.inr (.inl ())))))))
def oldArgFreeWire : (encode 0 term).W := .inl (.inr (.inl (.inl (.inr (.inr (.inr (.inr ⟨0,rfl⟩)))))))

def rootKept : concrete.Kept := ⟨oldRootApp,by constructor <;> intro h <;> cases h⟩
def readerKept : concrete.Kept := ⟨oldReader,by constructor <;> intro h <;> cases h⟩
def bodyOutside : concrete.Outside := ⟨oldBodyWire,by
  rintro ⟨d,h⟩;simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h <;> cases h⟩
def argRootOutside : concrete.Outside := ⟨oldArgRootWire,by
  rintro ⟨d,h⟩;simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h <;> cases h⟩
def argFreeOutside : concrete.Outside := ⟨oldArgFreeWire,by
  rintro ⟨d,h⟩;simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h <;> cases h⟩

theorem beta_root : concrete.site.reduce.wire (.inr (.inl (.inl ())))=
    .inr (.inr (.inr (.inl false),false)) :=
  beta_lift_wire (.inr (.inl (.inl (.inl ())))) (.inr (.inl (.inr (.inl false)))) rfl

theorem beta_context : concrete.site.reduce.wire (.inr (.inr (.inr (.inl false),true)))=
    .inr (.inr (.inr (.inr true),true)) := rfl

theorem beta_body : concrete.site.reduce.wire (.inr (.inr (.inr (.inr true),false)))=
    .inr (.inr (.inl (.inl bodyOutside),false)) :=
  beta_lift_wire (.inr (.inl (.inr (.inr true)))) (.inr (.inr (bodyOutside,false))) rfl

theorem beta_body_finish : concrete.site.reduce.wire (.inr (.inr (.inl (.inl bodyOutside),true)))=
    .inl ⟨.inl rootKept,appCtx⟩ :=
  beta_lift_wire (.inr (.inr (bodyOutside,true))) (.inl ⟨rootKept,appCtx⟩) rfl

theorem beta_arg : concrete.site.reduce.wire (.inl ⟨.inl rootKept,appArg⟩)=
    .inr (.inr (.inl (.inl argRootOutside),false)) :=
  beta_lift_wire (.inl ⟨rootKept,appArg⟩) (.inr (.inr (argRootOutside,false))) rfl

theorem beta_arg_finish : concrete.site.reduce.wire (.inr (.inr (.inl (.inl argRootOutside),true)))=
    .inl ⟨.inl readerKept,.inr ()⟩ :=
  beta_lift_wire (.inr (.inr (argRootOutside,true))) (.inl ⟨readerKept,.inr ()⟩) rfl

theorem beta_reader : concrete.site.reduce.wire (.inl ⟨.inl readerKept,.inl ()⟩)=
    .inr (.inr (.inl (.inl argFreeOutside),true)) :=
  beta_lift_wire (.inl ⟨readerKept,.inl ()⟩) (.inr (.inr (argFreeOutside,true))) rfl

theorem beta_reader_finish : concrete.site.reduce.wire (.inr (.inr (.inl (.inl argFreeOutside),false)))=
    .inl ⟨.inl braKept,.inr ()⟩ :=
  beta_lift_wire (.inr (.inr (argFreeOutside,false))) (.inl ⟨braKept,.inr ()⟩) rfl

def rootKept2 : braLambda.Kept := ⟨.inl rootKept,by
  constructor <;> intro h <;> have hs:=congrArg Subtype.val (Sum.inl.inj h) <;> cases hs⟩

def readerKept2 : braLambda.Kept := ⟨.inl readerKept,by
  constructor <;> intro h <;> have hs:=congrArg Subtype.val (Sum.inl.inj h) <;> cases hs⟩

def contextOutside2 : braLambda.Outside := ⟨.inr (.inl false),by
  rintro ⟨d,h⟩;simp only [actualBraLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h <;> cases h⟩

def bodyContextOutside2 : braLambda.Outside := ⟨.inr (.inr true),by
  rintro ⟨d,h⟩;simp only [actualBraLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h <;> cases h⟩

def bodyOutside2 : braLambda.Outside := ⟨.inl (.inl bodyOutside),by
  rintro ⟨d,h⟩;simp only [actualBraLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h <;> cases h⟩

def argRootOutside2 : braLambda.Outside := ⟨.inl (.inl argRootOutside),by
  rintro ⟨d,h⟩;simp only [actualBraLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h <;> cases h⟩

def argFreeOutside2 : braLambda.Outside := ⟨.inl (.inl argFreeOutside),by
  rintro ⟨d,h⟩;simp only [actualBraLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h <;> cases h⟩

theorem lambda_root : braLambda.site.reduce.wire (.inr (.inl (.inl ())))=
    .inr (.inr (.inl (.inl contextOutside2),false)) :=
  action2_lift_wire (.inr (.inl (.inl (.inl ())))) (.inr (.inr (contextOutside2,false))) beta_root

theorem lambda_context : braLambda.site.reduce.wire (.inr (.inr (.inl (.inl contextOutside2),true)))=
    .inr (.inr (.inl (.inl bodyContextOutside2),true)) :=
  action2_lift_wire (.inr (.inr (contextOutside2,true))) (.inr (.inr (bodyContextOutside2,true))) beta_context

theorem lambda_body : braLambda.site.reduce.wire (.inr (.inr (.inl (.inl bodyContextOutside2),false)))=
    .inr (.inr (.inl (.inl bodyOutside2),false)) :=
  action2_lift_wire (.inr (.inr (bodyContextOutside2,false))) (.inr (.inr (bodyOutside2,false))) beta_body

theorem lambda_body_finish : braLambda.site.reduce.wire (.inr (.inr (.inl (.inl bodyOutside2),true)))=
    .inl ⟨.inl rootKept2,appCtx⟩ :=
  action2_lift_wire (.inr (.inr (bodyOutside2,true))) (.inl ⟨rootKept2,appCtx⟩) beta_body_finish

theorem lambda_arg : braLambda.site.reduce.wire (.inl ⟨.inl rootKept2,appArg⟩)=
    .inr (.inr (.inl (.inl argRootOutside2),false)) :=
  action2_lift_wire (.inl ⟨rootKept2,appArg⟩) (.inr (.inr (argRootOutside2,false))) beta_arg

theorem lambda_arg_finish : braLambda.site.reduce.wire (.inr (.inr (.inl (.inl argRootOutside2),true)))=
    .inl ⟨.inl readerKept2,.inr ()⟩ :=
  action2_lift_wire (.inr (.inr (argRootOutside2,true))) (.inl ⟨readerKept2,.inr ()⟩) beta_arg_finish

theorem lambda_reader : braLambda.site.reduce.wire (.inl ⟨.inl readerKept2,.inl ()⟩)=
    .inr (.inr (.inl (.inl argFreeOutside2),true)) :=
  action2_lift_wire (.inl ⟨readerKept2,.inl ()⟩) (.inr (.inr (argFreeOutside2,true))) beta_reader

theorem lambda_reader_finish : braLambda.site.reduce.wire (.inr (.inr (.inl (.inl argFreeOutside2),false)))=
    .inr (.inr (.inr (.inl ()),false)) :=
  action2_lift_wire (.inr (.inr (argFreeOutside2,false))) (.inr (.inl (.inr (.inl ())))) beta_reader_finish

theorem lambda_context_finish : braLambda.site.reduce.wire (.inr (.inr (.inr (.inl ()),true)))=
    .inl ⟨.inr (.inl ()),.inl ()⟩ := rfl

def rootKept3 : braCro.Kept := ⟨.inl rootKept2,by constructor <;> intro h <;> cases h⟩

def readerKept3 : braCro.Kept := ⟨.inl readerKept2,by constructor <;> intro h <;> cases h⟩

def contextOutside3 : braCro.Outside := ⟨.inl (.inl contextOutside2),by
  rintro ⟨d,h⟩;simp only [actualBraCroCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h <;> cases h⟩

def bodyContextOutside3 : braCro.Outside := ⟨.inl (.inl bodyContextOutside2),by
  rintro ⟨d,h⟩;simp only [actualBraCroCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h <;> cases h⟩

def bodyOutside3 : braCro.Outside := ⟨.inl (.inl bodyOutside2),by
  rintro ⟨d,h⟩;simp only [actualBraCroCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h <;> cases h⟩

def argRootOutside3 : braCro.Outside := ⟨.inl (.inl argRootOutside2),by
  rintro ⟨d,h⟩;simp only [actualBraCroCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h <;> cases h⟩

def argFreeOutside3 : braCro.Outside := ⟨.inl (.inl argFreeOutside2),by
  rintro ⟨d,h⟩;simp only [actualBraCroCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h <;> cases h⟩

def controlContextOutside3 : braCro.Outside := ⟨.inr (.inl ()),by
  rintro ⟨d,h⟩;simp only [actualBraCroCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h <;> cases h⟩

theorem third_root : braCro.site.reduce.wire (.inr (.inl (.inl ())))=
    .inr (.inr (.inl (.inl contextOutside3),false)) :=
  action3_lift_wire (.inr (.inl (.inl (.inl ())))) (.inr (.inr (contextOutside3,false))) lambda_root

theorem third_context : braCro.site.reduce.wire (.inr (.inr (.inl (.inl contextOutside3),true)))=
    .inr (.inr (.inl (.inl bodyContextOutside3),true)) :=
  action3_lift_wire (.inr (.inr (contextOutside3,true))) (.inr (.inr (bodyContextOutside3,true))) lambda_context

theorem third_body : braCro.site.reduce.wire (.inr (.inr (.inl (.inl bodyContextOutside3),false)))=
    .inr (.inr (.inl (.inl bodyOutside3),false)) :=
  action3_lift_wire (.inr (.inr (bodyContextOutside3,false))) (.inr (.inr (bodyOutside3,false))) lambda_body

theorem third_body_finish : braCro.site.reduce.wire (.inr (.inr (.inl (.inl bodyOutside3),true)))=
    .inl ⟨.inl rootKept3,appCtx⟩ :=
  action3_lift_wire (.inr (.inr (bodyOutside3,true))) (.inl ⟨rootKept3,appCtx⟩) lambda_body_finish

theorem third_arg : braCro.site.reduce.wire (.inl ⟨.inl rootKept3,appArg⟩)=
    .inr (.inr (.inl (.inl argRootOutside3),false)) :=
  action3_lift_wire (.inl ⟨rootKept3,appArg⟩) (.inr (.inr (argRootOutside3,false))) lambda_arg

theorem third_arg_finish : braCro.site.reduce.wire (.inr (.inr (.inl (.inl argRootOutside3),true)))=
    .inl ⟨.inl readerKept3,.inr ()⟩ :=
  action3_lift_wire (.inr (.inr (argRootOutside3,true))) (.inl ⟨readerKept3,.inr ()⟩) lambda_arg_finish

theorem third_reader : braCro.site.reduce.wire (.inl ⟨.inl readerKept3,.inl ()⟩)=
    .inr (.inr (.inl (.inl argFreeOutside3),true)) :=
  action3_lift_wire (.inl ⟨readerKept3,.inl ()⟩) (.inr (.inr (argFreeOutside3,true))) lambda_reader

theorem third_reader_finish : braCro.site.reduce.wire (.inr (.inr (.inl (.inl argFreeOutside3),false)))=
    .inr (.inr (.inl (.inl controlContextOutside3),false)) :=
  action3_lift_wire (.inr (.inr (argFreeOutside3,false))) (.inr (.inr (controlContextOutside3,false))) lambda_reader_finish

theorem third_context_finish : braCro.site.reduce.wire (.inr (.inr (.inl (.inl controlContextOutside3),true)))=
    .inl ⟨.inl copiedLambda3,.inl ()⟩ :=
  action3_lift_wire (.inr (.inr (controlContextOutside3,true))) (.inl ⟨copiedLambda3,.inl ()⟩) lambda_context_finish

noncomputable def thirdEdges : List (Endpoint braCro.site.reduce) := [
  .inr (.inl (.inl ())),
  .inr (.inr (.inl (.inl contextOutside3),true)),
  .inr (.inr (.inl (.inl bodyContextOutside3),false)),
  .inr (.inr (.inl (.inl bodyOutside3),true)),
  .inl ⟨.inl rootKept3,appArg⟩,
  .inr (.inr (.inl (.inl argRootOutside3),true)),
  .inl ⟨.inl readerKept3,.inl ()⟩,
  .inr (.inr (.inl (.inl argFreeOutside3),false)),
  .inr (.inr (.inl (.inl controlContextOutside3),true))]

def rootKept4 : braApp.Kept := ⟨.inl rootKept3,by constructor <;> intro h <;> cases h⟩

def readerKept4 : braApp.Kept := ⟨.inl readerKept3,by constructor <;> intro h <;> cases h⟩

def contextOutside4 : braApp.Outside := ⟨.inl (.inl contextOutside3),by
  rintro ⟨d,h⟩;simp only [actualBraAppCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h <;> cases h⟩

def bodyContextOutside4 : braApp.Outside := ⟨.inl (.inl bodyContextOutside3),by
  rintro ⟨d,h⟩;simp only [actualBraAppCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h <;> cases h⟩

def bodyOutside4 : braApp.Outside := ⟨.inl (.inl bodyOutside3),by
  rintro ⟨d,h⟩;simp only [actualBraAppCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h <;> cases h⟩

def argRootOutside4 : braApp.Outside := ⟨.inl (.inl argRootOutside3),by
  rintro ⟨d,h⟩;simp only [actualBraAppCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h <;> cases h⟩

def argFreeOutside4 : braApp.Outside := ⟨.inl (.inl argFreeOutside3),by
  rintro ⟨d,h⟩;simp only [actualBraAppCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h <;> cases h⟩

def controlContextOutside4 : braApp.Outside := ⟨.inl (.inl controlContextOutside3),by
  rintro ⟨d,h⟩;simp only [actualBraAppCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h <;> cases h⟩

theorem final_root : braApp.site.reduce.wire (.inr (.inl (.inl ())))=
    .inr (.inr (.inl (.inl contextOutside4),false)) :=
  action4_lift_wire (.inr (.inl (.inl (.inl ())))) (.inr (.inr (contextOutside4,false))) third_root

theorem final_context : braApp.site.reduce.wire (.inr (.inr (.inl (.inl contextOutside4),true)))=
    .inr (.inr (.inl (.inl bodyContextOutside4),true)) :=
  action4_lift_wire (.inr (.inr (contextOutside4,true))) (.inr (.inr (bodyContextOutside4,true))) third_context

theorem final_body : braApp.site.reduce.wire (.inr (.inr (.inl (.inl bodyContextOutside4),false)))=
    .inr (.inr (.inl (.inl bodyOutside4),false)) :=
  action4_lift_wire (.inr (.inr (bodyContextOutside4,false))) (.inr (.inr (bodyOutside4,false))) third_body

theorem final_body_finish : braApp.site.reduce.wire (.inr (.inr (.inl (.inl bodyOutside4),true)))=
    .inl ⟨.inl rootKept4,appCtx⟩ :=
  action4_lift_wire (.inr (.inr (bodyOutside4,true))) (.inl ⟨rootKept4,appCtx⟩) third_body_finish

theorem final_arg : braApp.site.reduce.wire (.inl ⟨.inl rootKept4,appArg⟩)=
    .inr (.inr (.inl (.inl argRootOutside4),false)) :=
  action4_lift_wire (.inl ⟨rootKept4,appArg⟩) (.inr (.inr (argRootOutside4,false))) third_arg

theorem final_arg_finish : braApp.site.reduce.wire (.inr (.inr (.inl (.inl argRootOutside4),true)))=
    .inl ⟨.inl readerKept4,.inr ()⟩ :=
  action4_lift_wire (.inr (.inr (argRootOutside4,true))) (.inl ⟨readerKept4,.inr ()⟩) third_arg_finish

theorem final_reader : braApp.site.reduce.wire (.inl ⟨.inl readerKept4,.inl ()⟩)=
    .inr (.inr (.inl (.inl argFreeOutside4),true)) :=
  action4_lift_wire (.inl ⟨readerKept4,.inl ()⟩) (.inr (.inr (argFreeOutside4,true))) third_reader

theorem final_reader_finish : braApp.site.reduce.wire (.inr (.inr (.inl (.inl argFreeOutside4),false)))=
    .inr (.inr (.inl (.inl controlContextOutside4),false)) :=
  action4_lift_wire (.inr (.inr (argFreeOutside4,false))) (.inr (.inr (controlContextOutside4,false))) third_reader_finish

theorem final_context_finish : braApp.site.reduce.wire (.inr (.inr (.inl (.inl controlContextOutside4),true)))=
    .inl ⟨.inl copiedLambda4,.inl ()⟩ :=
  action4_lift_wire (.inr (.inr (controlContextOutside4,true))) (.inl ⟨copiedLambda4,.inl ()⟩) third_context_finish

noncomputable def finalEdges : List (Endpoint braApp.site.reduce) := [
  .inr (.inl (.inl ())),
  .inr (.inr (.inl (.inl contextOutside4),true)),
  .inr (.inr (.inl (.inl bodyContextOutside4),false)),
  .inr (.inr (.inl (.inl bodyOutside4),true)),
  .inl ⟨.inl rootKept4,appArg⟩,
  .inr (.inr (.inl (.inl argRootOutside4),true)),
  .inl ⟨.inl readerKept4,.inl ()⟩,
  .inr (.inr (.inl (.inl argFreeOutside4),false)),
  .inr (.inr (.inl (.inl controlContextOutside4),true))]

private theorem empty_replace (n : Nat) : Context.empty.replace n Context.empty=Context.empty := by
  ext k;simp [Context.replace]
private theorem emptyCro (n : Nat) : Traversal n (.op .cro) (.inr ()) (.inl ()) Context.empty Context.empty := by
  simpa only [Context.cons_empty,empty_replace] using
    (Traversal.direct (Passage.cro (i:=n) Context.empty Context.empty))

theorem thirdLabels : Labelling braCro.site.reduce thirdEdges Context.empty Context.empty := by
  apply Labelling.cons (by rw [third_root];exact LabelledTurn.transparent (g:=braCro.site.reduce) _ false Context.empty)
  apply Labelling.cons (by rw [third_context];exact LabelledTurn.transparent (g:=braCro.site.reduce) _ true Context.empty)
  apply Labelling.cons (by rw [third_body];exact LabelledTurn.transparent (g:=braCro.site.reduce) _ false Context.empty)
  apply Labelling.cons (by rw [third_body_finish];exact LabelledTurn.node (g:=braCro.site.reduce) (.inl rootKept3) appCtx appArg (.direct (.appArg Context.empty)))
  apply Labelling.cons (by rw [third_arg];exact LabelledTurn.transparent (g:=braCro.site.reduce) _ false Context.empty)
  apply Labelling.cons (by rw [third_arg_finish];exact LabelledTurn.node (g:=braCro.site.reduce) (.inl readerKept3) (.inr ()) (.inl ()) (emptyCro 1))
  apply Labelling.cons (by rw [third_reader];exact LabelledTurn.transparent (g:=braCro.site.reduce) _ true Context.empty)
  exact .cons (by rw [third_reader_finish];exact LabelledTurn.transparent (g:=braCro.site.reduce) _ false Context.empty) (.single _ _)

theorem thirdWord : accessWord braCro.site.reduce thirdEdges=[.arg] := rfl

theorem thirdFinish : thirdEdges.getLast?=some (braCro.site.reduce.wire (.inl ⟨.inl copiedLambda3,.inl ()⟩)) := by
  have inverse:=congrArg braCro.site.reduce.wire third_context_finish
  simp only [Pairing.involutive] at inverse
  simpa only [thirdEdges,List.getLast?_cons_cons,List.getLast?_singleton] using congrArg some inverse

noncomputable def thirdParent : RootAccess braCro.site.reduce (.inl ()) := by
  let flow := Classical.choose cro_certified
  exact ⟨thirdEdges,⟨⟨⟨Context.empty,Context.empty,thirdLabels⟩,
    thirdLabels.root_forward_of_flow flow (.inl ()) rfl rfl⟩,rfl,⟨.lam,by
      unfold accessKind;rw [thirdFinish]
      simp only [Option.bind_some,Pairing.involutive];rfl⟩⟩⟩

theorem finalLabels : Labelling braApp.site.reduce finalEdges Context.empty Context.empty := by
  apply Labelling.cons (by rw [final_root];exact LabelledTurn.transparent (g:=braApp.site.reduce) _ false Context.empty)
  apply Labelling.cons (by rw [final_context];exact LabelledTurn.transparent (g:=braApp.site.reduce) _ true Context.empty)
  apply Labelling.cons (by rw [final_body];exact LabelledTurn.transparent (g:=braApp.site.reduce) _ false Context.empty)
  apply Labelling.cons (by rw [final_body_finish];exact LabelledTurn.node (g:=braApp.site.reduce) (.inl rootKept4) appCtx appArg (.direct (.appArg Context.empty)))
  apply Labelling.cons (by rw [final_arg];exact LabelledTurn.transparent (g:=braApp.site.reduce) _ false Context.empty)
  apply Labelling.cons (by rw [final_arg_finish];exact LabelledTurn.node (g:=braApp.site.reduce) (.inl readerKept4) (.inr ()) (.inl ()) (emptyCro 1))
  apply Labelling.cons (by rw [final_reader];exact LabelledTurn.transparent (g:=braApp.site.reduce) _ true Context.empty)
  exact .cons (by rw [final_reader_finish];exact LabelledTurn.transparent (g:=braApp.site.reduce) _ false Context.empty) (.single _ _)

theorem finalWord : accessWord braApp.site.reduce finalEdges=[.arg] := rfl

theorem finalFinish : finalEdges.getLast?=some (braApp.site.reduce.wire (.inl ⟨.inl copiedLambda4,.inl ()⟩)) := by
  have inverse:=congrArg braApp.site.reduce.wire final_context_finish
  simp only [Pairing.involutive] at inverse
  simpa only [finalEdges,List.getLast?_cons_cons,List.getLast?_singleton] using congrArg some inverse

noncomputable def finalParent : RootAccess braApp.site.reduce (.inl ()) := by
  let flow := Classical.choose app_certified
  exact ⟨finalEdges,⟨⟨⟨Context.empty,Context.empty,finalLabels⟩,
    finalLabels.root_forward_of_flow flow (.inl ()) rfl rfl⟩,rfl,⟨.lam,by
      unfold accessKind;rw [finalFinish]
      simp only [Option.bind_some,Pairing.involutive];rfl⟩⟩⟩

#print axioms thirdParent
#print axioms finalParent
#print axioms finalLabels
#print axioms finalFinish
end Lamping.Checks.BraArgumentParent
