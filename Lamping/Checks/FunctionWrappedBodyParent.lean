import Lamping.Checks.FunctionWrappedReachable
set_option maxHeartbeats 4000000
namespace Lamping.Checks.FunctionWrappedBodyParent
open AG Graph Lambda Lambda.Labelled FunctionWrappedReachable

def bodyRootWire : (encode 0 term).W := wrapArgWire (.inr (.inl ()))
def bodyRootOutside : concrete.Outside := ⟨bodyRootWire,by
  rintro ⟨d,h⟩;simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h <;> cases h⟩
theorem beta_body_start : concrete.site.reduce.wire (.inl ⟨rhsLambda,lamBody⟩)=
    .inr (.inr (.inl (.inl bodyRootOutside),false)) :=
  beta_lift_wire (.inl ⟨argKept,lamBody⟩) (.inr (.inr (bodyRootOutside,false))) rfl
theorem beta_body_finish : concrete.site.reduce.wire (.inr (.inr (.inl (.inl bodyRootOutside),true)))=
    .inl ⟨.inl appKept,appCtx⟩ :=
  beta_lift_wire (.inr (.inr (bodyRootOutside,true))) (.inl ⟨appKept,appCtx⟩) rfl
def bodyRootOutside2 : croLambda.Outside := ⟨.inl (.inl bodyRootOutside),by
  rintro ⟨d,h⟩
  simp only [actualCroLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h <;> cases h⟩
theorem lambda_body_exit : croLambda.site.reduce.wire
    (.inr (.inr (.inr (.inr true),false)))=
    .inr (.inr (.inl (.inl bodyRootOutside2),false)) :=
  action2_lift_wire (.inr (.inl (.inr (.inr true))))
    (.inr (.inr (bodyRootOutside2,false))) beta_body_start
theorem lambda_body_finish : croLambda.site.reduce.wire
    (.inr (.inr (.inl (.inl bodyRootOutside2),true)))=.inl ⟨.inl appKept2,appCtx⟩ :=
  action2_lift_wire (.inr (.inr (bodyRootOutside2,true))) (.inl ⟨appKept2,appCtx⟩) beta_body_finish
def copiedLambda3 : croCro.Kept := ⟨.inr (.inl ()),by constructor <;> intro h <;> cases h⟩
def bodyControl3 : croCro.Kept := ⟨.inr (.inr true),by constructor <;> intro h <;> cases h⟩
def bodyFrontOutside3 : croCro.Outside := ⟨.inr (.inr true),by
  rintro ⟨d,h⟩
  simp only [actualCroCroCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h <;> cases h⟩
def bodyRootOutside3 : croCro.Outside := ⟨.inl (.inl bodyRootOutside2),by
  rintro ⟨d,h⟩
  simp only [actualCroCroCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h <;> cases h⟩
theorem third_body_start : croCro.site.reduce.wire (.inl ⟨.inl copiedLambda3,lamBody⟩)=
    .inl ⟨.inl bodyControl3,.inr ()⟩ :=
  action3_lift_wire (.inl ⟨copiedLambda3,lamBody⟩) (.inl ⟨bodyControl3,.inr ()⟩) rfl
theorem third_body_control : croCro.site.reduce.wire (.inl ⟨.inl bodyControl3,.inl ()⟩)=
    .inr (.inr (.inl (.inl bodyFrontOutside3),true)) :=
  action3_lift_wire (.inl ⟨bodyControl3,.inl ()⟩) (.inr (.inr (bodyFrontOutside3,true))) rfl
theorem third_body_exit : croCro.site.reduce.wire
    (.inr (.inr (.inl (.inl bodyFrontOutside3),false)))=
    .inr (.inr (.inl (.inl bodyRootOutside3),false)) :=
  action3_lift_wire (.inr (.inr (bodyFrontOutside3,false)))
    (.inr (.inr (bodyRootOutside3,false))) lambda_body_exit
theorem third_body_finish : croCro.site.reduce.wire
    (.inr (.inr (.inl (.inl bodyRootOutside3),true)))=.inl ⟨passiveApp,appCtx⟩ :=
  action3_lift_wire (.inr (.inr (bodyRootOutside3,true))) (.inl ⟨appKept3,appCtx⟩) lambda_body_finish

def copiedLambda4 : croApp.Kept := ⟨.inl copiedLambda3,by constructor <;> intro h <;> cases h⟩
def bodyControl4 : croApp.Kept := ⟨.inl bodyControl3,by constructor <;> intro h <;> cases h⟩
def bodyFrontOutside4 : croApp.Outside := ⟨.inl (.inl bodyFrontOutside3),by
  rintro ⟨d,h⟩
  simp only [actualCroAppCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h <;> cases h⟩
def bodyRootOutside4 : croApp.Outside := ⟨.inl (.inl bodyRootOutside3),by
  rintro ⟨d,h⟩
  simp only [actualCroAppCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h <;> cases h⟩
noncomputable abbrev cut4 : Net signature croApp.Kept (Boundary term⊕(Unit⊕Bool)) croApp.Outside :=
  cutFragment croApp.site.net (pathPartition (Schema.croAction .app 0 1 (by decide)) croApp.Inside) croApp.site.closed
theorem outside4_injective : Function.Injective croApp.site.outsideEnd := by
  intro e f same
  let split := fragmentEnd (B:=Boundary term) (W:=croApp.Outside) croApp.site.net.label
    (pathPartition (Schema.croAction .app 0 1 (by decide)) croApp.Inside)
  change split.invFun (.inl e)=split.invFun (.inl f) at same
  have mapped:=congrArg split same
  simpa only [split.right_inv,Sum.inl.injEq] using mapped
theorem action4_lift_wire (e f : Endpoint cut4)
    (h : croCro.site.reduce.wire (croApp.sourceIso.symm.ends (croApp.site.outsideEnd e))=
      croApp.sourceIso.symm.ends (croApp.site.outsideEnd f)) :
    croApp.site.reduce.wire (AG.plugLeft cut4 (Schema.croAction .app 0 1 (by decide)).right.net e)=
      AG.plugLeft cut4 (Schema.croAction .app 0 1 (by decide)).right.net f := by
  have old : croApp.site.net.wire (croApp.site.outsideEnd e)=croApp.site.outsideEnd f := by
    apply croApp.sourceIso.symm.ends.injective
    rw [croApp.sourceIso.symm.wiring];exact h
  have cut : cut4.wire e=f := outside4_injective ((croApp.site.outsideEnd_wire e).symm.trans old)
  exact (plugLeft_wire cut4 (Schema.croAction .app 0 1 (by decide)).right.net e).trans
    (congrArg (AG.plugLeft cut4 (Schema.croAction .app 0 1 (by decide)).right.net) cut)

noncomputable abbrev finalNet := croApp.site.reduce
noncomputable def finalLambda : croApp.Kept⊕(Unit⊕Bool) := .inl copiedLambda4
noncomputable def finalBodyControl : croApp.Kept⊕(Unit⊕Bool) := .inl bodyControl4
theorem final_body_start : finalNet.wire (.inl ⟨finalLambda,lamBody⟩)=
    .inl ⟨finalBodyControl,.inr ()⟩ :=
  action4_lift_wire (.inl ⟨copiedLambda4,lamBody⟩) (.inl ⟨bodyControl4,.inr ()⟩) third_body_start
theorem final_body_control : finalNet.wire (.inl ⟨finalBodyControl,.inl ()⟩)=
    .inr (.inr (.inl (.inl bodyFrontOutside4),true)) :=
  action4_lift_wire (.inl ⟨bodyControl4,.inl ()⟩) (.inr (.inr (bodyFrontOutside4,true))) third_body_control
theorem final_body_exit : finalNet.wire (.inr (.inr (.inl (.inl bodyFrontOutside4),false)))=
    .inr (.inr (.inl (.inl bodyRootOutside4),false)) :=
  action4_lift_wire (.inr (.inr (bodyFrontOutside4,false)))
    (.inr (.inr (bodyRootOutside4,false))) third_body_exit
theorem final_body_arrive : finalNet.wire (.inr (.inr (.inl (.inl bodyRootOutside4),true)))=
    .inr (.inr (.inr (.inr false),false)) :=
  action4_lift_wire (.inr (.inr (bodyRootOutside4,true)))
    (.inr (.inl (.inr (.inr false)))) third_body_finish
theorem final_reader_arrive : finalNet.wire (.inr (.inr (.inr (.inr false),true)))=
    .inl ⟨.inr (.inr false),.inl ()⟩ := rfl
theorem final_app_finish : finalNet.wire (.inl ⟨.inr (.inr false),.inr ()⟩)=
    .inl ⟨.inr (.inl ()),appCtx⟩ := rfl
#print axioms final_body_start
#print axioms final_app_finish

noncomputable def bodyEdges : List (Endpoint finalNet) := [
  .inl ⟨finalLambda,lamBody⟩,
  .inl ⟨finalBodyControl,.inl ()⟩,
  .inr (.inr (.inl (.inl bodyFrontOutside4),false)),
  .inr (.inr (.inl (.inl bodyRootOutside4),true)),
  .inr (.inr (.inr (.inr false),true)),
  .inl ⟨.inr (.inr false),.inr ()⟩]
theorem bodyLabels (a : Context) : Labelling finalNet bodyEdges a a := by
  apply Labelling.cons (by rw [final_body_start];exact LabelledTurn.node (g:=finalNet) finalBodyControl _ _ (.direct (InitialOffsets.Event.apply_rel (.cro 0) a)))
  apply Labelling.cons (by rw [final_body_control];exact LabelledTurn.transparent (g:=finalNet) (.inl (.inl bodyFrontOutside4)) true _)
  apply Labelling.cons (by rw [final_body_exit];exact LabelledTurn.transparent (g:=finalNet) (.inl (.inl bodyRootOutside4)) false _)
  apply Labelling.cons (by rw [final_body_arrive];exact LabelledTurn.transparent (g:=finalNet) (.inr (.inr false)) false _)
  exact .cons (by rw [final_reader_arrive];exact LabelledTurn.node (g:=finalNet) (.inr (.inr false)) _ _ (.inverse (InitialOffsets.Event.apply_rel (.cro 0) a))) (.single _ _)
theorem bodyWord : bodyEdges.flatMap (arrivalWord finalNet)=[.body] := rfl
theorem bodyHead : bodyEdges.head?=some (.inl ⟨finalLambda,lamBody⟩) := rfl
theorem bodyFinish : bodyEdges.getLast?=some (finalNet.wire (.inl ⟨.inr (.inl ()),appCtx⟩)) := by
  change some (.inl ⟨.inr (.inr false),.inr ()⟩ : Endpoint finalNet)=_
  have h:=congrArg finalNet.wire final_app_finish
  simp only [Pairing.involutive] at h
  exact congrArg some h.symm
#print axioms bodyLabels
#print axioms bodyWord
end Lamping.Checks.FunctionWrappedBodyParent
