import Lamping.Checks.FanSuccessfulReachable
import Lamping.Lamping.PhysicalCorridorPresentation
namespace Lamping.Checks.FanAppSuccessfulReachable
open AG Graph Lambda Lambda.Labelled FanSuccessfulReachable
open FanSuccessfulChains hiding original current

def originalArgApp : (encode 1 argument).N := .inr (.inl (.inl ()))
def oldArgApp : (encode 0 term).N := .inr (.inl (.inr (.inr originalArgApp)))
def argFunctionWire : (encode 0 term).W := wrapArgWire (.inl (.inr (.inr (.inl (.inl ())))))

theorem original_app_label : net.label oldArgApp=label .app 1 := rfl
theorem original_var_aux_wire : net.wire (.inl ⟨oldArgVar,.inr ()⟩)=.inr (.inr (argFunctionWire,true)) := rfl
theorem original_app_fn_wire : net.wire (.inr (.inr (argFunctionWire,false)))=.inl ⟨oldArgApp,.inl ()⟩ := by
  have h : net.wire (.inl ⟨oldArgApp,.inl ()⟩)=.inr (.inr (argFunctionWire,false)) := rfl
  exact (congrArg net.wire h).symm.trans (net.wire.involutive _)

def appKept : concrete.Kept := ⟨oldArgApp,by constructor <;> intro h <;> cases h⟩
def functionOutside : concrete.Outside := ⟨argFunctionWire,by
  rintro ⟨d,h⟩;simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h <;> cases h⟩

theorem beta_var_aux_wire : concrete.site.reduce.wire (.inl ⟨.inl varKept,.inr ()⟩)=
    .inr (.inr (.inl (.inl functionOutside),true)) :=
  beta_lift_wire (.inl ⟨varKept,.inr ()⟩) (.inr (.inr (functionOutside,true))) original_var_aux_wire

theorem beta_app_fn_wire : concrete.site.reduce.wire (.inr (.inr (.inl (.inl functionOutside),false)))=
    .inl ⟨.inl appKept,.inl ()⟩ :=
  beta_lift_wire (.inr (.inr (functionOutside,false))) (.inl ⟨appKept,.inl ()⟩) original_app_fn_wire

def appKept2 : actualFanPresentation.Kept := ⟨.inl appKept,by
  constructor <;> intro h <;> have same:=congrArg Subtype.val (Sum.inl.inj h) <;> cases same⟩
def functionOutside2 : actualFanPresentation.Outside := ⟨.inl (.inl functionOutside),by
  rintro ⟨d,h⟩
  simp only [actualFanLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h|h <;> cases h⟩

theorem lambda_var_aux_wire : actualFanPresentation.site.reduce.wire (.inl ⟨passiveVar,.inr ()⟩)=
    .inr (.inr (.inl (.inl functionOutside2),true)) :=
  action2_lift_wire (.inl ⟨varKept2,.inr ()⟩) (.inr (.inr (functionOutside2,true))) beta_var_aux_wire

theorem lambda_app_fn_wire : actualFanPresentation.site.reduce.wire
    (.inr (.inr (.inl (.inl functionOutside2),false)))=.inl ⟨.inl appKept2,.inl ()⟩ :=
  action2_lift_wire (.inr (.inr (functionOutside2,false))) (.inl ⟨appKept2,.inl ()⟩) beta_app_fn_wire

def appKept3 : fanCro.Kept := ⟨.inl appKept2,by
  constructor
  · intro h;cases h
  · intro h;have same:=congrArg Subtype.val (Sum.inl.inj h)
    have prior:=congrArg Subtype.val (Sum.inl.inj same)
    cases prior⟩
def functionOutside3 : fanCro.Outside := ⟨.inl (.inl functionOutside2),by
  rintro ⟨d,h⟩
  simp only [actualFanCroCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h <;> cases h⟩
noncomputable abbrev cut3 : Net signature fanCro.Kept (Boundary term⊕(Bool⊕Unit)) fanCro.Outside := cutFragment fanCro.site.net
  (pathPartition (Schema.fanAction .cro 0 1 (by decide)) fanCro.Inside) fanCro.site.closed

theorem outside3_injective : Function.Injective fanCro.site.outsideEnd := by
  intro e f same
  let split := fragmentEnd (B:=Boundary term) (W:=fanCro.Outside) fanCro.site.net.label
    (pathPartition (Schema.fanAction .cro 0 1 (by decide)) fanCro.Inside)
  change split.invFun (.inl e)=split.invFun (.inl f) at same
  have mapped:=congrArg split same
  simpa only [split.right_inv,Sum.inl.injEq] using mapped

theorem action3_lift_wire (e f : Endpoint cut3)
    (h : actualFanPresentation.site.reduce.wire (fanCro.sourceIso.symm.ends (fanCro.site.outsideEnd e))=
      fanCro.sourceIso.symm.ends (fanCro.site.outsideEnd f)) :
    fanCro.site.reduce.wire (AG.plugLeft cut3 (Schema.fanAction .cro 0 1 (by decide)).right.net e)=
      AG.plugLeft cut3 (Schema.fanAction .cro 0 1 (by decide)).right.net f := by
  have old : fanCro.site.net.wire (fanCro.site.outsideEnd e)=fanCro.site.outsideEnd f := by
    apply fanCro.sourceIso.symm.ends.injective
    rw [fanCro.sourceIso.symm.wiring];exact h
  have actual : cut3.wire e=f := outside3_injective ((fanCro.site.outsideEnd_wire e).symm.trans old)
  exact (plugLeft_wire cut3 (Schema.fanAction .cro 0 1 (by decide)).right.net e).trans
    (congrArg (AG.plugLeft cut3 (Schema.fanAction .cro 0 1 (by decide)).right.net) actual)

noncomputable def newFanNode : fanCro.Kept⊕(Bool⊕Unit) := .inr (.inr ())
noncomputable def newAppNode : fanCro.Kept⊕(Bool⊕Unit) := .inl appKept3
noncomputable def fanPrincipal : Endpoint fanCro.site.reduce := .inl ⟨newFanNode,.inl ()⟩
noncomputable def fanGlue : Endpoint fanCro.site.reduce := .inr (.inr (.inr (.inr ()),false))
noncomputable def functionStep : Endpoint fanCro.site.reduce := .inr (.inr (.inl (.inl functionOutside3),false))

theorem fan_label : fanCro.site.reduce.label newFanNode=label .fan 0 := rfl
theorem app_label : fanCro.site.reduce.label newAppNode=label .app 1 := rfl

theorem fan_start_wire : fanCro.site.reduce.wire fanPrincipal=
    .inr (.inr (.inr (.inr ()),true)) := rfl

theorem fan_glue_wire : fanCro.site.reduce.wire fanGlue=
    .inr (.inr (.inl (.inl functionOutside3),true)) :=
  action3_lift_wire (.inr (.inl (.inr (.inr ())))) (.inr (.inr (functionOutside3,true))) lambda_var_aux_wire

theorem app_finish_wire : fanCro.site.reduce.wire functionStep=.inl ⟨newAppNode,.inl ()⟩ :=
  action3_lift_wire (.inr (.inr (functionOutside3,false))) (.inl ⟨appKept3,.inl ()⟩) lambda_app_fn_wire

noncomputable def appCorridor : TransparentCorridor fanCro.site.reduce where
  first := ⟨newFanNode,.inl ()⟩
  last := ⟨newAppNode,.inl ()⟩
  edges := [fanPrincipal,fanGlue,functionStep]
  start := rfl
  finish := by
    have h:=congrArg fanCro.site.reduce.wire app_finish_wire
    simp only [Pairing.involutive] at h
    exact congrArg some h
  transparent := by
    intro e f member
    simp only [List.tail_cons,List.zip_cons_cons,List.zip_nil_right,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h|h
    · cases h;exact ⟨.inr (.inr ()),true,fan_start_wire,rfl⟩
    · cases h;exact ⟨.inl (.inl functionOutside3),true,fan_glue_wire,rfl⟩

noncomputable def fanApp := PhysicalCorridorPresentation.of_corridor fanCro.site.reduce
  (.fanAction .app 0 1 (by decide)) appCorridor newFanNode newAppNode
  (by intro h;cases h) fan_label app_label (.inl ()) (.inl ()) HEq.rfl HEq.rfl rfl rfl

theorem app_certified : Certified (ActualNet.ofNet fanApp.site.reduce) :=
  action_certified fanApp.graph_step (.fan .app 0 1 (by decide)) cro_certified

theorem actual_source_matches : Matches fanApp.site.net (.inl ()) current.erase := by
  obtain ⟨_,_,_,_,matching⟩ := cro_certified
  exact fanApp.sourceIso.matches matching

theorem actual_target_matches : Matches fanApp.site.reduce (.inl ()) current.erase := by
  obtain ⟨_,_,_,_,matching⟩ := app_certified
  exact matching

theorem actual_four_step_trace : GraphTrace (ActualNet.initial term) (ActualNet.ofNet fanApp.site.reduce)
    [.beta 0,.fanAction .lam 0 1 (by decide),.fanAction .cro 0 1 (by decide),.fanAction .app 0 1 (by decide)] :=
  .cons concrete.graph_step (.cons actualFanPresentation.graph_step (.cons fanCro.graph_step (.cons fanApp.graph_step (.refl _))))
end Lamping.Checks.FanAppSuccessfulReachable
#print axioms Lamping.Checks.FanAppSuccessfulReachable.original_app_label
#print axioms Lamping.Checks.FanAppSuccessfulReachable.original_var_aux_wire
#print axioms Lamping.Checks.FanAppSuccessfulReachable.original_app_fn_wire
#print axioms Lamping.Checks.FanAppSuccessfulReachable.fan_label
#print axioms Lamping.Checks.FanAppSuccessfulReachable.app_label
#print axioms Lamping.Checks.FanAppSuccessfulReachable.fanApp
#print axioms Lamping.Checks.FanAppSuccessfulReachable.actual_four_step_trace
#print axioms Lamping.Checks.FanAppSuccessfulReachable.actual_source_matches
#print axioms Lamping.Checks.FanAppSuccessfulReachable.actual_target_matches
