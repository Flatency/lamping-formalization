import Lamping.Checks.OldChainBetaFixture
import Lamping.Checks.FanBodyContextNextSlots
import Lamping.Lamping.PhysicalCorridorPresentation
import Lamping.Lamping.ActionMatching
import Lamping.Lamping.GraphRootInputPreservation
import Lamping.Lamping.ReachableTransparency
namespace Lamping.Checks.FanBodyDoubleLambdaReachable
open AG Graph Lambda Lambda.Labelled
abbrev term := FanBodyContextConsumer.bare
abbrev original := FanBodyContextConsumer.original
abbrev current := FanBodyContextConsumer.current
abbrev net := (encode 0 term).net
def app : (encode 0 term).N := .inl (.inl ())
def lam : (encode 0 term).N := .inr (.inl (.inl ()))
def wire : (encode 0 term).W := .inr (.inl (.inl ()))
def corridor : TransparentCorridor net where
  first := ⟨app,.inl ()⟩
  last := ⟨lam,.inl ()⟩
  edges := [.inl ⟨app,.inl ()⟩,.inr (.inr (wire,true))]
  start := rfl
  finish := rfl
  transparent := by
    intro e f member
    have same := List.mem_singleton.mp member
    cases same
    exact ⟨wire,false,rfl,rfl⟩
def parent : RootAccess net (.inl ()) :=
  ⟨[.inr (.inl (.inl ()))],⟨⟨⟨Context.empty,Context.empty,.single _ _⟩,.single _⟩,rfl,⟨.app,rfl⟩⟩⟩
theorem principalLabels (a : Context) : Labelling net corridor.edges a a :=
  .cons (LabelledTurn.transparent (g:=net) wire false a) (.single _ _)
theorem principalForward : Forward net corridor.edges :=
  .transparent wire false rfl rfl (.single _)
def childEdges : List (Endpoint net) := [.inr (.inl (.inl ())),.inl ⟨app,.inl ()⟩,.inr (.inr (wire,true))]
theorem childLabels : Labelling net childEdges Context.empty Context.empty :=
  .cons (LabelledTurn.node (g:=net) app appCtx (.inl ()) (.direct (.appFun _))) (principalLabels _)
def child : RootAccess net (.inl ()) :=
  ⟨childEdges,⟨⟨⟨_,_,childLabels⟩,
    .node app appCtx (.inl ()) rfl rfl ⟨rfl,Or.inl rfl⟩ principalForward⟩,rfl,⟨.lam,rfl⟩⟩⟩
def redex : RedexOcc term := ⟨[],_,rfl,True.intro⟩
def rich : ActualRedexAccess net (.inl ()) redex where
  connection := {
    app := app,lam := lam,appPort := .inl (),lamPort := .inl (),appIndex := 0,lamIndex := 0
    appLabel := rfl,lamLabel := rfl,appPrincipal := HEq.rfl,lamPrincipal := HEq.rfl
    edges := corridor.edges,proper := ⟨⟨Context.empty,Context.empty,principalLabels _⟩,principalForward⟩,start := rfl,finish := rfl,emptyWord := rfl }
  parent := parent
  child := child
  ctx := appCtx
  contextPrincipal := HEq.rfl
  parentWord := rfl
  childWord := rfl
  parentFinish := rfl
  split := rfl
noncomputable def concrete := PhysicalCorridorPresentation.of_corridor net (.beta 0)
  corridor app lam (by intro h;cases h) rfl rfl (.inl ()) (.inl ()) HEq.rfl HEq.rfl rfl rfl

theorem actual_root_member : []∈physicalBetaFiberPaths net (.inl ()) term app lam :=
  (mem_physicalBetaFiberPaths net (.inl ()) term app lam []).mpr ⟨redex,rich,rfl,rfl,rfl⟩
theorem actual_fiber : concrete.site.betaSyntaxFiber (.inl ()) term=[[]] := by
  rw [concrete.betaSyntaxFiber_eq]
  let test := physicalBetaTest net (.inl ()) term app lam
  have yes : test []=true := (List.mem_filter.mp actual_root_member).2
  change ([[]] : List Path).filter test=[[]]
  simp [yes]

def endpoint : Marked := .app [] (.lam (.lam (.var 1))) (.lam (.lam (.var 1)))
theorem relative : Marked.RelativeHistory [[]]
    (Marked.mark (concrete.site.betaSyntaxFiber (.inl ()) term) term) endpoint := by
  rw [actual_fiber]
  exact .cons (.root _ _ _) (.nil _)

theorem beta_matches : Matches concrete.site.reduce (.inl ()) current.erase := by
  obtain ⟨flow⟩ := encode_flowBalance term 0
  obtain ⟨balance⟩ := encode_indexed_balance term 0
  exact concrete.site.beta_complete_matches FanBodyContextConsumer.initial FanBodyContextConsumer.closed
    (concrete.sourceIso.matches (encode_closed_matches term FanBodyContextConsumer.closed 0))
    (concrete.sourceIso.rootInputs (encode_closed_independence term FanBodyContextConsumer.closed 0).rootInputs)
    (concrete.sourceIso.flowBalance flow) rfl
    (concrete.sourceIso.indexed_balance balance) rfl
    (concrete.sourceIso.transparency (encode_closed_transparency term FanBodyContextConsumer.closed 0))
    relative (by simp [endpoint,Marked.Normal]) FanBodyContextConsumer.actualHistory
#print axioms concrete
#print axioms actual_fiber
#print axioms beta_matches


def sharedInput : Shared (.var 0) (.var 0) := ⟨⟨0,rfl⟩,rfl⟩
def oldFan : (encode 0 term).N := .inr (.inl (.inr (.inl (.inr (.inr sharedInput)))))
def oldArgLam : (encode 0 term).N := .inr (.inr (.inl ()))
def fanKept : RemainingNodes app lam := ⟨oldFan,by constructor <;> intro h <;> cases h⟩
def argKept : RemainingNodes app lam := ⟨oldArgLam,by constructor <;> intro h <;> cases h⟩
theorem actual_kept_fan_label : concrete.kept fanKept=label .fan 0 := rfl
theorem actual_kept_arg_label : concrete.kept argKept=label .lam 1 := rfl

def bindingWire : (encode 0 term).W := .inl (.inr (.inl (.inr (.inr ⟨0,Or.inr rfl⟩))))
def argumentWire : (encode 0 term).W := .inr (.inr (.inl ()))
theorem old_fan_wire : net.wire (.inl ⟨oldFan,.inl ()⟩)=.inr (.inr (bindingWire,true)) := rfl
theorem old_binding_finish : net.wire (.inr (.inr (bindingWire,false)))=.inl ⟨lam,lamBind⟩ := rfl

def outsideBinding : concrete.Outside := ⟨bindingWire,by
  rintro ⟨d,h⟩;simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h <;> cases h⟩
def outsideArg : concrete.Outside := ⟨argumentWire,by
  rintro ⟨d,h⟩;simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h <;> cases h⟩
theorem site_fan_wire : concrete.site.net.wire (.inl ⟨.inl fanKept,.inl ()⟩)=.inr (.inr (.inl outsideBinding,true)) := by
  apply concrete.sourceIso.symm.ends.injective;rw [concrete.sourceIso.symm.wiring];rfl
theorem site_bind_wire : concrete.site.net.wire (.inr (.inr (.inl outsideBinding,false)))=.inl ⟨.inr (.inr ()),lamBind⟩ := by
  apply concrete.sourceIso.symm.ends.injective;rw [concrete.sourceIso.symm.wiring];rfl
theorem site_arg_wire : concrete.site.net.wire (.inl ⟨.inr (.inl ()),appArg⟩)=.inr (.inr (.inl outsideArg,false)) := by
  apply concrete.sourceIso.symm.ends.injective;rw [concrete.sourceIso.symm.wiring];rfl
theorem site_arg_finish : concrete.site.net.wire (.inr (.inr (.inl outsideArg,true)))=.inl ⟨.inl argKept,.inl ()⟩ := by
  apply concrete.sourceIso.symm.ends.injective;rw [concrete.sourceIso.symm.wiring];rfl
noncomputable abbrev actualCut := cutFragment concrete.site.net (pathPartition (Schema.beta 0) concrete.Inside) concrete.site.closed

theorem cut_fan_wire : actualCut.wire (.inl ⟨fanKept,.inl ()⟩)=.inr (.inr (outsideBinding,true)) := by
  apply concrete.site.outsideEnd_injective;exact (concrete.site.outsideEnd_wire _).symm.trans site_fan_wire
theorem cut_bind_wire : actualCut.wire (.inr (.inr (outsideBinding,false)))=.inr (.inl (.inr (.inr false))) := by
  apply concrete.site.outsideEnd_injective;exact (concrete.site.outsideEnd_wire _).symm.trans site_bind_wire
theorem cut_arg_wire : actualCut.wire (.inr (.inl (.inr (.inl true))))=.inr (.inr (outsideArg,false)) := by
  apply concrete.site.outsideEnd_injective;exact (concrete.site.outsideEnd_wire _).symm.trans site_arg_wire
theorem cut_arg_finish : actualCut.wire (.inr (.inr (outsideArg,true)))=.inl ⟨argKept,.inl ()⟩ := by
  apply concrete.site.outsideEnd_injective;exact (concrete.site.outsideEnd_wire _).symm.trans site_arg_finish
noncomputable def rhsFan : concrete.Kept⊕Empty := .inl fanKept
noncomputable def rhsLambda : concrete.Kept⊕Empty := .inl argKept
noncomputable def fanPrincipal : Endpoint concrete.site.reduce := .inl ⟨rhsFan,.inl ()⟩
noncomputable def step1 : Endpoint concrete.site.reduce := .inr (.inr (.inl (.inl outsideBinding),false))
noncomputable def step2 : Endpoint concrete.site.reduce := .inr (.inr (.inr (.inr false),true))
noncomputable def step3 : Endpoint concrete.site.reduce := .inr (.inr (.inr (.inl true),false))
noncomputable def step4 : Endpoint concrete.site.reduce := .inr (.inr (.inl (.inl outsideArg),true))
theorem target_fan_wire : concrete.site.reduce.wire fanPrincipal=.inr (.inr (.inl (.inl outsideBinding),true)) :=
  (plugLeft_wire actualCut (Schema.beta 0).right.net (.inl ⟨fanKept,.inl ()⟩)).trans
    (congrArg (AG.plugLeft actualCut (Schema.beta 0).right.net) cut_fan_wire)
theorem target_bind_wire : concrete.site.reduce.wire step1=.inr (.inr (.inr (.inr false),false)) :=
  (plugLeft_wire actualCut (Schema.beta 0).right.net (.inr (.inr (outsideBinding,false)))).trans
    (congrArg (AG.plugLeft actualCut (Schema.beta 0).right.net) cut_bind_wire)
theorem target_glue : concrete.site.reduce.wire step2=.inr (.inr (.inr (.inl true),true)) := rfl
theorem target_arg_wire : concrete.site.reduce.wire step3=.inr (.inr (.inl (.inl outsideArg),false)) :=
  (plugLeft_wire actualCut (Schema.beta 0).right.net (.inr (.inl (.inr (.inl true))))).trans
    (congrArg (AG.plugLeft actualCut (Schema.beta 0).right.net) cut_arg_wire)
theorem target_finish : concrete.site.reduce.wire step4=.inl ⟨rhsLambda,.inl ()⟩ :=
  (plugLeft_wire actualCut (Schema.beta 0).right.net (.inr (.inr (outsideArg,true)))).trans
    (congrArg (AG.plugLeft actualCut (Schema.beta 0).right.net) cut_arg_finish)
noncomputable def outerCorridor : TransparentCorridor concrete.site.reduce where
  first := ⟨rhsFan,.inl ()⟩
  last := ⟨rhsLambda,.inl ()⟩
  edges := [fanPrincipal,step1,step2,step3,step4]
  start := rfl
  finish := by
    have h:=congrArg concrete.site.reduce.wire target_finish
    simp only [Pairing.involutive] at h
    exact congrArg some h
  transparent := by
    intro e f member
    simp only [List.tail_cons,List.zip_cons_cons,List.zip_nil_right,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h|h|h|h
    · cases h;exact ⟨.inl (.inl outsideBinding),true,target_fan_wire,rfl⟩
    · cases h;exact ⟨.inr (.inr false),false,target_bind_wire,rfl⟩
    · cases h;exact ⟨.inr (.inl true),true,target_glue,rfl⟩
    · cases h;exact ⟨.inl (.inl outsideArg),false,target_arg_wire,rfl⟩
noncomputable def outerFan := PhysicalCorridorPresentation.of_corridor concrete.site.reduce
  (.fanAction .lam 0 1 (by decide)) outerCorridor rhsFan rhsLambda
  (by intro h;have same:=congrArg Subtype.val (Sum.inl.inj h);cases same)
  rfl rfl (.inl ()) (.inl ()) HEq.rfl HEq.rfl rfl rfl
#print axioms outerFan

def oldInnerLambda : (encode 0 term).N := .inr (.inr (.inr (.inl (.inl ()))))
def innerKept : concrete.Kept := ⟨oldInnerLambda,by constructor <;> intro h <;> cases h⟩
def bodyWire : (encode 0 term).W := .inl (.inr (.inr (.inr (.inl ()))))
theorem old_body_start : net.wire (.inl ⟨oldArgLam,lamBody⟩)=.inr (.inr (bodyWire,false)) := rfl
theorem old_body_finish : net.wire (.inr (.inr (bodyWire,true)))=.inl ⟨oldInnerLambda,.inl ()⟩ := by
  have h : net.wire (.inl ⟨oldInnerLambda,.inl ()⟩)=.inr (.inr (bodyWire,true)) := rfl
  exact (congrArg net.wire h).symm.trans (net.wire.involutive _)
def outsideBody : concrete.Outside := ⟨bodyWire,by
  rintro ⟨d,h⟩;simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h <;> cases h⟩
theorem beta_lift_wire (e f : Endpoint actualCut)
    (h : net.wire (concrete.sourceIso.symm.ends (concrete.site.outsideEnd e))=
      concrete.sourceIso.symm.ends (concrete.site.outsideEnd f)) :
    concrete.site.reduce.wire (AG.plugLeft actualCut (Schema.beta 0).right.net e)=
      AG.plugLeft actualCut (Schema.beta 0).right.net f := by
  have old : concrete.site.net.wire (concrete.site.outsideEnd e)=concrete.site.outsideEnd f := by
    apply concrete.sourceIso.symm.ends.injective
    rw [concrete.sourceIso.symm.wiring];exact h
  have cut : actualCut.wire e=f := concrete.site.outsideEnd_injective
    ((concrete.site.outsideEnd_wire e).symm.trans old)
  exact (plugLeft_wire actualCut (Schema.beta 0).right.net e).trans
    (congrArg (AG.plugLeft actualCut (Schema.beta 0).right.net) cut)
theorem beta_body_start : concrete.site.reduce.wire (.inl ⟨rhsLambda,lamBody⟩)=
    .inr (.inr (.inl (.inl outsideBody),false)) :=
  beta_lift_wire (.inl ⟨argKept,lamBody⟩) (.inr (.inr (outsideBody,false))) old_body_start
theorem beta_body_finish : concrete.site.reduce.wire (.inr (.inr (.inl (.inl outsideBody),true)))=
    .inl ⟨.inl innerKept,.inl ()⟩ :=
  beta_lift_wire (.inr (.inr (outsideBody,true))) (.inl ⟨innerKept,.inl ()⟩) old_body_finish

def innerKept2 : outerFan.Kept := ⟨.inl innerKept,by
  constructor
  · intro h;have same:=congrArg Subtype.val (Sum.inl.inj h);cases same
  · intro h;have same:=congrArg Subtype.val (Sum.inl.inj h);cases same⟩
def outsideBody2 : outerFan.Outside := ⟨.inl (.inl outsideBody),by
  rintro ⟨d,h⟩
  simp only [outerCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h <;> cases h⟩
noncomputable abbrev cut2 : Net signature outerFan.Kept (Boundary term⊕(Bool⊕Bool)) outerFan.Outside :=
  cutFragment outerFan.site.net (pathPartition (Schema.fanAction .lam 0 1 (by decide)) outerFan.Inside) outerFan.site.closed

theorem outside2_injective : Function.Injective outerFan.site.outsideEnd := by
  intro e f same
  let split := fragmentEnd (B:=Boundary term) (W:=outerFan.Outside) outerFan.site.net.label
    (pathPartition (Schema.fanAction .lam 0 1 (by decide)) outerFan.Inside)
  change split.invFun (.inl e)=split.invFun (.inl f) at same
  have mapped:=congrArg split same
  simpa only [split.right_inv,Sum.inl.injEq] using mapped

theorem outer_lift_wire (e f : Endpoint cut2)
    (h : concrete.site.reduce.wire (outerFan.sourceIso.symm.ends (outerFan.site.outsideEnd e))=
      outerFan.sourceIso.symm.ends (outerFan.site.outsideEnd f)) :
    outerFan.site.reduce.wire (AG.plugLeft cut2 (Schema.fanAction .lam 0 1 (by decide)).right.net e)=
      AG.plugLeft cut2 (Schema.fanAction .lam 0 1 (by decide)).right.net f := by
  have old : outerFan.site.net.wire (outerFan.site.outsideEnd e)=outerFan.site.outsideEnd f := by
    apply outerFan.sourceIso.symm.ends.injective
    rw [outerFan.sourceIso.symm.wiring];exact h
  have cut : cut2.wire e=f := outside2_injective ((outerFan.site.outsideEnd_wire e).symm.trans old)
  exact (plugLeft_wire cut2 (Schema.fanAction .lam 0 1 (by decide)).right.net e).trans
    (congrArg (AG.plugLeft cut2 (Schema.fanAction .lam 0 1 (by decide)).right.net) cut)
noncomputable def innerFanNode : outerFan.Kept⊕(Bool⊕Bool) := .inr (.inr true)
noncomputable def innerLambdaNode : outerFan.Kept⊕(Bool⊕Bool) := .inl innerKept2
theorem inner_fan_label : outerFan.site.reduce.label innerFanNode=label .fan 0 := rfl
theorem inner_lambda_label : outerFan.site.reduce.label innerLambdaNode=label .lam 1 := rfl
noncomputable def innerPrincipal : Endpoint outerFan.site.reduce := .inl ⟨innerFanNode,.inl ()⟩
noncomputable def innerStep : Endpoint outerFan.site.reduce := .inr (.inr (.inl (.inl outsideBody2),true))
noncomputable def innerGlue : Endpoint outerFan.site.reduce := .inr (.inr (.inr (.inr true),false))
theorem inner_start_wire : outerFan.site.reduce.wire innerPrincipal=
    .inr (.inr (.inr (.inr true),true)) := rfl
theorem inner_glue_wire : outerFan.site.reduce.wire innerGlue=
    .inr (.inr (.inl (.inl outsideBody2),false)) :=
  outer_lift_wire (.inr (.inl (.inr (.inr true)))) (.inr (.inr (outsideBody2,false))) beta_body_start
theorem inner_finish_wire : outerFan.site.reduce.wire innerStep=.inl ⟨innerLambdaNode,.inl ()⟩ :=
  outer_lift_wire (.inr (.inr (outsideBody2,true))) (.inl ⟨innerKept2,.inl ()⟩) beta_body_finish
noncomputable def innerCorridor : TransparentCorridor outerFan.site.reduce where
  first := ⟨innerFanNode,.inl ()⟩
  last := ⟨innerLambdaNode,.inl ()⟩
  edges := [innerPrincipal,innerGlue,innerStep]
  start := rfl
  finish := by
    have h:=congrArg outerFan.site.reduce.wire inner_finish_wire
    simp only [Pairing.involutive] at h
    exact congrArg some h
  transparent := by
    intro e f member
    simp only [List.tail_cons,List.zip_cons_cons,List.zip_nil_right,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h|h
    · cases h;exact ⟨.inr (.inr true),true,inner_start_wire,rfl⟩
    · cases h;exact ⟨.inl (.inl outsideBody2),false,inner_glue_wire,rfl⟩
noncomputable def innerFan := PhysicalCorridorPresentation.of_corridor outerFan.site.reduce
  (.fanAction .lam 0 1 (by decide)) innerCorridor innerFanNode innerLambdaNode
  (by intro h;cases h) inner_fan_label inner_lambda_label (.inl ()) (.inl ()) HEq.rfl HEq.rfl rfl rfl
#print axioms inner_fan_label
#print axioms inner_lambda_label
#print axioms innerFan
def Certified (g : ActualNet (Boundary term)) : Prop :=
  ∃ (_flow : FlowBalance g.net initialBoundaryPolarity)
    (_balance : IndexedLevelBalance g.net (boundaryDepthAt 0)),
    RootInputs g.net (.inl ()) ∧ Transparency g.net (.inl ()) ∧ Matches g.net (.inl ()) current.erase
theorem beta_certified : Certified (ActualNet.ofNet concrete.site.reduce) := by
  obtain ⟨flow⟩ := encode_flowBalance term 0
  obtain ⟨balance⟩ := encode_indexed_balance term 0
  obtain ⟨nextFlow⟩ := concrete.graph_step.flowBalance flow
  obtain ⟨nextBalance⟩ := concrete.graph_step.indexed_balance balance
  exact ⟨nextFlow,nextBalance,
    concrete.graph_step.rootInputs flow rfl balance rfl
      (encode_closed_independence term FanBodyContextConsumer.closed 0).rootInputs
      (encode_closed_transparency term FanBodyContextConsumer.closed 0) (encode_closed_matches term FanBodyContextConsumer.closed 0),
    concrete.graph_step.transparency_indexed flow rfl balance rfl (encode_closed_transparency term FanBodyContextConsumer.closed 0),
    beta_matches⟩
theorem action_certified {g h : ActualNet (Boundary term)} {s : Schema}
    (step : GraphStep s g h) (action : IsAction s) (old : Certified g) : Certified h := by
  obtain ⟨flow,balance,inputs,transparency,matching⟩ := old
  obtain ⟨nextFlow⟩ := step.flowBalance flow
  obtain ⟨nextBalance⟩ := step.indexed_balance balance
  exact ⟨nextFlow,nextBalance,step.rootInputs flow rfl balance rfl inputs transparency matching,
    step.transparency_indexed flow rfl balance rfl transparency,
    step.action_matches_rootInputs action flow rfl balance rfl inputs transparency matching⟩
theorem outer_certified : Certified (ActualNet.ofNet outerFan.site.reduce) :=
  action_certified outerFan.graph_step (.fan .lam 0 1 (by decide)) beta_certified

theorem inner_certified : Certified (ActualNet.ofNet innerFan.site.reduce) :=
  action_certified innerFan.graph_step (.fan .lam 0 1 (by decide)) outer_certified

theorem actual_three_step_trace : GraphTrace (ActualNet.initial term) (ActualNet.ofNet innerFan.site.reduce)
    [.beta 0,.fanAction .lam 0 1 (by decide),.fanAction .lam 0 1 (by decide)] :=
  .cons concrete.graph_step (.cons outerFan.graph_step (.cons innerFan.graph_step (.refl _)))
theorem actual_inner_source_matches : Matches innerFan.site.net (.inl ()) current.erase := by
  obtain ⟨_,_,_,_,matching⟩ := outer_certified
  exact innerFan.sourceIso.matches matching
theorem actual_final_matches : Matches innerFan.site.reduce (.inl ()) current.erase := by
  obtain ⟨_,_,_,_,matching⟩ := inner_certified
  exact matching
#print axioms actual_three_step_trace
#print axioms actual_inner_source_matches
#print axioms actual_final_matches
end Lamping.Checks.FanBodyDoubleLambdaReachable