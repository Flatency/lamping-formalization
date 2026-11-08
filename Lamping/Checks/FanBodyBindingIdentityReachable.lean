import Lamping.Checks.OldChainBetaFixture
import Lamping.Checks.WrappedSuccessfulChains
import Lamping.Lamping.PhysicalCorridorPresentation
import Lamping.Lamping.ActionMatching
import Lamping.Lamping.GraphRootInputPreservation
import Lamping.Lamping.ReachableTransparency
set_option maxHeartbeats 4000000
namespace Lamping.Checks.FanBodyBindingIdentityReachable
open AG Graph Lambda Lambda.Labelled
abbrev I : Term := WrappedSuccessfulChains.I
abbrev term : Term := .app (.lam (.app (.var 0) (.var 0))) I
abbrev original : LTerm := initLabels term
abbrev current : LTerm := WrappedSuccessfulChains.contractRoot original
theorem initial : INIT original := init_is_INIT _
theorem closed : Closed term := by change (0<1 ∧0<1) ∧0<1;decide
def actualStep : StepAt [] original current := .root _ _ _ _
def actualHistory : History [[]] original current := .cons actualStep (.nil _)
theorem currentClosed : Closed current.erase := actualHistory.closed closed
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
  have member := actual_root_member
  let test := physicalBetaTest net (.inl ()) term app lam
  change []∈([[]] : List Path).filter test at member
  have yes : test []=true := (List.mem_filter.mp member).2
  change ([[]] : List Path).filter test=[[]]
  simp [yes]

def endpoint : Marked := .app [] (.lam (.var 0)) (.lam (.var 0))
theorem relative : Marked.RelativeHistory [[]]
    (Marked.mark (concrete.site.betaSyntaxFiber (.inl ()) term) term) endpoint := by
  rw [actual_fiber]
  exact .cons (.root _ _ _) (.nil _)

theorem beta_matches : Matches concrete.site.reduce (.inl ()) current.erase := by
  obtain ⟨flow⟩ := encode_flowBalance term 0
  obtain ⟨balance⟩ := encode_indexed_balance term 0
  exact concrete.site.beta_complete_matches initial closed
    (concrete.sourceIso.matches (encode_closed_matches term closed 0))
    (concrete.sourceIso.rootInputs (encode_closed_independence term closed 0).rootInputs)
    (concrete.sourceIso.flowBalance flow) rfl
    (concrete.sourceIso.indexed_balance balance) rfl
    (concrete.sourceIso.transparency (encode_closed_transparency term closed 0))
    relative (by simp [endpoint,Marked.Normal]) actualHistory
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
      (encode_closed_independence term closed 0).rootInputs
      (encode_closed_transparency term closed 0) (encode_closed_matches term closed 0),
    concrete.graph_step.transparency_indexed flow rfl balance rfl (encode_closed_transparency term closed 0),
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


theorem actual_two_step_trace : GraphTrace (ActualNet.initial term) (ActualNet.ofNet outerFan.site.reduce)
    [.beta 0,.fanAction .lam 0 1 (by decide)] :=
  .cons concrete.graph_step (.cons outerFan.graph_step (.refl _))

theorem actual_source_matches : Matches outerFan.site.net (.inl ()) current.erase := by
  obtain ⟨_,_,_,_,matching⟩ := beta_certified
  exact outerFan.sourceIso.matches matching

theorem actual_target_matches : Matches outerFan.site.reduce (.inl ()) current.erase := by
  obtain ⟨_,_,_,_,matching⟩ := outer_certified
  exact matching
end Lamping.Checks.FanBodyBindingIdentityReachable
#print axioms Lamping.Checks.FanBodyBindingIdentityReachable.initial
#print axioms Lamping.Checks.FanBodyBindingIdentityReachable.actualHistory
#print axioms Lamping.Checks.FanBodyBindingIdentityReachable.actual_two_step_trace
#print axioms Lamping.Checks.FanBodyBindingIdentityReachable.actual_source_matches
#print axioms Lamping.Checks.FanBodyBindingIdentityReachable.actual_target_matches

namespace Lamping.Checks.FanBodyBindingIdentityReachable
open AG Graph Lambda Lambda.Labelled
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
def oldBodyApp : (encode 0 term).N := .inr (.inl (.inr (.inl (.inl ()))))
def oldFnVar : (encode 0 term).N := .inr (.inl (.inr (.inr (.inl ()))))
def appKept : concrete.Kept := ⟨oldBodyApp,by constructor <;> intro h <;> cases h⟩
def varKept : concrete.Kept := ⟨oldFnVar,by constructor <;> intro h <;> cases h⟩
def wrapFnWire (w : (encode 0 (.lam (.app (.var 0) (.var 0)))).W) : (encode 0 term).W := .inl (.inr (.inl w))
def wrapBodyWire (w : (encode 0 (.app (.var 0) (.var 0))).W) : (encode 0 term).W := wrapFnWire (.inl (.inr w))
def appRootWire : (encode 0 term).W := wrapFnWire (.inr (.inl ()))
def fnVarWire : (encode 0 term).W := wrapBodyWire (.inr (.inl (.inl ())))
def fnInputWire : (encode 0 term).W := wrapBodyWire (.inr (.inl (.inr ⟨0,rfl⟩)))
def outsideRoot : concrete.Outside := ⟨appRootWire,by
  rintro ⟨d,h⟩;simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h;rcases h with h|h <;> cases h⟩
def outsideFn : concrete.Outside := ⟨fnVarWire,by
  rintro ⟨d,h⟩;simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h;rcases h with h|h <;> cases h⟩
def outsideInput : concrete.Outside := ⟨fnInputWire,by
  rintro ⟨d,h⟩;simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h;rcases h with h|h <;> cases h⟩
theorem beta_root : concrete.site.reduce.wire (.inr (.inl (.inl ())))=
    .inr (.inr (.inr (.inl false),false)) := beta_lift_wire (.inr (.inl (.inl (.inl ()))) ) (.inr (.inl (.inr (.inl false)))) rfl
theorem beta_root_glue : concrete.site.reduce.wire (.inr (.inr (.inr (.inl false),true)))=
    .inr (.inr (.inr (.inr true),true)) := rfl
theorem beta_body : concrete.site.reduce.wire (.inr (.inr (.inr (.inr true),false)))=
    .inr (.inr (.inl (.inl outsideRoot),false)) := beta_lift_wire (.inr (.inl (.inr (.inr true)))) (.inr (.inr (outsideRoot,false))) rfl
theorem beta_app : concrete.site.reduce.wire (.inr (.inr (.inl (.inl outsideRoot),true)))=
    .inl ⟨.inl appKept,appCtx⟩ := beta_lift_wire (.inr (.inr (outsideRoot,true))) (.inl ⟨appKept,appCtx⟩) rfl
theorem beta_fn : concrete.site.reduce.wire (.inl ⟨.inl appKept,.inl ()⟩)=
    .inr (.inr (.inl (.inl outsideFn),false)) := beta_lift_wire (.inl ⟨appKept,.inl ()⟩) (.inr (.inr (outsideFn,false))) rfl
theorem beta_var_aux : concrete.site.reduce.wire (.inr (.inr (.inl (.inl outsideFn),true)))=
    .inl ⟨.inl varKept,.inr ()⟩ := beta_lift_wire (.inr (.inr (outsideFn,true))) (.inl ⟨varKept,.inr ()⟩) rfl
theorem beta_var_principal : concrete.site.reduce.wire (.inl ⟨.inl varKept,.inl ()⟩)=
    .inr (.inr (.inl (.inl outsideInput),true)) := beta_lift_wire (.inl ⟨varKept,.inl ()⟩) (.inr (.inr (outsideInput,true))) rfl
theorem beta_fan_aux : concrete.site.reduce.wire (.inr (.inr (.inl (.inl outsideInput),false)))=
    .inl ⟨rhsFan,.inr false⟩ := beta_lift_wire (.inr (.inr (outsideInput,false))) (.inl ⟨fanKept,.inr false⟩) rfl

def finalApp : outerFan.Kept := ⟨.inl appKept,by
  constructor <;> intro h <;> have hs:=congrArg Subtype.val (Sum.inl.inj h) <;> cases hs⟩
def finalVar : outerFan.Kept := ⟨.inl varKept,by
  constructor <;> intro h <;> have hs:=congrArg Subtype.val (Sum.inl.inj h) <;> cases hs⟩
def rootOutside : outerFan.Outside := ⟨.inr (.inl false),by
  rintro ⟨d,h⟩;simp only [outerCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h <;> cases h⟩
def bodyOutside : outerFan.Outside := ⟨.inr (.inr true),by
  rintro ⟨d,h⟩;simp only [outerCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h <;> cases h⟩
def appOutside : outerFan.Outside := ⟨.inl (.inl outsideRoot),by
  rintro ⟨d,h⟩;simp only [outerCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h <;> cases h⟩
def fnOutside : outerFan.Outside := ⟨.inl (.inl outsideFn),by
  rintro ⟨d,h⟩;simp only [outerCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h <;> cases h⟩
def inputOutside : outerFan.Outside := ⟨.inl (.inl outsideInput),by
  rintro ⟨d,h⟩;simp only [outerCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h <;> cases h⟩
theorem outer_root : outerFan.site.reduce.wire (.inr (.inl (.inl ())))=
    .inr (.inr (.inl (.inl rootOutside),false)) := outer_lift_wire (.inr (.inl (.inl (.inl ())))) (.inr (.inr (rootOutside,false))) beta_root
theorem outer_root_glue : outerFan.site.reduce.wire (.inr (.inr (.inl (.inl rootOutside),true)))=
    .inr (.inr (.inl (.inl bodyOutside),true)) := outer_lift_wire (.inr (.inr (rootOutside,true))) (.inr (.inr (bodyOutside,true))) beta_root_glue
theorem outer_body : outerFan.site.reduce.wire (.inr (.inr (.inl (.inl bodyOutside),false)))=
    .inr (.inr (.inl (.inl appOutside),false)) := outer_lift_wire (.inr (.inr (bodyOutside,false))) (.inr (.inr (appOutside,false))) beta_body
theorem outer_app : outerFan.site.reduce.wire (.inr (.inr (.inl (.inl appOutside),true)))=
    .inl ⟨.inl finalApp,appCtx⟩ := outer_lift_wire (.inr (.inr (appOutside,true))) (.inl ⟨finalApp,appCtx⟩) beta_app
theorem outer_fn : outerFan.site.reduce.wire (.inl ⟨.inl finalApp,.inl ()⟩)=
    .inr (.inr (.inl (.inl fnOutside),false)) := outer_lift_wire (.inl ⟨finalApp,.inl ()⟩) (.inr (.inr (fnOutside,false))) beta_fn
theorem outer_var_aux : outerFan.site.reduce.wire (.inr (.inr (.inl (.inl fnOutside),true)))=
    .inl ⟨.inl finalVar,.inr ()⟩ := outer_lift_wire (.inr (.inr (fnOutside,true))) (.inl ⟨finalVar,.inr ()⟩) beta_var_aux
theorem outer_var_principal : outerFan.site.reduce.wire (.inl ⟨.inl finalVar,.inl ()⟩)=
    .inr (.inr (.inl (.inl inputOutside),true)) := outer_lift_wire (.inl ⟨finalVar,.inl ()⟩) (.inr (.inr (inputOutside,true))) beta_var_principal
theorem outer_fan_front : outerFan.site.reduce.wire (.inr (.inr (.inl (.inl inputOutside),false)))=
    .inr (.inr (.inr (.inl false),false)) := outer_lift_wire (.inr (.inr (inputOutside,false))) (.inr (.inl (.inr (.inl false)))) beta_fan_aux
theorem outer_copy_ctx : outerFan.site.reduce.wire (.inr (.inr (.inr (.inl false),true)))=
    .inl ⟨.inr (.inl false),.inl ()⟩ := rfl

noncomputable abbrev outerNet := outerFan.site.reduce
noncomputable def rootEdges : List (Endpoint outerNet) :=
  [.inr (.inl (.inl ())),.inr (.inr (.inl (.inl rootOutside),true)),
   .inr (.inr (.inl (.inl bodyOutside),false)),.inr (.inr (.inl (.inl appOutside),true))]
theorem rootLabels (a : Context) : Labelling outerNet rootEdges a a := by
  apply Labelling.cons (by rw [outer_root];exact .transparent _ false a)
  apply Labelling.cons (by rw [outer_root_glue];exact .transparent _ true a)
  exact .cons (by rw [outer_body];exact .transparent _ false a) (.single _ _)
theorem rootFinish : rootEdges.getLast?=some (outerNet.wire (.inl ⟨.inl finalApp,appCtx⟩)) := by
  have h:=congrArg outerNet.wire outer_app
  simp only [Pairing.involutive] at h
  exact congrArg some h
noncomputable def rootAccess : RootAccess outerNet (.inl ()) := by
  let flow := Classical.choose outer_certified
  exact ⟨rootEdges,⟨⟨⟨Context.empty,Context.empty,rootLabels _⟩,
    (rootLabels Context.empty).root_forward_of_flow flow (.inl ()) rfl rfl⟩,rfl,⟨.app,by
      unfold accessKind;rw [rootFinish];simp only [Option.bind_some,Pairing.involutive];rfl⟩⟩⟩
noncomputable def fnTail : List (Endpoint outerNet) :=
  [.inl ⟨.inl finalApp,.inl ()⟩,.inr (.inr (.inl (.inl fnOutside),true)),
   .inl ⟨.inl finalVar,.inl ()⟩,.inr (.inr (.inl (.inl inputOutside),false)),
   .inr (.inr (.inr (.inl false),true))]
theorem fnTailLabels : Labelling outerNet fnTail Context.empty Context.empty := by
  have emptyCro : Traversal 0 (.op .cro) (.inr ()) (.inl ()) Context.empty Context.empty := by
    simpa only [Context.cons_empty,Context.replace_zero] using
      (Traversal.direct (Passage.cro (i:=0) Context.empty Context.empty))
  apply Labelling.cons (by rw [outer_fn];exact .transparent _ false Context.empty)
  apply Labelling.cons (by rw [outer_var_aux];exact LabelledTurn.node (g:=outerNet) (.inl finalVar) _ _ emptyCro)
  apply Labelling.cons (by rw [outer_var_principal];exact .transparent _ true Context.empty)
  exact .cons (by rw [outer_fan_front];exact .transparent _ false Context.empty) (.single _ _)
noncomputable def lambdaEdges : List (Endpoint outerNet) := rootEdges++fnTail
theorem lambdaLabels : Labelling outerNet lambdaEdges Context.empty Context.empty :=
  (rootLabels Context.empty).append_seam fnTailLabels (by
    intro e f last first
    have he:=Option.some.inj (last.symm.trans rootFinish)
    have hf:=Option.some.inj first
    subst e;subst f
    rw [Pairing.involutive]
    exact LabelledTurn.node (g:=outerNet) (.inl finalApp) appCtx (.inl ()) (.direct (.appFun Context.empty)))
theorem lambdaWord : accessWord outerNet lambdaEdges=[.fn] := rfl
theorem lambdaFinish : lambdaEdges.getLast?=some (outerNet.wire (.inl ⟨.inr (.inl false),.inl ()⟩)) := by
  have h:=congrArg outerNet.wire outer_copy_ctx
  simp only [Pairing.involutive] at h
  exact congrArg some h
noncomputable def lambdaParent : RootAccess outerNet (.inl ()) := by
  let flow := Classical.choose outer_certified
  exact ⟨lambdaEdges,⟨⟨⟨Context.empty,Context.empty,lambdaLabels⟩,
    lambdaLabels.root_forward_of_flow flow (.inl ()) rfl rfl⟩,rfl,⟨.lam,by
      unfold accessKind;rw [lambdaFinish];simp only [Option.bind_some,Pairing.involutive];rfl⟩⟩⟩
#print axioms rootAccess
#print axioms lambdaParent
#print axioms lambdaWord
#print axioms lambdaFinish
end Lamping.Checks.FanBodyBindingIdentityReachable
