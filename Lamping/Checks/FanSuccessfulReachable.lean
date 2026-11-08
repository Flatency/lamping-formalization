import Lamping.Checks.OldChainBetaFixture
import Lamping.Checks.FanSuccessfulChains
import Lamping.Lamping.ActionMatching
import Lamping.Lamping.GraphRootInputPreservation
import Lamping.Lamping.ReachableTransparency

/-! Actual closed wrapped fan-control candidate.  No AuxiliarySeparation premise.
The outer application is retained throughout the intended administrative actions.
-/
namespace Lamping.Checks.FanSuccessfulReachable
open AG Graph Lambda Lambda.Labelled

abbrev argument : Term := .lam (.app (.var 0) identity)
abbrev fnBody : Term := .lam (.app (.app (.var 0) (.var 1)) (.var 1))
abbrev fnTerm : Term := .lam fnBody
abbrev inner : Term := .app fnTerm argument
abbrev term : Term := .app inner identity
abbrev net := (encode 0 term).net

def app : (encode 0 term).N := .inr (.inl (.inl (.inl ())))
def lam : (encode 0 term).N := .inr (.inl (.inr (.inl (.inl ()))))
def principalWire : (encode 0 term).W := .inl (.inr (.inl (.inr (.inl (.inl ())))))

def corridor : TransparentCorridor net where
  first := ⟨app,.inl ()⟩
  last := ⟨lam,.inl ()⟩
  edges := [.inl ⟨app,.inl ()⟩,.inr (.inr (principalWire,true))]
  start := rfl
  finish := rfl
  transparent := by
    intro e f member
    have same := List.mem_singleton.mp member
    cases same
    exact ⟨principalWire,false,rfl,rfl⟩

noncomputable def concrete := PhysicalCorridorPresentation.of_corridor net (.beta 0)
  corridor app lam (by intro h;cases h) rfl rfl (.inl ()) (.inl ())
  HEq.rfl HEq.rfl rfl rfl

theorem actual_beta_step : GraphStep (.beta 0) (ActualNet.initial term)
    (ActualNet.ofNet concrete.site.reduce) := concrete.graph_step

theorem closed : Closed term := by
  change ((((0<2) ∧ (1<2)) ∧ (1<2)) ∧ ((0<1) ∧ (0<2))) ∧ (0<1)
  decide

#print axioms actual_beta_step

def outerApp : (encode 0 term).N := .inl (.inl ())
def outerFnWire : (encode 0 term).W := .inr (.inl (.inl ()))
def parentEdges : List (Endpoint net) :=
  [.inr (.inl (.inl ())),.inl ⟨outerApp,.inl ()⟩,.inr (.inr (outerFnWire,true))]
theorem parentLabels (a : Context) : Labelling net parentEdges a a :=
  .cons (LabelledTurn.node (g:=net) outerApp appCtx (.inl ()) (.direct (.appFun a)))
    (.cons (LabelledTurn.transparent (g:=net) outerFnWire false a) (.single _ _))
theorem parentForward : Forward net parentEdges :=
  .node outerApp appCtx (.inl ()) rfl rfl ⟨rfl,Or.inl rfl⟩
    (.transparent outerFnWire false rfl rfl (.single _))
def parent : RootAccess net (.inl ()) :=
  ⟨parentEdges,⟨⟨⟨Context.empty,Context.empty,parentLabels _⟩,parentForward⟩,rfl,⟨.app,rfl⟩⟩⟩
theorem principalLabels (a : Context) : Labelling net corridor.edges a a :=
  .cons (LabelledTurn.transparent (g:=net) principalWire false a) (.single _ _)
theorem principalForward : Forward net corridor.edges :=
  .transparent principalWire false rfl rfl (.single _)
def childEdges : List (Endpoint net) := parentEdges++corridor.edges
theorem childLabels (a : Context) : Labelling net childEdges a a :=
  .cons (LabelledTurn.node (g:=net) outerApp appCtx (.inl ()) (.direct (.appFun a)))
    (.cons (LabelledTurn.transparent (g:=net) outerFnWire false a)
      (.cons (LabelledTurn.node (g:=net) app appCtx (.inl ()) (.direct (.appFun a)))
        (principalLabels a)))
def child : RootAccess net (.inl ()) :=
  ⟨childEdges,⟨⟨⟨Context.empty,Context.empty,childLabels _⟩,
    .node outerApp appCtx (.inl ()) rfl rfl ⟨rfl,Or.inl rfl⟩
      (.transparent outerFnWire false rfl rfl
        (.node app appCtx (.inl ()) rfl rfl ⟨rfl,Or.inl rfl⟩ principalForward))⟩,
    rfl,⟨.lam,rfl⟩⟩⟩
def redex : RedexOcc term := ⟨[.fn],_,rfl,True.intro⟩
def rich : ActualRedexAccess net (.inl ()) redex where
  connection := {
    app := app,lam := lam,appPort := .inl (),lamPort := .inl (),appIndex := 0,lamIndex := 0
    appLabel := rfl,lamLabel := rfl,appPrincipal := HEq.rfl,lamPrincipal := HEq.rfl
    edges := corridor.edges,proper := ⟨⟨Context.empty,Context.empty,principalLabels _⟩,principalForward⟩
    start := rfl,finish := rfl,emptyWord := rfl }
  parent := parent
  child := child
  ctx := appCtx
  contextPrincipal := HEq.rfl
  parentWord := rfl
  childWord := rfl
  parentFinish := rfl
  split := rfl
theorem member : [.fn]∈physicalBetaFiberPaths net (.inl ()) term app lam :=
  (mem_physicalBetaFiberPaths net (.inl ()) term app lam [.fn]).mpr
    ⟨redex,rich,rfl,rfl,rfl⟩
theorem actual_fiber : concrete.site.betaSyntaxFiber (.inl ()) term=[[.fn]] := by
  rw [concrete.betaSyntaxFiber_eq]
  let test := physicalBetaTest net (.inl ()) term app lam
  have yes : test [.fn]=true := (List.mem_filter.mp member).2
  change ([[.fn]] : List Path).filter test=[[.fn]]
  simp [yes]
#print axioms actual_fiber

def sharedInput : Shared (.app (.var 0) (.var 1)) (.var 1) := ⟨⟨1,rfl⟩,Or.inr rfl⟩
def oldFan : (encode 0 term).N := .inr (.inl (.inr (.inl (.inr (.inr (.inl (.inr (.inr sharedInput))))))))
def oldArgLam : (encode 0 term).N := .inr (.inl (.inr (.inr (.inl ()))))
def fanKept : RemainingNodes app lam := ⟨oldFan,by constructor <;> intro h <;> cases h⟩
def argKept : RemainingNodes app lam := ⟨oldArgLam,by constructor <;> intro h <;> cases h⟩
theorem actual_kept_fan_label : concrete.kept fanKept=label .fan 0 := rfl
theorem actual_kept_arg_label : concrete.kept argKept=label .lam 1 := rfl

def bindingWire1 : (encode 0 term).W := .inl (.inr (.inl (.inl (.inr (.inl (.inl (.inr (.inr (.inr ⟨1,Or.inr rfl⟩)))))))))
def bindingWire2 : (encode 0 term).W := .inl (.inr (.inl (.inl (.inr (.inl (.inr (.inr ⟨0,Or.inr rfl⟩)))))))
def argumentWire : (encode 0 term).W := .inl (.inr (.inl (.inr (.inr (.inl ())))))
theorem old_fan_wire : net.wire (.inl ⟨oldFan,.inl ()⟩)=.inr (.inr (bindingWire1,true)) := rfl
theorem old_binding_transit : net.wire (.inr (.inr (bindingWire1,false)))=.inr (.inr (bindingWire2,true)) := rfl
theorem old_binding_finish : net.wire (.inr (.inr (bindingWire2,false)))=.inl ⟨lam,lamBind⟩ := rfl
def outside1 : concrete.Outside := ⟨bindingWire1,by rintro ⟨d,h⟩;simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h;rcases h with h|h <;> cases h⟩
def outside2 : concrete.Outside := ⟨bindingWire2,by rintro ⟨d,h⟩;simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h;rcases h with h|h <;> cases h⟩
def outsideArg : concrete.Outside := ⟨argumentWire,by rintro ⟨d,h⟩;simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h;rcases h with h|h <;> cases h⟩
theorem site_fan_wire : concrete.site.net.wire (.inl ⟨.inl fanKept,.inl ()⟩)=.inr (.inr (.inl outside1,true)) := by
  apply concrete.sourceIso.symm.ends.injective;rw [concrete.sourceIso.symm.wiring];rfl
theorem site_transit : concrete.site.net.wire (.inr (.inr (.inl outside1,false)))=.inr (.inr (.inl outside2,true)) := by
  apply concrete.sourceIso.symm.ends.injective;rw [concrete.sourceIso.symm.wiring];rfl
theorem site_bind_wire : concrete.site.net.wire (.inr (.inr (.inl outside2,false)))=.inl ⟨.inr (.inr ()),lamBind⟩ := by
  apply concrete.sourceIso.symm.ends.injective;rw [concrete.sourceIso.symm.wiring];rfl
theorem site_arg_wire : concrete.site.net.wire (.inl ⟨.inr (.inl ()),appArg⟩)=.inr (.inr (.inl outsideArg,false)) := by
  apply concrete.sourceIso.symm.ends.injective;rw [concrete.sourceIso.symm.wiring];rfl
theorem site_arg_finish : concrete.site.net.wire (.inr (.inr (.inl outsideArg,true)))=.inl ⟨.inl argKept,.inl ()⟩ := by
  apply concrete.sourceIso.symm.ends.injective;rw [concrete.sourceIso.symm.wiring];rfl
noncomputable abbrev actualCut := cutFragment concrete.site.net (pathPartition (Schema.beta 0) concrete.Inside) concrete.site.closed
theorem cut_fan_wire : actualCut.wire (.inl ⟨fanKept,.inl ()⟩)=.inr (.inr (outside1,true)) := by
  apply concrete.site.outsideEnd_injective;exact (concrete.site.outsideEnd_wire _).symm.trans site_fan_wire
theorem cut_transit : actualCut.wire (.inr (.inr (outside1,false)))=.inr (.inr (outside2,true)) := by
  apply concrete.site.outsideEnd_injective;exact (concrete.site.outsideEnd_wire _).symm.trans site_transit
theorem cut_bind_wire : actualCut.wire (.inr (.inr (outside2,false)))=.inr (.inl (.inr (.inr false))) := by
  apply concrete.site.outsideEnd_injective;exact (concrete.site.outsideEnd_wire _).symm.trans site_bind_wire
theorem cut_arg_wire : actualCut.wire (.inr (.inl (.inr (.inl true))))=.inr (.inr (outsideArg,false)) := by
  apply concrete.site.outsideEnd_injective;exact (concrete.site.outsideEnd_wire _).symm.trans site_arg_wire
theorem cut_arg_finish : actualCut.wire (.inr (.inr (outsideArg,true)))=.inl ⟨argKept,.inl ()⟩ := by
  apply concrete.site.outsideEnd_injective;exact (concrete.site.outsideEnd_wire _).symm.trans site_arg_finish
noncomputable def rhsFan : concrete.Kept⊕Empty := .inl fanKept
noncomputable def rhsLambda : concrete.Kept⊕Empty := .inl argKept
noncomputable def fanPrincipal : Endpoint concrete.site.reduce := .inl ⟨rhsFan,.inl ()⟩
noncomputable def step1 : Endpoint concrete.site.reduce := .inr (.inr (.inl (.inl outside1),false))
noncomputable def step2 : Endpoint concrete.site.reduce := .inr (.inr (.inl (.inl outside2),false))
noncomputable def step3 : Endpoint concrete.site.reduce := .inr (.inr (.inr (.inr false),true))
noncomputable def step4 : Endpoint concrete.site.reduce := .inr (.inr (.inr (.inl true),false))
noncomputable def step5 : Endpoint concrete.site.reduce := .inr (.inr (.inl (.inl outsideArg),true))
theorem target_fan_wire : concrete.site.reduce.wire fanPrincipal=.inr (.inr (.inl (.inl outside1),true)) :=
  (plugLeft_wire actualCut (Schema.beta 0).right.net (.inl ⟨fanKept,.inl ()⟩)).trans
    (congrArg (AG.plugLeft actualCut (Schema.beta 0).right.net) cut_fan_wire)
theorem target_transit : concrete.site.reduce.wire step1=.inr (.inr (.inl (.inl outside2),true)) :=
  (plugLeft_wire actualCut (Schema.beta 0).right.net (.inr (.inr (outside1,false)))).trans
    (congrArg (AG.plugLeft actualCut (Schema.beta 0).right.net) cut_transit)
theorem target_bind_wire : concrete.site.reduce.wire step2=.inr (.inr (.inr (.inr false),false)) :=
  (plugLeft_wire actualCut (Schema.beta 0).right.net (.inr (.inr (outside2,false)))).trans
    (congrArg (AG.plugLeft actualCut (Schema.beta 0).right.net) cut_bind_wire)
theorem target_glue : concrete.site.reduce.wire step3=.inr (.inr (.inr (.inl true),true)) := rfl
theorem target_arg_wire : concrete.site.reduce.wire step4=.inr (.inr (.inl (.inl outsideArg),false)) :=
  (plugLeft_wire actualCut (Schema.beta 0).right.net (.inr (.inl (.inr (.inl true))))).trans
    (congrArg (AG.plugLeft actualCut (Schema.beta 0).right.net) cut_arg_wire)
theorem target_finish : concrete.site.reduce.wire step5=.inl ⟨rhsLambda,.inl ()⟩ :=
  (plugLeft_wire actualCut (Schema.beta 0).right.net (.inr (.inr (outsideArg,true)))).trans
    (congrArg (AG.plugLeft actualCut (Schema.beta 0).right.net) cut_arg_finish)
noncomputable def actualFanLambdaCorridor : TransparentCorridor concrete.site.reduce where
  first := ⟨rhsFan,.inl ()⟩
  last := ⟨rhsLambda,.inl ()⟩
  edges := [fanPrincipal,step1,step2,step3,step4,step5]
  start := rfl
  finish := by
    have h:=congrArg concrete.site.reduce.wire target_finish
    simp only [Pairing.involutive] at h
    exact congrArg some h
  transparent := by
    intro e f member
    simp only [List.tail_cons,List.zip_cons_cons,List.zip_nil_right,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h|h|h|h|h
    · cases h;exact ⟨.inl (.inl outside1),true,target_fan_wire,rfl⟩
    · cases h;exact ⟨.inl (.inl outside2),true,target_transit,rfl⟩
    · cases h;exact ⟨.inr (.inr false),false,target_bind_wire,rfl⟩
    · cases h;exact ⟨.inr (.inl true),true,target_glue,rfl⟩
    · cases h;exact ⟨.inl (.inl outsideArg),false,target_arg_wire,rfl⟩
noncomputable def actualFanPresentation := PhysicalCorridorPresentation.of_corridor concrete.site.reduce
  (.fanAction .lam 0 1 (by decide)) actualFanLambdaCorridor rhsFan rhsLambda
  (by intro h;have same:=congrArg Subtype.val (Sum.inl.inj h);cases same)
  rfl rfl (.inl ()) (.inl ()) HEq.rfl HEq.rfl rfl rfl

#print axioms actualFanPresentation
abbrev original := FanSuccessfulChains.original
abbrev current := FanSuccessfulChains.current
def endpoint : Marked := .app [] (.lam (.app [] (.app [] (.var 0) (.lam (.app [] (.var 0) (.lam (.var 0))))) (.lam (.app [] (.var 0) (.lam (.var 0)))))) (.lam (.var 0))
theorem relative : Marked.RelativeHistory [[.fn]]
    (Marked.mark (concrete.site.betaSyntaxFiber (.inl ()) term) term) endpoint := by
  rw [actual_fiber]
  exact .cons (.appL (.root _ _ _)) (.nil _)
theorem beta_matches : Matches concrete.site.reduce (.inl ()) current.erase := by
  obtain ⟨flow⟩ := encode_flowBalance term 0
  obtain ⟨balance⟩ := encode_indexed_balance term 0
  exact concrete.site.beta_complete_matches FanSuccessfulChains.initial closed
    (concrete.sourceIso.matches (encode_closed_matches term closed 0))
    (concrete.sourceIso.rootInputs (encode_closed_independence term closed 0).rootInputs)
    (concrete.sourceIso.flowBalance flow) rfl
    (concrete.sourceIso.indexed_balance balance) rfl
    (concrete.sourceIso.transparency (encode_closed_transparency term closed 0))
    relative (by simp [endpoint,Marked.Normal]) FanSuccessfulChains.actualHistory
#print axioms beta_matches

def originalArgVar : (encode 1 argument).N := .inr (.inr (.inl ()))
def oldArgVar : (encode 0 term).N := .inr (.inl (.inr (.inr originalArgVar)))
example : net.label oldArgVar=label .cro 1 := rfl
def wrapArgWire (w : (encode 1 argument).W) : (encode 0 term).W :=
  .inl (.inr (.inl (.inl (.inr (.inr w)))))
def argBindingWire : (encode 0 term).W := wrapArgWire (.inr (.inr ⟨0,Or.inl rfl⟩))
def argVariableWire : (encode 0 term).W := wrapArgWire (.inl (.inr (.inr (.inl (.inr ⟨0,rfl⟩)))))
theorem arg_bind_start : net.wire (.inl ⟨oldArgLam,lamBind⟩)=.inr (.inr (argBindingWire,false)) := rfl
theorem arg_bind_transit : net.wire (.inr (.inr (argBindingWire,true)))=
    .inr (.inr (argVariableWire,false)) := rfl
theorem arg_var_finish : net.wire (.inr (.inr (argVariableWire,true)))=
    .inl ⟨oldArgVar,.inl ()⟩ := by
  have h : net.wire (.inl ⟨oldArgVar,.inl ()⟩)=.inr (.inr (argVariableWire,true)) := rfl
  exact (congrArg net.wire h).symm.trans (net.wire.involutive _)

def varKept : concrete.Kept := ⟨oldArgVar,by constructor <;> intro h <;> cases h⟩
def argBindingOutside : concrete.Outside := ⟨argBindingWire,by
  rintro ⟨d,h⟩
  simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h <;> cases h⟩
def argVariableOutside : concrete.Outside := ⟨argVariableWire,by
  rintro ⟨d,h⟩
  simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h <;> cases h⟩
theorem beta_lift_wire (e f : Endpoint actualCut)
    (h : net.wire (concrete.sourceIso.symm.ends (concrete.site.outsideEnd e))=
      concrete.sourceIso.symm.ends (concrete.site.outsideEnd f)) :
    concrete.site.reduce.wire (AG.plugLeft actualCut (Schema.beta 0).right.net e)=
      AG.plugLeft actualCut (Schema.beta 0).right.net f := by
  have old : concrete.site.net.wire (concrete.site.outsideEnd e)=concrete.site.outsideEnd f := by
    apply concrete.sourceIso.symm.ends.injective
    rw [concrete.sourceIso.symm.wiring]
    exact h
  have cut : actualCut.wire e=f := concrete.site.outsideEnd_injective
    ((concrete.site.outsideEnd_wire e).symm.trans old)
  exact (plugLeft_wire actualCut (Schema.beta 0).right.net e).trans
    (congrArg (AG.plugLeft actualCut (Schema.beta 0).right.net) cut)
theorem beta_arg_bind_start : concrete.site.reduce.wire (.inl ⟨rhsLambda,lamBind⟩)=
    .inr (.inr (.inl (.inl argBindingOutside),false)) :=
  beta_lift_wire (.inl ⟨argKept,lamBind⟩) (.inr (.inr (argBindingOutside,false))) arg_bind_start
theorem beta_arg_bind_transit : concrete.site.reduce.wire
    (.inr (.inr (.inl (.inl argBindingOutside),true)))=
    .inr (.inr (.inl (.inl argVariableOutside),false)) :=
  beta_lift_wire (.inr (.inr (argBindingOutside,true)))
    (.inr (.inr (argVariableOutside,false))) arg_bind_transit
theorem beta_arg_var_finish : concrete.site.reduce.wire
    (.inr (.inr (.inl (.inl argVariableOutside),true)))=.inl ⟨.inl varKept,.inl ()⟩ :=
  beta_lift_wire (.inr (.inr (argVariableOutside,true))) (.inl ⟨varKept,.inl ()⟩) arg_var_finish

def varKept2 : actualFanPresentation.Kept := ⟨.inl varKept,by
  constructor
  · intro h;have hs:=congrArg Subtype.val (Sum.inl.inj h);cases hs
  · intro h;have hs:=congrArg Subtype.val (Sum.inl.inj h);cases hs⟩
def argBindingOutside2 : actualFanPresentation.Outside := ⟨.inl (.inl argBindingOutside),by
  rintro ⟨d,h⟩
  simp only [actualFanLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h|h <;> cases h⟩
def argVariableOutside2 : actualFanPresentation.Outside := ⟨.inl (.inl argVariableOutside),by
  rintro ⟨d,h⟩
  simp only [actualFanLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h|h <;> cases h⟩
noncomputable abbrev cut2 : Net signature actualFanPresentation.Kept (Boundary term⊕(Bool⊕Bool)) actualFanPresentation.Outside := cutFragment actualFanPresentation.site.net
  (pathPartition (Schema.fanAction .lam 0 1 (by decide)) actualFanPresentation.Inside) actualFanPresentation.site.closed
theorem outside2_injective : Function.Injective actualFanPresentation.site.outsideEnd := by
  intro e f same
  let split := fragmentEnd (B:=Boundary term) (W:=actualFanPresentation.Outside) actualFanPresentation.site.net.label
    (pathPartition (Schema.fanAction .lam 0 1 (by decide)) actualFanPresentation.Inside)
  change split.invFun (.inl e)=split.invFun (.inl f) at same
  have mapped:=congrArg split same
  simpa only [split.right_inv,Sum.inl.injEq] using mapped
theorem action2_lift_wire (e f : Endpoint cut2)
    (h : concrete.site.reduce.wire (actualFanPresentation.sourceIso.symm.ends (actualFanPresentation.site.outsideEnd e))=
      actualFanPresentation.sourceIso.symm.ends (actualFanPresentation.site.outsideEnd f)) :
    actualFanPresentation.site.reduce.wire (AG.plugLeft cut2 (Schema.fanAction .lam 0 1 (by decide)).right.net e)=
      AG.plugLeft cut2 (Schema.fanAction .lam 0 1 (by decide)).right.net f := by
  have old : actualFanPresentation.site.net.wire (actualFanPresentation.site.outsideEnd e)=actualFanPresentation.site.outsideEnd f := by
    apply actualFanPresentation.sourceIso.symm.ends.injective
    rw [actualFanPresentation.sourceIso.symm.wiring]
    exact h
  have cut : cut2.wire e=f := outside2_injective
    ((actualFanPresentation.site.outsideEnd_wire e).symm.trans old)
  exact (plugLeft_wire cut2 (Schema.fanAction .lam 0 1 (by decide)).right.net e).trans
    (congrArg (AG.plugLeft cut2 (Schema.fanAction .lam 0 1 (by decide)).right.net) cut)

noncomputable def lowBinding : actualFanPresentation.Kept⊕(Bool⊕Bool) := .inr (.inr false)
noncomputable def passiveVar : actualFanPresentation.Kept⊕(Bool⊕Bool) := .inl varKept2
noncomputable def lowPrincipal : Endpoint actualFanPresentation.site.reduce := .inl ⟨lowBinding,.inl ()⟩
noncomputable def lowGlue : Endpoint actualFanPresentation.site.reduce := .inr (.inr (.inr (.inr false),false))
noncomputable def lowStep1 : Endpoint actualFanPresentation.site.reduce := .inr (.inr (.inl (.inl argBindingOutside2),true))
noncomputable def lowStep2 : Endpoint actualFanPresentation.site.reduce := .inr (.inr (.inl (.inl argVariableOutside2),true))
theorem low_start : actualFanPresentation.site.reduce.wire lowPrincipal=
    .inr (.inr (.inr (.inr false),true)) := rfl
theorem low_glue : actualFanPresentation.site.reduce.wire lowGlue=
    .inr (.inr (.inl (.inl argBindingOutside2),false)) :=
  action2_lift_wire (.inr (.inl (.inr (.inr false))))
    (.inr (.inr (argBindingOutside2,false))) beta_arg_bind_start
theorem low_transit : actualFanPresentation.site.reduce.wire lowStep1=
    .inr (.inr (.inl (.inl argVariableOutside2),false)) :=
  action2_lift_wire (.inr (.inr (argBindingOutside2,true)))
    (.inr (.inr (argVariableOutside2,false))) beta_arg_bind_transit
theorem low_finish : actualFanPresentation.site.reduce.wire lowStep2=.inl ⟨passiveVar,.inl ()⟩ :=
  action2_lift_wire (.inr (.inr (argVariableOutside2,true)))
    (.inl ⟨varKept2,.inl ()⟩) beta_arg_var_finish
noncomputable def actualFanCroCorridor : TransparentCorridor actualFanPresentation.site.reduce where
  first := ⟨lowBinding,.inl ()⟩
  last := ⟨passiveVar,.inl ()⟩
  edges := [lowPrincipal,lowGlue,lowStep1,lowStep2]
  start := rfl
  finish := by
    have h:=congrArg actualFanPresentation.site.reduce.wire low_finish
    simp only [Pairing.involutive] at h
    exact congrArg some h
  transparent := by
    intro e f member
    simp only [List.tail_cons,List.zip_cons_cons,List.zip_nil_right,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h|h|h
    · cases h;exact ⟨.inr (.inr false),true,low_start,rfl⟩
    · cases h;exact ⟨.inl (.inl argBindingOutside2),false,low_glue,rfl⟩
    · cases h;exact ⟨.inl (.inl argVariableOutside2),false,low_transit,rfl⟩
noncomputable def fanCro := PhysicalCorridorPresentation.of_corridor actualFanPresentation.site.reduce
  (.fanAction .cro 0 1 (by decide)) actualFanCroCorridor lowBinding passiveVar
  (by intro h;cases h) rfl rfl (.inl ()) (.inl ()) HEq.rfl HEq.rfl rfl rfl
#print axioms actualFanCroCorridor


#print axioms fanCro
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
theorem lambda_certified : Certified (ActualNet.ofNet actualFanPresentation.site.reduce) :=
  action_certified actualFanPresentation.graph_step (.fan .lam 0 1 (by decide)) beta_certified
theorem cro_certified : Certified (ActualNet.ofNet fanCro.site.reduce) :=
  action_certified fanCro.graph_step (.fan .cro 0 1 (by decide)) lambda_certified

theorem actual_final_matches : Matches fanCro.site.reduce (.inl ()) current.erase := by
  obtain ⟨_,_,_,_,matching⟩ := cro_certified
  exact matching

theorem actual_source_matches : Matches fanCro.site.net (.inl ()) current.erase := by
  obtain ⟨_,_,_,_,matching⟩ := lambda_certified
  exact fanCro.sourceIso.matches matching

theorem actual_three_step_trace : GraphTrace (ActualNet.initial term)
    (ActualNet.ofNet fanCro.site.reduce)
    [.beta 0,.fanAction .lam 0 1 (by decide),.fanAction .cro 0 1 (by decide)] :=
  .cons concrete.graph_step (.cons actualFanPresentation.graph_step (.cons fanCro.graph_step (.refl _)))
#print axioms actual_three_step_trace
#print axioms actual_source_matches
#print axioms actual_final_matches

end Lamping.Checks.FanSuccessfulReachable
