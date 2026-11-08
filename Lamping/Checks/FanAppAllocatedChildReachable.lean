import Lamping.Lamping.FanAppReadSlotDispatcher
import Lamping.Checks.OldChainBetaFixture
import Lamping.Checks.FanSuccessfulChains
import Lamping.Lamping.ActionMatching
import Lamping.Lamping.GraphRootInputPreservation
import Lamping.Lamping.ReachableTransparency

import Lamping.Lamping.FanAppArgumentLambdaTransport
import Lamping.Lamping.FanControlOccurrenceComparison
set_option maxHeartbeats 4000000
namespace Lamping.Checks.FanAppAllocatedChildReachable.Syntax
open AG Graph Lambda Lambda.Labelled
abbrev I : Term := identity
abbrev payload : Term := .lam (.app (.app (.var 0) I) I)
abbrev bare : Term := .app (.app (.lam (.lam (.app (.app (.var 0) (.var 1)) (.var 1)))) payload) I
abbrev original : LTerm := initLabels bare
abbrev current : LTerm := match original with
  | .app b fn arg => .app b (WrappedSuccessfulChains.contractRoot fn) arg
  | t => t
def actualStep : StepAt [.fn] original current := .fn (.root _ _ _ _)
def actualHistory : History [[.fn]] original current := .cons actualStep (.nil _)
theorem initial : INIT original := init_is_INIT _
theorem sourceClosed : Closed original.erase := by
  change (((0<2 ∧1<2) ∧1<2) ∧((0<1 ∧0<2) ∧0<2)) ∧0<1
  decide
theorem targetClosed : Closed current.erase := actualHistory.closed sourceClosed
abbrev functionLabel : Lambda.Labelled.Label := ((Lambda.Labelled.Label.atom 1).concat (Lambda.Labelled.Label.atom 2).over).concat (.atom 3)
abbrev leftLabel : Lambda.Labelled.Label := ((Lambda.Labelled.Label.atom 7).concat (Lambda.Labelled.Label.atom 2).under).concat (.atom 9)
abbrev rightLabel : Lambda.Labelled.Label := ((Lambda.Labelled.Label.atom 8).concat (Lambda.Labelled.Label.atom 2).under).concat (.atom 9)
abbrev left : Path := [.fn,.body,.fn,.arg]
abbrev right : Path := [.fn,.body,.arg]
abbrev xVar : Path := [.fn,.body,.fn,.fn]
abbrev innerApp (branch : Bool) : Path := (if branch then right else left)++[.body,.fn]
abbrev variablePath (branch : Bool) : Path := innerApp branch++[.fn]
abbrev start (branch : Bool) : Path := (if branch then right else left)++[.body]
abbrev lambdaEdges (branch : Bool) : List Path :=
  if branch then [right,[.fn,.body,.fn],xVar,[.fn]] else [left,xVar,[.fn]]
abbrev edges (branch : Bool) : List Path := innerApp branch::variablePath branch::lambdaEdges branch
abbrev payloadInner : LTerm := .app (.atom 11) (.var (.atom 12) 0) (.lam (.atom 13) (.var (.atom 14) 0))
def outer_stop : PrerequisiteChain current [.fn] [[.fn]] := .redex_lam (p:=[]) rfl
def left_lambda_chain : PrerequisiteChain current left (lambdaEdges false) :=
  .lam (parent:=[.fn,.body,.fn]) (step:=.arg) rfl (by decide)
    (.app rfl (by intro l b same;cases same)
      (.var (parent:=[.fn]) (rest:=[.fn,.fn]) rfl rfl rfl rfl outer_stop))
def right_lambda_chain : PrerequisiteChain current right (lambdaEdges true) :=
  .lam (parent:=[.fn,.body]) (step:=.arg) rfl (by decide)
    (.app rfl (by intro l b same;cases same)
      (.app rfl (by intro l b same;cases same)
        (.var (parent:=[.fn]) (rest:=[.fn,.fn]) rfl rfl rfl rfl outer_stop)))
def actual_chain (branch : Bool) : PrerequisiteChain current (start branch) (edges branch) := by
  cases branch
  · exact .app rfl (by intro l b same;cases same)
      (.app rfl (by intro l b same;cases same)
        (.var (parent:=left) (rest:=[.fn,.fn]) rfl rfl rfl rfl left_lambda_chain))
  · exact .app rfl (by intro l b same;cases same)
      (.app rfl (by intro l b same;cases same)
        (.var (parent:=right) (rest:=[.fn,.fn]) rfl rfl rfl rfl right_lambda_chain))
theorem actual_read_slots (branch : Bool) : (edges branch).length=(if branch then 6 else 5) ∧
    (edges branch)[0]?=some (innerApp branch) ∧(edges branch)[1]?=some (variablePath branch) := by cases branch <;> decide
theorem inner_lookup (branch : Bool) : current.subterm (innerApp branch)=some payloadInner := by cases branch <;> rfl
def innerPosition (branch : Bool) : Position current.erase := ⟨innerApp branch,by cases branch <;> rfl⟩
def parentPosition (branch : Bool) : Position current.erase := ⟨start branch,by cases branch <;> rfl⟩
def inner_occurrence (branch : Bool) : SourceSubterm [] .external current (innerApp branch)
    [if branch then rightLabel else leftLabel,functionLabel] (.appFn (.atom 10)) payloadInner := by
  cases branch
  · exact .fn (.body (.fn (.arg (.body (.fn .nil)))))
  · exact .fn (.body (.arg (.body (.fn .nil))))
end Lamping.Checks.FanAppAllocatedChildReachable.Syntax
namespace Lamping.Checks.FanAppAllocatedChildReachable.Base
open AG Graph Lambda Lambda.Labelled

abbrev argument : Term := .lam (.app (.app (.var 0) identity) identity)
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
  change (((0<2 ∧1<2) ∧1<2) ∧((0<1 ∧0<2) ∧0<2)) ∧0<1
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
abbrev original := Syntax.original
abbrev current := Syntax.current
def endpoint : Marked := .app [] (.lam (.app [] (.app [] (.var 0) (.lam (.app [] (.app [] (.var 0) (.lam (.var 0))) (.lam (.var 0))))) (.lam (.app [] (.app [] (.var 0) (.lam (.var 0))) (.lam (.var 0)))))) (.lam (.var 0))

theorem relative : Marked.RelativeHistory [[.fn]]
    (Marked.mark (concrete.site.betaSyntaxFiber (.inl ()) term) term) endpoint := by
  rw [actual_fiber]
  exact .cons (.appL (.root _ _ _)) (.nil _)
theorem beta_matches : Matches concrete.site.reduce (.inl ()) current.erase := by
  obtain ⟨flow⟩ := encode_flowBalance term 0
  obtain ⟨balance⟩ := encode_indexed_balance term 0
  exact concrete.site.beta_complete_matches Syntax.initial closed
    (concrete.sourceIso.matches (encode_closed_matches term closed 0))
    (concrete.sourceIso.rootInputs (encode_closed_independence term closed 0).rootInputs)
    (concrete.sourceIso.flowBalance flow) rfl
    (concrete.sourceIso.indexed_balance balance) rfl
    (concrete.sourceIso.transparency (encode_closed_transparency term closed 0))
    relative (by simp [endpoint,Marked.Normal]) Syntax.actualHistory
#print axioms beta_matches

def originalArgVar : (encode 1 argument).N := .inr (.inr (.inl (.inr (.inl ()))))
def oldArgVar : (encode 0 term).N := .inr (.inl (.inr (.inr originalArgVar)))
example : net.label oldArgVar=label .cro 1 := rfl
def wrapArgWire (w : (encode 1 argument).W) : (encode 0 term).W :=
  .inl (.inr (.inl (.inl (.inr (.inr w)))))
def argBindingWire : (encode 0 term).W := wrapArgWire (.inr (.inr ⟨0,Or.inl (Or.inl rfl)⟩))
def argVariableWire : (encode 0 term).W := wrapArgWire (.inl (.inr (.inr (.inl (.inr ⟨0,Or.inl rfl⟩)))))
def argVariableWire2 : (encode 0 term).W := wrapArgWire (.inl (.inr (.inl (.inr (.inl (.inr (.inl (.inr ⟨0,rfl⟩))))))))
theorem arg_var_transit : net.wire (.inr (.inr (argVariableWire,true)))=
    .inr (.inr (argVariableWire2,false)) := rfl

theorem arg_bind_start : net.wire (.inl ⟨oldArgLam,lamBind⟩)=.inr (.inr (argBindingWire,false)) := rfl
theorem arg_bind_transit : net.wire (.inr (.inr (argBindingWire,true)))=
    .inr (.inr (argVariableWire,false)) := rfl
theorem arg_var_finish : net.wire (.inr (.inr (argVariableWire2,true)))=
    .inl ⟨oldArgVar,.inl ()⟩ := by
  have h : net.wire (.inl ⟨oldArgVar,.inl ()⟩)=.inr (.inr (argVariableWire2,true)) := rfl
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
def argVariableOutsideExtra : concrete.Outside := ⟨argVariableWire2,by
  rintro ⟨d,h⟩;simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h
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
theorem beta_arg_var_transit : concrete.site.reduce.wire
    (.inr (.inr (.inl (.inl argVariableOutside),true)))=
    .inr (.inr (.inl (.inl argVariableOutsideExtra),false)) :=
  beta_lift_wire (.inr (.inr (argVariableOutside,true)))
    (.inr (.inr (argVariableOutsideExtra,false))) arg_var_transit

theorem beta_arg_var_finish : concrete.site.reduce.wire
    (.inr (.inr (.inl (.inl argVariableOutsideExtra),true)))=.inl ⟨.inl varKept,.inl ()⟩ :=
  beta_lift_wire (.inr (.inr (argVariableOutsideExtra,true))) (.inl ⟨varKept,.inl ()⟩) arg_var_finish

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
def argVariableOutsideExtra2 : actualFanPresentation.Outside := ⟨.inl (.inl argVariableOutsideExtra),by
  rintro ⟨d,h⟩;simp only [actualFanLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
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
noncomputable def lowStep3 : Endpoint actualFanPresentation.site.reduce := .inr (.inr (.inl (.inl argVariableOutsideExtra2),true))
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
theorem low_transit_extra : actualFanPresentation.site.reduce.wire lowStep2=
    .inr (.inr (.inl (.inl argVariableOutsideExtra2),false)) :=
  action2_lift_wire (.inr (.inr (argVariableOutside2,true)))
    (.inr (.inr (argVariableOutsideExtra2,false))) beta_arg_var_transit

theorem low_finish : actualFanPresentation.site.reduce.wire lowStep3=.inl ⟨passiveVar,.inl ()⟩ :=
  action2_lift_wire (.inr (.inr (argVariableOutsideExtra2,true)))
    (.inl ⟨varKept2,.inl ()⟩) beta_arg_var_finish
noncomputable def actualFanCroCorridor : TransparentCorridor actualFanPresentation.site.reduce where
  first := ⟨lowBinding,.inl ()⟩
  last := ⟨passiveVar,.inl ()⟩
  edges := [lowPrincipal,lowGlue,lowStep1,lowStep2,lowStep3]
  start := rfl
  finish := by
    have h:=congrArg actualFanPresentation.site.reduce.wire low_finish
    simp only [Pairing.involutive] at h
    exact congrArg some h
  transparent := by
    intro e f member
    simp only [List.tail_cons,List.zip_cons_cons,List.zip_nil_right,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h|h|h|h
    · cases h;exact ⟨.inr (.inr false),true,low_start,rfl⟩
    · cases h;exact ⟨.inl (.inl argBindingOutside2),false,low_glue,rfl⟩
    · cases h;exact ⟨.inl (.inl argVariableOutside2),false,low_transit,rfl⟩
    · cases h;exact ⟨.inl (.inl argVariableOutsideExtra2),false,low_transit_extra,rfl⟩
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

end Lamping.Checks.FanAppAllocatedChildReachable.Base

namespace Lamping.Checks.FanAppAllocatedChildReachable
open AG Graph Lambda Lambda.Labelled Base

def originalArgApp : (encode 1 argument).N := .inr (.inr (.inl (.inl (.inl ()))))
def oldArgApp : (encode 0 term).N := .inr (.inl (.inr (.inr originalArgApp)))
def argFunctionWire : (encode 0 term).W := wrapArgWire (.inl (.inr (.inl (.inr (.inl (.inr (.inl (.inl ()))))))))

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
  rcases h with h|h|h|h|h <;> cases h⟩
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
end Lamping.Checks.FanAppAllocatedChildReachable
#print axioms Lamping.Checks.FanAppAllocatedChildReachable.original_app_label
#print axioms Lamping.Checks.FanAppAllocatedChildReachable.original_var_aux_wire
#print axioms Lamping.Checks.FanAppAllocatedChildReachable.original_app_fn_wire
#print axioms Lamping.Checks.FanAppAllocatedChildReachable.fan_label
#print axioms Lamping.Checks.FanAppAllocatedChildReachable.app_label
#print axioms Lamping.Checks.FanAppAllocatedChildReachable.fanApp
#print axioms Lamping.Checks.FanAppAllocatedChildReachable.actual_four_step_trace
#print axioms Lamping.Checks.FanAppAllocatedChildReachable.actual_source_matches
#print axioms Lamping.Checks.FanAppAllocatedChildReachable.actual_target_matches

namespace Lamping.Checks.FanAppAllocatedChildReachable.Parents
open AG Graph Lambda Lambda.Labelled Base
abbrev outerBody : Term := .app (.app (.var 0) (.var 1)) (.var 1)
abbrev innerBody : Term := .app (.var 0) (.var 1)
def embedN (n : (encode 0 inner).N) : (encode 0 term).N := .inr (.inl n)
def embedW (w : (encode 0 inner).W) : (encode 0 term).W := .inl (.inr (.inl w))
def liftFnW (w : (encode 0 fnTerm).W) : (encode 0 term).W := embedW (.inl (.inr (.inl w)))
def liftFBodyW (w : (encode 0 fnBody).W) : (encode 0 fnTerm).W := .inl (.inr w)
def liftXBodyW (w : (encode 0 outerBody).W) : (encode 0 fnBody).W := .inl (.inr w)
def liftInnerN (n : (encode 0 innerBody).N) : (encode 0 term).N :=
  embedN (.inr (.inl (.inr (.inr (.inr (.inl n))))))
def liftInnerW (w : (encode 0 innerBody).W) : (encode 0 outerBody).W := .inl (.inr (.inl w))

def nroot : (encode 0 term).N := outerApp
def kroot : concrete.Kept := ⟨nroot,by constructor <;> intro h <;> cases h⟩
def qroot : actualFanPresentation.Kept := ⟨.inl kroot,by
  constructor <;> intro h <;> have same:=congrArg Subtype.val (Sum.inl.inj h) <;> cases same⟩

def nx : (encode 0 term).N := embedN (.inr (.inl (.inr (.inl ()))))
def kx : concrete.Kept := ⟨nx,by constructor <;> intro h <;> cases h⟩
def qx : actualFanPresentation.Kept := ⟨.inl kx,by
  constructor <;> intro h <;> have same:=congrArg Subtype.val (Sum.inl.inj h) <;> cases same⟩

def nouter : (encode 0 term).N := embedN (.inr (.inl (.inr (.inr (.inl (.inl ()))))))
def kouter : concrete.Kept := ⟨nouter,by constructor <;> intro h <;> cases h⟩
def qouter : actualFanPresentation.Kept := ⟨.inl kouter,by
  constructor <;> intro h <;> have same:=congrArg Subtype.val (Sum.inl.inj h) <;> cases same⟩

def ninner : (encode 0 term).N := liftInnerN (.inl (.inl ()))
def kinner : concrete.Kept := ⟨ninner,by constructor <;> intro h <;> cases h⟩
def qinner : actualFanPresentation.Kept := ⟨.inl kinner,by
  constructor <;> intro h <;> have same:=congrArg Subtype.val (Sum.inl.inj h) <;> cases same⟩

def nleftVar : (encode 0 term).N := liftInnerN (.inr (.inr ()))
def kleftVar : concrete.Kept := ⟨nleftVar,by constructor <;> intro h <;> cases h⟩
def qleftVar : actualFanPresentation.Kept := ⟨.inl kleftVar,by
  constructor <;> intro h <;> have same:=congrArg Subtype.val (Sum.inl.inj h) <;> cases same⟩

def nleftBra : (encode 0 term).N := liftInnerN (.inl (.inr (.inl ⟨1,rfl⟩)))
def kleftBra : concrete.Kept := ⟨nleftBra,by constructor <;> intro h <;> cases h⟩
def qleftBra : actualFanPresentation.Kept := ⟨.inl kleftBra,by
  constructor <;> intro h <;> have same:=congrArg Subtype.val (Sum.inl.inj h) <;> cases same⟩

def nrightVar : (encode 0 term).N := embedN (.inr (.inl (.inr (.inr (.inr (.inr ()))))))
def krightVar : concrete.Kept := ⟨nrightVar,by constructor <;> intro h <;> cases h⟩
def qrightVar : actualFanPresentation.Kept := ⟨.inl krightVar,by
  constructor <;> intro h <;> have same:=congrArg Subtype.val (Sum.inl.inj h) <;> cases same⟩

def nrightBra : (encode 0 term).N := embedN (.inr (.inl (.inr (.inr (.inl (.inr (.inl ⟨1,rfl⟩)))))))
def krightBra : concrete.Kept := ⟨nrightBra,by constructor <;> intro h <;> cases h⟩
def qrightBra : actualFanPresentation.Kept := ⟨.inl krightBra,by
  constructor <;> intro h <;> have same:=congrArg Subtype.val (Sum.inl.inj h) <;> cases same⟩

def wroot : (encode 0 term).W := outerFnWire
def oroot : concrete.Outside := ⟨wroot,by
  rintro ⟨d,h⟩;simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h <;> cases h⟩
def vroot : actualFanPresentation.Outside := ⟨.inl (.inl oroot),by
  rintro ⟨d,h⟩;simp only [actualFanLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h|h <;> cases h⟩

def wx : (encode 0 term).W := liftFnW (.inr (.inl ()))
def ox : concrete.Outside := ⟨wx,by
  rintro ⟨d,h⟩;simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h <;> cases h⟩
def vx : actualFanPresentation.Outside := ⟨.inl (.inl ox),by
  rintro ⟨d,h⟩;simp only [actualFanLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h|h <;> cases h⟩

def wouter : (encode 0 term).W := liftFnW (liftFBodyW (.inr (.inl ())))
def oouter : concrete.Outside := ⟨wouter,by
  rintro ⟨d,h⟩;simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h <;> cases h⟩
def vouter : actualFanPresentation.Outside := ⟨.inl (.inl oouter),by
  rintro ⟨d,h⟩;simp only [actualFanLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h|h <;> cases h⟩

def winner : (encode 0 term).W := liftFnW (liftFBodyW (liftXBodyW (.inr (.inl (.inl ())))))
def oinner : concrete.Outside := ⟨winner,by
  rintro ⟨d,h⟩;simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h <;> cases h⟩
def vinner : actualFanPresentation.Outside := ⟨.inl (.inl oinner),by
  rintro ⟨d,h⟩;simp only [actualFanLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h|h <;> cases h⟩

def wleftVar : (encode 0 term).W := liftFnW (liftFBodyW (liftXBodyW (liftInnerW (.inr (.inr (.inl ()))))))
def oleftVar : concrete.Outside := ⟨wleftVar,by
  rintro ⟨d,h⟩;simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h <;> cases h⟩
def vleftVar : actualFanPresentation.Outside := ⟨.inl (.inl oleftVar),by
  rintro ⟨d,h⟩;simp only [actualFanLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h|h <;> cases h⟩

def wleftInput : (encode 0 term).W := liftFnW (liftFBodyW (liftXBodyW (liftInnerW (.inr (.inr (.inr ⟨1,rfl⟩))))))
def oleftInput : concrete.Outside := ⟨wleftInput,by
  rintro ⟨d,h⟩;simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h <;> cases h⟩
def vleftInput : actualFanPresentation.Outside := ⟨.inl (.inl oleftInput),by
  rintro ⟨d,h⟩;simp only [actualFanLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h|h <;> cases h⟩

def wleftFan : (encode 0 term).W := liftFnW (liftFBodyW (liftXBodyW (.inr (.inl (.inr ⟨1,Or.inr rfl⟩)))))
def oleftFan : concrete.Outside := ⟨wleftFan,by
  rintro ⟨d,h⟩;simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h <;> cases h⟩
def vleftFan : actualFanPresentation.Outside := ⟨.inl (.inl oleftFan),by
  rintro ⟨d,h⟩;simp only [actualFanLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h|h <;> cases h⟩

def wrightVar : (encode 0 term).W := embedW (.inl (.inr (.inl (.inl (.inr (.inl (.inr (.inr (.inr (.inl ()))))))))))
def orightVar : concrete.Outside := ⟨wrightVar,by
  rintro ⟨d,h⟩;simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h <;> cases h⟩
def vrightVar : actualFanPresentation.Outside := ⟨.inl (.inl orightVar),by
  rintro ⟨d,h⟩;simp only [actualFanLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h|h <;> cases h⟩

def wrightInput : (encode 0 term).W := embedW (.inl (.inr (.inl (.inl (.inr (.inl (.inr (.inr (.inr (.inr ⟨1,rfl⟩))))))))))
def orightInput : concrete.Outside := ⟨wrightInput,by
  rintro ⟨d,h⟩;simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h <;> cases h⟩
def vrightInput : actualFanPresentation.Outside := ⟨.inl (.inl orightInput),by
  rintro ⟨d,h⟩;simp only [actualFanLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h|h <;> cases h⟩

def vctx : actualFanPresentation.Outside := ⟨.inr (.inl false),by
  rintro ⟨d,h⟩;simp only [actualFanLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h|h <;> cases h⟩

def vbody : actualFanPresentation.Outside := ⟨.inr (.inr true),by
  rintro ⟨d,h⟩;simp only [actualFanLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h|h <;> cases h⟩

noncomputable abbrev lambdaNet := actualFanPresentation.site.reduce
noncomputable def bEnd (e : Endpoint actualCut) : Endpoint concrete.site.reduce :=
  AG.plugLeft actualCut (Schema.beta 0).right.net e
noncomputable def fEnd (e : Endpoint cut2) : Endpoint lambdaNet :=
  AG.plugLeft cut2 (Schema.fanAction .lam 0 1 (by decide)).right.net e

theorem beta_root : concrete.site.reduce.wire (bEnd (.inr (.inl (.inl (.inl ())))))=bEnd (.inl ⟨kroot,appCtx⟩) :=
  beta_lift_wire (.inr (.inl (.inl (.inl ())))) (.inl ⟨kroot,appCtx⟩) rfl
theorem lambda_root : lambdaNet.wire (fEnd (.inr (.inl (.inl (.inl ())))))=fEnd (.inl ⟨qroot,appCtx⟩) :=
  action2_lift_wire (.inr (.inl (.inl (.inl ())))) (.inl ⟨qroot,appCtx⟩) beta_root

theorem beta_rootfn : concrete.site.reduce.wire (bEnd (.inl ⟨kroot,.inl ()⟩))=bEnd (.inr (.inr (oroot,false))) :=
  beta_lift_wire (.inl ⟨kroot,.inl ()⟩) (.inr (.inr (oroot,false))) rfl
theorem lambda_rootfn : lambdaNet.wire (fEnd (.inl ⟨qroot,.inl ()⟩))=fEnd (.inr (.inr (vroot,false))) :=
  action2_lift_wire (.inl ⟨qroot,.inl ()⟩) (.inr (.inr (vroot,false))) beta_rootfn

theorem beta_context : concrete.site.reduce.wire (bEnd (.inr (.inr (oroot,true))))=bEnd (.inr (.inl (.inr (.inl false)))) :=
  beta_lift_wire (.inr (.inr (oroot,true))) (.inr (.inl (.inr (.inl false)))) rfl
theorem lambda_context : lambdaNet.wire (fEnd (.inr (.inr (vroot,true))))=fEnd (.inr (.inr (vctx,false))) :=
  action2_lift_wire (.inr (.inr (vroot,true))) (.inr (.inr (vctx,false))) beta_context

theorem beta_body : concrete.site.reduce.wire (bEnd (.inr (.inl (.inr (.inr true)))))=bEnd (.inr (.inr (ox,false))) :=
  beta_lift_wire (.inr (.inl (.inr (.inr true)))) (.inr (.inr (ox,false))) rfl
theorem lambda_body : lambdaNet.wire (fEnd (.inr (.inr (vbody,false))))=fEnd (.inr (.inr (vx,false))) :=
  action2_lift_wire (.inr (.inr (vbody,false))) (.inr (.inr (vx,false))) beta_body

theorem beta_x : concrete.site.reduce.wire (bEnd (.inr (.inr (ox,true))))=bEnd (.inl ⟨kx,.inl ()⟩) :=
  beta_lift_wire (.inr (.inr (ox,true))) (.inl ⟨kx,.inl ()⟩) rfl
theorem lambda_x : lambdaNet.wire (fEnd (.inr (.inr (vx,true))))=fEnd (.inl ⟨qx,.inl ()⟩) :=
  action2_lift_wire (.inr (.inr (vx,true))) (.inl ⟨qx,.inl ()⟩) beta_x

theorem beta_xbody : concrete.site.reduce.wire (bEnd (.inl ⟨kx,lamBody⟩))=bEnd (.inr (.inr (oouter,false))) :=
  beta_lift_wire (.inl ⟨kx,lamBody⟩) (.inr (.inr (oouter,false))) rfl
theorem lambda_xbody : lambdaNet.wire (fEnd (.inl ⟨qx,lamBody⟩))=fEnd (.inr (.inr (vouter,false))) :=
  action2_lift_wire (.inl ⟨qx,lamBody⟩) (.inr (.inr (vouter,false))) beta_xbody

theorem beta_outer : concrete.site.reduce.wire (bEnd (.inr (.inr (oouter,true))))=bEnd (.inl ⟨kouter,appCtx⟩) :=
  beta_lift_wire (.inr (.inr (oouter,true))) (.inl ⟨kouter,appCtx⟩) rfl
theorem lambda_outer : lambdaNet.wire (fEnd (.inr (.inr (vouter,true))))=fEnd (.inl ⟨qouter,appCtx⟩) :=
  action2_lift_wire (.inr (.inr (vouter,true))) (.inl ⟨qouter,appCtx⟩) beta_outer

theorem beta_outerfn : concrete.site.reduce.wire (bEnd (.inl ⟨kouter,.inl ()⟩))=bEnd (.inr (.inr (oinner,false))) :=
  beta_lift_wire (.inl ⟨kouter,.inl ()⟩) (.inr (.inr (oinner,false))) rfl
theorem lambda_outerfn : lambdaNet.wire (fEnd (.inl ⟨qouter,.inl ()⟩))=fEnd (.inr (.inr (vinner,false))) :=
  action2_lift_wire (.inl ⟨qouter,.inl ()⟩) (.inr (.inr (vinner,false))) beta_outerfn

theorem beta_inner : concrete.site.reduce.wire (bEnd (.inr (.inr (oinner,true))))=bEnd (.inl ⟨kinner,appCtx⟩) :=
  beta_lift_wire (.inr (.inr (oinner,true))) (.inl ⟨kinner,appCtx⟩) rfl
theorem lambda_inner : lambdaNet.wire (fEnd (.inr (.inr (vinner,true))))=fEnd (.inl ⟨qinner,appCtx⟩) :=
  action2_lift_wire (.inr (.inr (vinner,true))) (.inl ⟨qinner,appCtx⟩) beta_inner

theorem beta_innerarg : concrete.site.reduce.wire (bEnd (.inl ⟨kinner,appArg⟩))=bEnd (.inr (.inr (oleftVar,false))) :=
  beta_lift_wire (.inl ⟨kinner,appArg⟩) (.inr (.inr (oleftVar,false))) rfl
theorem lambda_innerarg : lambdaNet.wire (fEnd (.inl ⟨qinner,appArg⟩))=fEnd (.inr (.inr (vleftVar,false))) :=
  action2_lift_wire (.inl ⟨qinner,appArg⟩) (.inr (.inr (vleftVar,false))) beta_innerarg

theorem beta_leftvaraux : concrete.site.reduce.wire (bEnd (.inr (.inr (oleftVar,true))))=bEnd (.inl ⟨kleftVar,.inr ()⟩) :=
  beta_lift_wire (.inr (.inr (oleftVar,true))) (.inl ⟨kleftVar,.inr ()⟩) rfl
theorem lambda_leftvaraux : lambdaNet.wire (fEnd (.inr (.inr (vleftVar,true))))=fEnd (.inl ⟨qleftVar,.inr ()⟩) :=
  action2_lift_wire (.inr (.inr (vleftVar,true))) (.inl ⟨qleftVar,.inr ()⟩) beta_leftvaraux

theorem beta_leftvar : concrete.site.reduce.wire (bEnd (.inl ⟨kleftVar,.inl ()⟩))=bEnd (.inr (.inr (oleftInput,true))) :=
  beta_lift_wire (.inl ⟨kleftVar,.inl ()⟩) (.inr (.inr (oleftInput,true))) rfl
theorem lambda_leftvar : lambdaNet.wire (fEnd (.inl ⟨qleftVar,.inl ()⟩))=fEnd (.inr (.inr (vleftInput,true))) :=
  action2_lift_wire (.inl ⟨qleftVar,.inl ()⟩) (.inr (.inr (vleftInput,true))) beta_leftvar

theorem beta_leftbraaux : concrete.site.reduce.wire (bEnd (.inr (.inr (oleftInput,false))))=bEnd (.inl ⟨kleftBra,.inr ()⟩) :=
  beta_lift_wire (.inr (.inr (oleftInput,false))) (.inl ⟨kleftBra,.inr ()⟩) rfl
theorem lambda_leftbraaux : lambdaNet.wire (fEnd (.inr (.inr (vleftInput,false))))=fEnd (.inl ⟨qleftBra,.inr ()⟩) :=
  action2_lift_wire (.inr (.inr (vleftInput,false))) (.inl ⟨qleftBra,.inr ()⟩) beta_leftbraaux

theorem beta_leftbra : concrete.site.reduce.wire (bEnd (.inl ⟨kleftBra,.inl ()⟩))=bEnd (.inr (.inr (oleftFan,true))) :=
  beta_lift_wire (.inl ⟨kleftBra,.inl ()⟩) (.inr (.inr (oleftFan,true))) rfl
theorem lambda_leftbra : lambdaNet.wire (fEnd (.inl ⟨qleftBra,.inl ()⟩))=fEnd (.inr (.inr (vleftFan,true))) :=
  action2_lift_wire (.inl ⟨qleftBra,.inl ()⟩) (.inr (.inr (vleftFan,true))) beta_leftbra

theorem beta_leftfan : concrete.site.reduce.wire (bEnd (.inr (.inr (oleftFan,false))))=bEnd (.inl ⟨fanKept,.inr false⟩) :=
  beta_lift_wire (.inr (.inr (oleftFan,false))) (.inl ⟨fanKept,.inr false⟩) rfl
theorem lambda_leftfan : lambdaNet.wire (fEnd (.inr (.inr (vleftFan,false))))=fEnd (.inr (.inl (.inr (.inl false)))) :=
  action2_lift_wire (.inr (.inr (vleftFan,false))) (.inr (.inl (.inr (.inl false)))) beta_leftfan

theorem beta_outerarg : concrete.site.reduce.wire (bEnd (.inl ⟨kouter,appArg⟩))=bEnd (.inr (.inr (orightVar,false))) :=
  beta_lift_wire (.inl ⟨kouter,appArg⟩) (.inr (.inr (orightVar,false))) rfl
theorem lambda_outerarg : lambdaNet.wire (fEnd (.inl ⟨qouter,appArg⟩))=fEnd (.inr (.inr (vrightVar,false))) :=
  action2_lift_wire (.inl ⟨qouter,appArg⟩) (.inr (.inr (vrightVar,false))) beta_outerarg

theorem beta_rightvaraux : concrete.site.reduce.wire (bEnd (.inr (.inr (orightVar,true))))=bEnd (.inl ⟨krightVar,.inr ()⟩) :=
  beta_lift_wire (.inr (.inr (orightVar,true))) (.inl ⟨krightVar,.inr ()⟩) rfl
theorem lambda_rightvaraux : lambdaNet.wire (fEnd (.inr (.inr (vrightVar,true))))=fEnd (.inl ⟨qrightVar,.inr ()⟩) :=
  action2_lift_wire (.inr (.inr (vrightVar,true))) (.inl ⟨qrightVar,.inr ()⟩) beta_rightvaraux

theorem beta_rightvar : concrete.site.reduce.wire (bEnd (.inl ⟨krightVar,.inl ()⟩))=bEnd (.inr (.inr (orightInput,true))) :=
  beta_lift_wire (.inl ⟨krightVar,.inl ()⟩) (.inr (.inr (orightInput,true))) rfl
theorem lambda_rightvar : lambdaNet.wire (fEnd (.inl ⟨qrightVar,.inl ()⟩))=fEnd (.inr (.inr (vrightInput,true))) :=
  action2_lift_wire (.inl ⟨qrightVar,.inl ()⟩) (.inr (.inr (vrightInput,true))) beta_rightvar

theorem beta_rightbraaux : concrete.site.reduce.wire (bEnd (.inr (.inr (orightInput,false))))=bEnd (.inl ⟨krightBra,.inr ()⟩) :=
  beta_lift_wire (.inr (.inr (orightInput,false))) (.inl ⟨krightBra,.inr ()⟩) rfl
theorem lambda_rightbraaux : lambdaNet.wire (fEnd (.inr (.inr (vrightInput,false))))=fEnd (.inl ⟨qrightBra,.inr ()⟩) :=
  action2_lift_wire (.inr (.inr (vrightInput,false))) (.inl ⟨qrightBra,.inr ()⟩) beta_rightbraaux

theorem beta_rightbra : concrete.site.reduce.wire (bEnd (.inl ⟨krightBra,.inl ()⟩))=bEnd (.inl ⟨fanKept,.inr true⟩) :=
  beta_lift_wire (.inl ⟨krightBra,.inl ()⟩) (.inl ⟨fanKept,.inr true⟩) rfl
theorem lambda_rightbra : lambdaNet.wire (fEnd (.inl ⟨qrightBra,.inl ()⟩))=fEnd (.inr (.inl (.inr (.inl true)))) :=
  action2_lift_wire (.inl ⟨qrightBra,.inl ()⟩) (.inr (.inl (.inr (.inl true)))) beta_rightbra

theorem lambda_context_body : lambdaNet.wire (fEnd (.inr (.inr (vctx,true))))=
    fEnd (.inr (.inr (vbody,true))) := by
  exact action2_lift_wire (.inr (.inr (vctx,true))) (.inr (.inr (vbody,true))) rfl

noncomputable def outerEdges : List (Endpoint lambdaNet) := [
  fEnd (.inr (.inl (.inl (.inl ())))),fEnd (.inl ⟨qroot,.inl ()⟩),
  fEnd (.inr (.inr (vroot,true))),fEnd (.inr (.inr (vctx,true))),
  fEnd (.inr (.inr (vbody,false))),fEnd (.inr (.inr (vx,true))),
  fEnd (.inl ⟨qx,lamBody⟩),fEnd (.inr (.inr (vouter,true)))]

theorem outerLabels (a : Context) : Labelling lambdaNet outerEdges a a := by
  apply Labelling.cons (by rw [lambda_root];exact LabelledTurn.node (g:=lambdaNet) (.inl qroot) appCtx (.inl ()) (.direct (.appFun a)))
  apply Labelling.cons (by rw [lambda_rootfn];exact .transparent _ false a)
  apply Labelling.cons (by rw [lambda_context];exact .transparent _ false a)
  apply Labelling.cons (by rw [lambda_context_body];exact .transparent _ true a)
  apply Labelling.cons (by rw [lambda_body];exact .transparent _ false a)
  apply Labelling.cons (by rw [lambda_x];exact LabelledTurn.node (g:=lambdaNet) (.inl qx) (Sum.inl ()) lamBody (.direct (.lamBody a)))
  exact .cons (by rw [lambda_xbody];exact .transparent _ false a) (.single _ a)

theorem outerWord : accessWord lambdaNet outerEdges=[.fn,.body] := rfl

theorem outerFinish : outerEdges.getLast?=some (lambdaNet.wire (fEnd (.inl ⟨qouter,appCtx⟩))) := by
  have inverse:=congrArg lambdaNet.wire lambda_outer
  simp only [Pairing.involutive] at inverse
  simpa only [outerEdges,List.getLast?_cons_cons,List.getLast?_singleton] using congrArg some inverse

noncomputable def front (b : Bool) : Endpoint lambdaNet := .inr (.inr (.inr (.inl b),true))
theorem front_finish (b : Bool) : lambdaNet.wire (front b)=.inl ⟨.inr (.inl b),.inl ()⟩ := rfl

abbrev pairContext := Context.empty.cons (.pair .empty .empty)
private theorem empty_replace (n : Nat) : Context.empty.replace n Context.empty=Context.empty := by
  ext k;simp [Context.replace]
private theorem emptyCro : Traversal 1 (.op .cro) (.inr ()) (.inl ()) Context.empty Context.empty := by
  simpa only [Context.cons_empty,empty_replace] using (Traversal.direct (Passage.cro (i:=1) Context.empty Context.empty))
private theorem emptyBra : Traversal 0 (.op .bra) (.inr ()) (.inl ()) Context.empty pairContext := by
  simpa only [Context.cons_empty,Context.replace_zero] using (Traversal.direct (Passage.bra (i:=0) Context.empty Context.empty .empty .empty))

noncomputable def leftTail : List (Endpoint lambdaNet) := [
  fEnd (.inl ⟨qouter,.inl ()⟩),fEnd (.inr (.inr (vinner,true))),
  fEnd (.inl ⟨qinner,appArg⟩),fEnd (.inr (.inr (vleftVar,true))),
  fEnd (.inl ⟨qleftVar,.inl ()⟩),fEnd (.inr (.inr (vleftInput,false))),
  fEnd (.inl ⟨qleftBra,.inl ()⟩),fEnd (.inr (.inr (vleftFan,false))),front false]

theorem leftTailLabels : Labelling lambdaNet leftTail Context.empty pairContext := by
  apply Labelling.cons (by rw [lambda_outerfn];exact .transparent _ false Context.empty)
  apply Labelling.cons (by rw [lambda_inner];exact LabelledTurn.node (g:=lambdaNet) (.inl qinner) appCtx appArg (.direct (.appArg Context.empty)))
  apply Labelling.cons (by rw [lambda_innerarg];exact .transparent _ false Context.empty)
  apply Labelling.cons (by rw [lambda_leftvaraux];exact LabelledTurn.node (g:=lambdaNet) (.inl qleftVar) _ _ emptyCro)
  apply Labelling.cons (by rw [lambda_leftvar];exact .transparent _ true Context.empty)
  apply Labelling.cons (by rw [lambda_leftbraaux];exact LabelledTurn.node (g:=lambdaNet) (.inl qleftBra) _ _ emptyBra)
  apply Labelling.cons (by rw [lambda_leftbra];exact .transparent _ true pairContext)
  exact .cons (by rw [lambda_leftfan];exact .transparent _ false pairContext) (.single _ _)

noncomputable def rightTail : List (Endpoint lambdaNet) := [
  fEnd (.inl ⟨qouter,appArg⟩),fEnd (.inr (.inr (vrightVar,true))),
  fEnd (.inl ⟨qrightVar,.inl ()⟩),fEnd (.inr (.inr (vrightInput,false))),
  fEnd (.inl ⟨qrightBra,.inl ()⟩),front true]

theorem rightTailLabels : Labelling lambdaNet rightTail Context.empty pairContext := by
  apply Labelling.cons (by rw [lambda_outerarg];exact .transparent _ false Context.empty)
  apply Labelling.cons (by rw [lambda_rightvaraux];exact LabelledTurn.node (g:=lambdaNet) (.inl qrightVar) _ _ emptyCro)
  apply Labelling.cons (by rw [lambda_rightvar];exact .transparent _ true Context.empty)
  apply Labelling.cons (by rw [lambda_rightbraaux];exact LabelledTurn.node (g:=lambdaNet) (.inl qrightBra) _ _ emptyBra)
  exact .cons (by rw [lambda_rightbra];exact .transparent _ false pairContext) (.single _ _)

noncomputable def leftEdges := outerEdges++leftTail
noncomputable def rightEdges := outerEdges++rightTail

theorem leftLabels : Labelling lambdaNet leftEdges Context.empty pairContext := by
  exact (outerLabels Context.empty).append_seam leftTailLabels (by
    intro e f last first
    have he:=Option.some.inj (last.symm.trans outerFinish)
    have hf:=Option.some.inj first
    subst e;subst f
    rw [Pairing.involutive]
    exact LabelledTurn.node (g:=lambdaNet) (.inl qouter) appCtx (.inl ()) (.direct (.appFun Context.empty)))

theorem rightLabels : Labelling lambdaNet rightEdges Context.empty pairContext := by
  exact (outerLabels Context.empty).append_seam rightTailLabels (by
    intro e f last first
    have he:=Option.some.inj (last.symm.trans outerFinish)
    have hf:=Option.some.inj first
    subst e;subst f
    rw [Pairing.involutive]
    exact LabelledTurn.node (g:=lambdaNet) (.inl qouter) appCtx appArg (.direct (.appArg Context.empty)))

theorem leftWord : accessWord lambdaNet leftEdges=Syntax.left := by
  rw [leftEdges,accessWord_append lambdaNet _ _ (outerLabels Context.empty).nonempty,outerWord]
  rfl
theorem rightWord : accessWord lambdaNet rightEdges=Syntax.right := by
  rw [rightEdges,accessWord_append lambdaNet _ _ (outerLabels Context.empty).nonempty,outerWord]
  rfl

theorem leftFinish : leftEdges.getLast?=some (lambdaNet.wire (.inl ⟨.inr (.inl false),.inl ()⟩)) := by
  rw [leftEdges,List.getLast?_append]
  have inverse:=congrArg lambdaNet.wire (front_finish false)
  simp only [Pairing.involutive] at inverse
  simpa only [leftTail,List.getLast?_cons_cons,List.getLast?_singleton,Option.some_or] using congrArg some inverse

theorem rightFinish : rightEdges.getLast?=some (lambdaNet.wire (.inl ⟨.inr (.inl true),.inl ()⟩)) := by
  rw [rightEdges,List.getLast?_append]
  have inverse:=congrArg lambdaNet.wire (front_finish true)
  simp only [Pairing.involutive] at inverse
  simpa only [rightTail,List.getLast?_cons_cons,List.getLast?_singleton,Option.some_or] using congrArg some inverse

noncomputable def leftParent : RootAccess lambdaNet (.inl ()) := by
  let flow:=Classical.choose lambda_certified
  exact ⟨leftEdges,⟨⟨⟨Context.empty,pairContext,leftLabels⟩,
    leftLabels.root_forward_of_flow flow (.inl ()) rfl rfl⟩,rfl,⟨.lam,by
      unfold accessKind;rw [leftFinish];simp only [Option.bind_some,Pairing.involutive];rfl⟩⟩⟩
noncomputable def rightParent : RootAccess lambdaNet (.inl ()) := by
  let flow:=Classical.choose lambda_certified
  exact ⟨rightEdges,⟨⟨⟨Context.empty,pairContext,rightLabels⟩,
    rightLabels.root_forward_of_flow flow (.inl ()) rfl rfl⟩,rfl,⟨.lam,by
      unfold accessKind;rw [rightFinish];simp only [Option.bind_some,Pairing.involutive];rfl⟩⟩⟩
#print axioms leftParent
#print axioms rightParent
#print axioms leftWord
#print axioms rightWord

def copiedLambda (b : Bool) : fanCro.Kept := ⟨.inr (.inl b),by constructor <;> intro h <;> cases h⟩
noncomputable def chosenParent (b : Bool) : RootAccess lambdaNet (.inl ()) :=
  if b then rightParent else leftParent

theorem chosenWord (b : Bool) : accessWord lambdaNet (chosenParent b).val=
    if b then Syntax.right else Syntax.left := by
  cases b
  · exact leftWord
  · exact rightWord

theorem chosenFinish (b : Bool) : (chosenParent b).val.getLast?=
    some (lambdaNet.wire (.inl ⟨.inr (.inl b),.inl ()⟩)) := by
  cases b
  · exact leftFinish
  · exact rightFinish

noncomputable def sourceParent (b : Bool) : RootAccess fanCro.site.net (.inl ()) :=
  fanCro.sourceIso.rootAccessBij (.inl ()) (chosenParent b)

theorem sourceWord (b : Bool) : accessWord fanCro.site.net (sourceParent b).val=
    if b then Syntax.right else Syntax.left :=
  (fanCro.sourceIso.accessWord (chosenParent b).val).trans (chosenWord b)

theorem sourceFinish (b : Bool) : (sourceParent b).val.getLast?=
    some (fanCro.site.net.wire (.inl ⟨.inl (copiedLambda b),.inl ()⟩)) := by
  change ((chosenParent b).val.map fanCro.sourceIso.ends).getLast?=_
  rw [List.getLast?_map,chosenFinish]
  simp only [Option.map_some]
  apply congrArg some
  rw [fanCro.sourceIso.wiring]
  apply congrArg fanCro.site.net.wire
  apply fanCro.sourceIso.symm.ends.injective
  change fanCro.sourceIso.ends.invFun (fanCro.sourceIso.ends.toFun (.inl ⟨.inr (.inl b),.inl ()⟩)) =
    fanCro.sourceIso.ends.invFun (.inl ⟨.inl (copiedLambda b),.inl ()⟩)
  rw [fanCro.sourceIso.ends.left_inv]
  rfl

def parentPosition (b : Bool) : Position current.erase :=
  ⟨if b then Syntax.right else Syntax.left,by cases b <;> rfl⟩
noncomputable def targetParent (b : Bool) : RootAccess fanCro.site.reduce (.inl ()) :=
  Classical.choose (Matches.observation fanCro.site.reduce actual_final_matches (parentPosition b))

theorem targetWord (b : Bool) : accessWord fanCro.site.reduce (targetParent b).val=
    if b then Syntax.right else Syntax.left :=
  (Classical.choose_spec (Matches.observation fanCro.site.reduce actual_final_matches (parentPosition b))).1

theorem targetFinish (b : Bool) : (targetParent b).val.getLast?=
    some (fanCro.site.reduce.wire (.inl ⟨.inl (copiedLambda b),.inl ()⟩)) := by
  obtain ⟨port,finish⟩ := fanCro.site.fan_control_access_kept (Or.inr (Or.inl rfl)) (targetParent b)
  obtain ⟨a,c,labels⟩ := (targetParent b).property.1.1
  obtain ⟨principal⟩ := fanCro.site.actionPrincipal_exists
  obtain ⟨flow,_,_,_,_⟩ := lambda_certified
  have normalized := fanCro.site.action_kept_canonical_access (.fan .cro 0 1 (by decide))
    (fanCro.sourceIso.flowBalance flow) (.inl ()) rfl Base.actual_source_matches principal
    (sourceParent b) (targetParent b) ((sourceWord b).trans (targetWord b).symm)
    port.1 port.2 finish labels
  have wireEq := Option.some.inj ((sourceFinish b).symm.trans normalized.2.2)
  have endEq := congrArg fanCro.site.net.wire wireEq
  simp only [Pairing.involutive] at endEq
  rcases port with ⟨node,p⟩
  have nodeEq : copiedLambda b=node := Sum.inl.inj (congrArg Sigma.fst (Sum.inl.inj endEq))
  subst node
  have portEq : (Sum.inl () : Port (fanCro.kept (copiedLambda b)).sort)=p :=
    eq_of_heq (Sigma.mk.inj (Sum.inl.inj endEq)).2
  subst p
  exact finish
#print axioms sourceFinish
#print axioms targetFinish


end Lamping.Checks.FanAppAllocatedChildReachable.Parents

namespace Lamping.Checks.FanAppAllocatedChildReachable.Domain
open AG Graph Lambda Lambda.Labelled Base
-- The parent is the payload's OUTER APP. The selected fourth-site APP is its FN child.
def originalOuter : (encode 1 argument).N := .inr (.inl (.inl ()))
def oldOuter : (encode 0 term).N := .inr (.inl (.inr (.inr originalOuter)))
def outerKept : concrete.Kept := ⟨oldOuter,by constructor <;> intro h <;> cases h⟩
def outerKept2 : actualFanPresentation.Kept := ⟨.inl outerKept,by
  constructor <;> intro h <;> have same:=congrArg Subtype.val (Sum.inl.inj h) <;> cases same⟩
def outerKept3 : fanCro.Kept := ⟨.inl outerKept2,by
  constructor
  · intro h;cases h
  · intro h;have same:=congrArg Subtype.val (Sum.inl.inj h)
    have prior:=congrArg Subtype.val (Sum.inl.inj same);cases prior⟩
noncomputable def thirdOuterNode : fanCro.Kept⊕(Bool⊕Unit) := .inl outerKept3
def bodyRootWire : (encode 0 term).W := wrapArgWire (.inr (.inl ()))
def bodyRootOutside : concrete.Outside := ⟨bodyRootWire,by
  rintro ⟨d,h⟩;simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h <;> cases h⟩
theorem beta_body_start : concrete.site.reduce.wire (.inl ⟨rhsLambda,lamBody⟩)=
    .inr (.inr (.inl (.inl bodyRootOutside),false)) :=
  beta_lift_wire (.inl ⟨argKept,lamBody⟩) (.inr (.inr (bodyRootOutside,false))) rfl
theorem beta_body_finish : concrete.site.reduce.wire (.inr (.inr (.inl (.inl bodyRootOutside),true)))=
    .inl ⟨.inl outerKept,appCtx⟩ :=
  beta_lift_wire (.inr (.inr (bodyRootOutside,true))) (.inl ⟨outerKept,appCtx⟩) rfl

def bodyRootOutside2 : actualFanPresentation.Outside := ⟨.inl (.inl bodyRootOutside),by
  rintro ⟨d,h⟩;simp only [actualFanLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h|h <;> cases h⟩
theorem lambda_body_exit : actualFanPresentation.site.reduce.wire
    (.inr (.inr (.inr (.inr true),false)))=.inr (.inr (.inl (.inl bodyRootOutside2),false)) :=
  action2_lift_wire (.inr (.inl (.inr (.inr true)))) (.inr (.inr (bodyRootOutside2,false))) beta_body_start
theorem lambda_body_finish : actualFanPresentation.site.reduce.wire
    (.inr (.inr (.inl (.inl bodyRootOutside2),true)))=.inl ⟨.inl outerKept2,appCtx⟩ :=
  action2_lift_wire (.inr (.inr (bodyRootOutside2,true))) (.inl ⟨outerKept2,appCtx⟩) beta_body_finish

def bodyControl3 : fanCro.Kept := ⟨.inr (.inr true),by constructor <;> intro h <;> cases h⟩
def bodyFront3 : fanCro.Outside := ⟨.inr (.inr true),by
  rintro ⟨d,h⟩;simp only [actualFanCroCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h <;> cases h⟩
def bodyRoot3 : fanCro.Outside := ⟨.inl (.inl bodyRootOutside2),by
  rintro ⟨d,h⟩;simp only [actualFanCroCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h <;> cases h⟩
theorem third_body_start (branch : Bool) : fanCro.site.reduce.wire
    (.inl ⟨.inl (Parents.copiedLambda branch),lamBody⟩)=
    .inl ⟨.inl bodyControl3,.inr branch⟩ :=
  action3_lift_wire (.inl ⟨Parents.copiedLambda branch,lamBody⟩) (.inl ⟨bodyControl3,.inr branch⟩) rfl
theorem third_body_control : fanCro.site.reduce.wire (.inl ⟨.inl bodyControl3,.inl ()⟩)=
    .inr (.inr (.inl (.inl bodyFront3),true)) :=
  action3_lift_wire (.inl ⟨bodyControl3,.inl ()⟩) (.inr (.inr (bodyFront3,true))) rfl
theorem third_body_exit : fanCro.site.reduce.wire (.inr (.inr (.inl (.inl bodyFront3),false)))=
    .inr (.inr (.inl (.inl bodyRoot3),false)) :=
  action3_lift_wire (.inr (.inr (bodyFront3,false))) (.inr (.inr (bodyRoot3,false))) lambda_body_exit
theorem third_body_finish : fanCro.site.reduce.wire (.inr (.inr (.inl (.inl bodyRoot3),true)))=
    .inl ⟨thirdOuterNode,appCtx⟩ :=
  action3_lift_wire (.inr (.inr (bodyRoot3,true))) (.inl ⟨outerKept3,appCtx⟩) lambda_body_finish

noncomputable def bodyTail (branch : Bool) : List (Endpoint fanCro.site.reduce) := [
 .inl ⟨.inl (Parents.copiedLambda branch),lamBody⟩,
 .inl ⟨.inl bodyControl3,.inl ()⟩,
 .inr (.inr (.inl (.inl bodyFront3),false)),
 .inr (.inr (.inl (.inl bodyRoot3),true))]
theorem bodyTailLabels (branch : Bool) (a : Context) : Labelling fanCro.site.reduce (bodyTail branch) a (InitialOffsets.fanAt 0 branch a) := by
  apply Labelling.cons (by rw [third_body_start];exact LabelledTurn.node (g:=fanCro.site.reduce) (.inl bodyControl3) _ _ (.direct (InitialOffsets.Event.apply_rel (.fan 0 branch) a)))
  apply Labelling.cons (by rw [third_body_control];exact LabelledTurn.transparent (g:=fanCro.site.reduce) (.inl (.inl bodyFront3)) true _)
  exact .cons (by rw [third_body_exit];exact LabelledTurn.transparent (g:=fanCro.site.reduce) (.inl (.inl bodyRoot3)) false _) (.single _ _)
theorem bodyTailWord (branch : Bool) : (bodyTail branch).flatMap (arrivalWord fanCro.site.reduce)=[.body] := rfl
theorem bodyTailFinish (branch : Bool) : (bodyTail branch).getLast?=some (fanCro.site.reduce.wire (.inl ⟨thirdOuterNode,appCtx⟩)) := by
  have h:=congrArg fanCro.site.reduce.wire third_body_finish
  simp only [Pairing.involutive] at h
  exact congrArg some h
noncomputable def bodyAppEdges (branch : Bool) := (Parents.targetParent branch).val++bodyTail branch

theorem bodyAppWord (branch : Bool) : accessWord fanCro.site.reduce (bodyAppEdges branch)=Syntax.start branch := by
  obtain ⟨a,b,labels⟩ := (Parents.targetParent branch).property.1.1
  rw [bodyAppEdges,accessWord_append _ _ _ labels.nonempty,
    Parents.targetWord,bodyTailWord]

theorem bodyAppAccessProof (branch : Bool) : IsRootAccess fanCro.site.reduce (.inl ()) (bodyAppEdges branch) := by
  obtain ⟨a,b,labels⟩ := (Parents.targetParent branch).property.1.1
  have whole := labels.append_seam (bodyTailLabels branch b) (by
    intro e f last first
    have he:=Option.some.inj (last.symm.trans (Parents.targetFinish branch))
    have hf:=Option.some.inj first
    subst e;subst f;rw [Pairing.involutive]
    exact LabelledTurn.node (g:=fanCro.site.reduce) (.inl (Parents.copiedLambda branch)) (.inl ()) lamBody (.direct (.lamBody b)))
  obtain ⟨flow,_,_,_,_⟩ := cro_certified
  have head : (bodyAppEdges branch).head?=some (.inr (.inl (.inl ()))) := by
    rw [bodyAppEdges,List.head?_append,(Parents.targetParent branch).property.2.1,Option.some_or]
  have last : (bodyAppEdges branch).getLast?=some (fanCro.site.reduce.wire (.inl ⟨thirdOuterNode,appCtx⟩)) := by
    rw [bodyAppEdges,List.getLast?_append,bodyTailFinish,Option.some_or]
  exact ⟨⟨⟨a,_,whole⟩,whole.root_forward_of_flow flow (.inl ()) head rfl⟩,head,⟨.app,by
    unfold accessKind;rw [last];simp only [Option.bind_some,Pairing.involutive];rfl⟩⟩
noncomputable def bodyAppParent (branch : Bool) : RootAccess fanCro.site.reduce (.inl ()) := ⟨bodyAppEdges branch,bodyAppAccessProof branch⟩
def outerFunctionWire : (encode 0 term).W := wrapArgWire (.inl (.inr (.inr (.inl (.inl ())))))
def outerFnOutside : concrete.Outside := ⟨outerFunctionWire,by
  rintro ⟨d,h⟩;simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h <;> cases h⟩
def outerFnOutside2 : actualFanPresentation.Outside := ⟨.inl (.inl outerFnOutside),by
  rintro ⟨d,h⟩;simp only [actualFanLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h|h <;> cases h⟩
def outerFnOutside3 : fanCro.Outside := ⟨.inl (.inl outerFnOutside2),by
  rintro ⟨d,h⟩;simp only [actualFanCroCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h <;> cases h⟩
theorem beta_outer_fn : concrete.site.reduce.wire (.inl ⟨.inl outerKept,.inl ()⟩)=
    .inr (.inr (.inl (.inl outerFnOutside),false)) :=
  beta_lift_wire (.inl ⟨outerKept,.inl ()⟩) (.inr (.inr (outerFnOutside,false))) rfl
theorem beta_inner_ctx : concrete.site.reduce.wire (.inr (.inr (.inl (.inl outerFnOutside),true)))=
    .inl ⟨.inl appKept,appCtx⟩ :=
  beta_lift_wire (.inr (.inr (outerFnOutside,true))) (.inl ⟨appKept,appCtx⟩) rfl
theorem lambda_outer_fn : actualFanPresentation.site.reduce.wire (.inl ⟨.inl outerKept2,.inl ()⟩)=
    .inr (.inr (.inl (.inl outerFnOutside2),false)) :=
  action2_lift_wire (.inl ⟨outerKept2,.inl ()⟩) (.inr (.inr (outerFnOutside2,false))) beta_outer_fn
theorem lambda_inner_ctx : actualFanPresentation.site.reduce.wire (.inr (.inr (.inl (.inl outerFnOutside2),true)))=
    .inl ⟨.inl appKept2,appCtx⟩ :=
  action2_lift_wire (.inr (.inr (outerFnOutside2,true))) (.inl ⟨appKept2,appCtx⟩) beta_inner_ctx
theorem third_outer_fn : fanCro.site.reduce.wire (.inl ⟨thirdOuterNode,.inl ()⟩)=
    .inr (.inr (.inl (.inl outerFnOutside3),false)) :=
  action3_lift_wire (.inl ⟨outerKept3,.inl ()⟩) (.inr (.inr (outerFnOutside3,false))) lambda_outer_fn
theorem third_inner_ctx : fanCro.site.reduce.wire (.inr (.inr (.inl (.inl outerFnOutside3),true)))=
    .inl ⟨newAppNode,appCtx⟩ :=
  action3_lift_wire (.inr (.inr (outerFnOutside3,true))) (.inl ⟨appKept3,appCtx⟩) lambda_inner_ctx
noncomputable def innerTail : List (Endpoint fanCro.site.reduce) :=
  [.inl ⟨thirdOuterNode,.inl ()⟩,.inr (.inr (.inl (.inl outerFnOutside3),true))]
theorem innerTailLabels (a : Context) : Labelling fanCro.site.reduce innerTail a a :=
  .cons (by rw [third_outer_fn];exact .transparent _ false a) (.single _ _)
theorem innerTailFinish : innerTail.getLast?=some (fanCro.site.reduce.wire (.inl ⟨newAppNode,appCtx⟩)) := by
  have h:=congrArg fanCro.site.reduce.wire third_inner_ctx
  simp only [Pairing.involutive] at h
  exact congrArg some h
noncomputable def innerEdges (branch : Bool) := (bodyAppParent branch).val++innerTail
theorem innerWord (branch : Bool) : accessWord fanCro.site.reduce (innerEdges branch)=Syntax.innerApp branch := by
  obtain ⟨a,b,labels⟩ := (bodyAppParent branch).property.1.1
  rw [innerEdges,accessWord_append _ _ _ labels.nonempty]
  change accessWord fanCro.site.reduce (bodyAppEdges branch)++_=_
  rw [bodyAppWord]
  cases branch <;> rfl
theorem innerAccessProof (branch : Bool) : IsRootAccess fanCro.site.reduce (.inl ()) (innerEdges branch) := by
  obtain ⟨a,b,labels⟩ := (bodyAppParent branch).property.1.1
  have parentLast : (bodyAppParent branch).val.getLast?=some (fanCro.site.reduce.wire (.inl ⟨thirdOuterNode,appCtx⟩)) := by
    change (bodyAppEdges branch).getLast?=_
    rw [bodyAppEdges,List.getLast?_append,bodyTailFinish,Option.some_or]
  have whole := labels.append_seam (innerTailLabels b) (by
    intro e f last first
    have he:=Option.some.inj (last.symm.trans parentLast)
    have hf:=Option.some.inj first
    subst e;subst f;rw [Pairing.involutive]
    exact LabelledTurn.node (g:=fanCro.site.reduce) thirdOuterNode appCtx (.inl ()) (.direct (.appFun b)))
  obtain ⟨flow,_,_,_,_⟩ := cro_certified
  have head : (innerEdges branch).head?=some (.inr (.inl (.inl ()))) := by
    rw [innerEdges,List.head?_append,(bodyAppParent branch).property.2.1,Option.some_or]
  have last : (innerEdges branch).getLast?=some (fanCro.site.reduce.wire (.inl ⟨newAppNode,appCtx⟩)) := by
    rw [innerEdges,List.getLast?_append,innerTailFinish,Option.some_or]
  exact ⟨⟨⟨a,b,whole⟩,whole.root_forward_of_flow flow (.inl ()) head rfl⟩,head,⟨.app,by
    unfold accessKind;rw [last];simp only [Option.bind_some,Pairing.involutive];rfl⟩⟩
noncomputable def innerAccess (branch : Bool) : RootAccess fanCro.site.reduce (.inl ()) := ⟨innerEdges branch,innerAccessProof branch⟩
noncomputable def sourceParent (branch : Bool) : RootAccess fanApp.site.net (.inl ()) :=
  fanApp.sourceIso.rootAccessBij (.inl ()) (bodyAppParent branch)
noncomputable def sourceChild (branch : Bool) : RootAccess fanApp.site.net (.inl ()) :=
  fanApp.sourceIso.rootAccessBij (.inl ()) (innerAccess branch)
theorem sourceParentWord (branch : Bool) : accessWord fanApp.site.net (sourceParent branch).val=Syntax.start branch :=
  (fanApp.sourceIso.accessWord (bodyAppParent branch).val).trans (bodyAppWord branch)
theorem sourceChildWord (branch : Bool) : accessWord fanApp.site.net (sourceChild branch).val=Syntax.innerApp branch :=
  (fanApp.sourceIso.accessWord (innerAccess branch).val).trans (innerWord branch)
theorem sourceChildFinish (branch : Bool) : (sourceChild branch).val.getLast?=
    some (fanApp.site.net.wire (.inl ⟨.inr (.inr ()),appCtx⟩)) := by
  change ((innerAccess branch).val.map fanApp.sourceIso.ends).getLast?=_
  have last : (innerAccess branch).val.getLast?=some (fanCro.site.reduce.wire (.inl ⟨newAppNode,appCtx⟩)) := by
    change (innerEdges branch).getLast?=_
    rw [innerEdges,List.getLast?_append,innerTailFinish,Option.some_or]
  rw [List.getLast?_map,last];simp only [Option.map_some]
  apply congrArg some
  rw [fanApp.sourceIso.wiring]
  apply congrArg fanApp.site.net.wire
  apply fanApp.sourceIso.symm.ends.injective
  change fanApp.sourceIso.ends.invFun (fanApp.sourceIso.ends.toFun (.inl ⟨newAppNode,appCtx⟩))=_
  rw [fanApp.sourceIso.ends.left_inv];rfl
noncomputable def outerKept4 : fanApp.Kept := ⟨thirdOuterNode,by
  constructor
  · intro same;cases same
  · intro same
    have h:=congrArg Subtype.val (Sum.inl.inj same)
    have h2:=congrArg Subtype.val (Sum.inl.inj h)
    have h3:=congrArg Subtype.val (Sum.inl.inj h2)
    cases h3⟩
theorem sourceParentFinish (branch : Bool) : (sourceParent branch).val.getLast?=
    some (fanApp.site.net.wire (.inl ⟨.inl outerKept4,appCtx⟩)) := by
  change ((bodyAppParent branch).val.map fanApp.sourceIso.ends).getLast?=_
  have last : (bodyAppParent branch).val.getLast?=some (fanCro.site.reduce.wire (.inl ⟨thirdOuterNode,appCtx⟩)) := by
    change (bodyAppEdges branch).getLast?=_
    rw [bodyAppEdges,List.getLast?_append,bodyTailFinish,Option.some_or]
  rw [List.getLast?_map,last];simp only [Option.map_some]
  apply congrArg some
  rw [fanApp.sourceIso.wiring]
  apply congrArg fanApp.site.net.wire
  apply fanApp.sourceIso.symm.ends.injective
  change fanApp.sourceIso.ends.invFun (fanApp.sourceIso.ends.toFun (.inl ⟨thirdOuterNode,appCtx⟩))=_
  rw [fanApp.sourceIso.ends.left_inv];rfl
noncomputable def targetParent (branch : Bool) : RootAccess fanApp.site.reduce (.inl ()) :=
  Classical.choose (Matches.observation fanApp.site.reduce actual_target_matches (Syntax.parentPosition branch))
noncomputable def targetChild (branch : Bool) : RootAccess fanApp.site.reduce (.inl ()) :=
  Classical.choose (Matches.observation fanApp.site.reduce actual_target_matches (Syntax.innerPosition branch))
theorem targetParentWord (branch : Bool) : accessWord fanApp.site.reduce (targetParent branch).val=Syntax.start branch :=
  (Classical.choose_spec (Matches.observation fanApp.site.reduce actual_target_matches (Syntax.parentPosition branch))).1
theorem targetChildWord (branch : Bool) : accessWord fanApp.site.reduce (targetChild branch).val=Syntax.innerApp branch :=
  (Classical.choose_spec (Matches.observation fanApp.site.reduce actual_target_matches (Syntax.innerPosition branch))).1
/-- A SOURCE kept parent cannot become a selected copied APP context.
This contradiction is established on SOURCE, not by reversing target Ne. -/
theorem targetParentKept (branch : Bool) : ∃port : NodePort signature fanApp.Kept fanApp.kept,
    (targetParent branch).val.getLast?=some (fanApp.site.reduce.wire (.inl ⟨.inl port.1,port.2⟩)) := by
  rcases fanApp.site.fan_app_access_cases (targetParent branch) with kept|⟨copy,finish⟩
  · exact kept
  · obtain ⟨flow,_,_,_,_⟩ := cro_certified
    obtain ⟨principal⟩ := fanApp.site.actionPrincipal_exists
    obtain ⟨a,b,labels⟩ := (targetParent branch).property.1.1
    obtain ⟨_,_,_,sourceFinish,_⟩ := fanApp.site.fan_aux_canonical_access
      (fanApp.sourceIso.flowBalance flow) (.inl ()) rfl actual_source_matches principal
      (sourceParent branch) (targetParent branch) ((sourceParentWord branch).trans (targetParentWord branch).symm)
      copy false finish labels
    have wired:=congrArg fanApp.site.net.wire (Option.some.inj ((sourceParentFinish branch).symm.trans sourceFinish))
    simp only [Pairing.involutive] at wired
    cases wired
/-- The selected SOURCE child's context forces the allocated APP target case. -/
theorem targetChildCopied (branch : Bool) : ∃copy : Bool,
    (targetChild branch).val.getLast?=some (fanApp.site.reduce.wire (.inl ⟨.inr (.inl copy),appCtx⟩)) := by
  rcases fanApp.site.fan_app_access_cases (targetChild branch) with ⟨port,finish⟩|copied
  · obtain ⟨flow,_,_,_,_⟩ := cro_certified
    obtain ⟨principal⟩ := fanApp.site.actionPrincipal_exists
    obtain ⟨a,b,labels⟩ := (targetChild branch).property.1.1
    obtain ⟨_,_,sourceFinish⟩ := fanApp.site.action_kept_canonical_access (.fan .app 0 1 (by decide))
      (fanApp.sourceIso.flowBalance flow) (.inl ()) rfl actual_source_matches principal
      (sourceChild branch) (targetChild branch) ((sourceChildWord branch).trans (targetChildWord branch).symm)
      port.1 port.2 finish labels
    have wired:=congrArg fanApp.site.net.wire (Option.some.inj ((sourceChildFinish branch).symm.trans sourceFinish))
    simp only [Pairing.involutive] at wired
    have nodes:=congrArg Sigma.fst (Sum.inl.inj wired)
    cases nodes
  · exact copied
theorem actual_next_function (branch : Bool) : ∃more,PrerequisiteChain current (Syntax.innerApp branch) more ∧
    (Syntax.edges branch)[0+1]?=some (Syntax.innerApp branch++[.fn]) :=
  (Syntax.actual_chain branch).app_read_next_function_slot (Syntax.actual_read_slots branch).2.1 (Syntax.inner_lookup branch)

theorem actual_selected_fragment_domain
    (source : OccurrenceFragmentSelection current fanApp.site.net (.inl ()))
    (target : OccurrenceFragmentSelection current fanApp.site.reduce (.inl ())) (branch : Bool) :
    (source (Syntax.innerPosition branch)).fragment.access.val.getLast?=
      some (fanApp.site.net.wire (.inl ⟨.inr (.inr ()),appCtx⟩)) ∧
    (∃port : NodePort signature fanApp.Kept fanApp.kept,
      (targetParent branch).val.getLast?=some (fanApp.site.reduce.wire (.inl ⟨.inl port.1,port.2⟩))) ∧
    ∃copy : Bool,(target (Syntax.innerPosition branch)).fragment.access.val.getLast?=
      some (fanApp.site.reduce.wire (.inl ⟨.inr (.inl copy),appCtx⟩)) := by
  have sourceEq : (source (Syntax.innerPosition branch)).fragment.access=sourceChild branch :=
    actual_source_matches.accessWord_injective
      ((source (Syntax.innerPosition branch)).fragment.word.trans (sourceChildWord branch).symm)
  have targetEq : (target (Syntax.innerPosition branch)).fragment.access=targetChild branch :=
    actual_target_matches.accessWord_injective
      ((target (Syntax.innerPosition branch)).fragment.word.trans (targetChildWord branch).symm)
  refine ⟨?_,targetParentKept branch,?_⟩
  · rw [sourceEq];exact sourceChildFinish branch
  · rw [targetEq];exact targetChildCopied branch

/-- Same original INIT/history, true four schema events and actual KC domain.
The explicit concrete low-cut existential is not claimed here. Its failed
elaboration runs are archived; the abstract low cut is proved separately. -/
theorem actual_reachable_allocated_child :
    INIT Syntax.original ∧Closed Syntax.original.erase ∧History [[.fn]] Syntax.original current ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet fanApp.site.reduce)
      [.beta 0,.fanAction .lam 0 1 (by decide),.fanAction .cro 0 1 (by decide),.fanAction .app 0 1 (by decide)] ∧
    Matches fanApp.site.net (.inl ()) current.erase ∧Matches fanApp.site.reduce (.inl ()) current.erase ∧
    Nonempty (OccurrenceFragmentSelection current fanApp.site.net (.inl ())) ∧
    Nonempty (OccurrenceFragmentSelection current fanApp.site.reduce (.inl ())) ∧
    ∀(source : OccurrenceFragmentSelection current fanApp.site.net (.inl ()))
     (target : OccurrenceFragmentSelection current fanApp.site.reduce (.inl ())) (branch : Bool),
      PrerequisiteChain current (Syntax.start branch) (Syntax.edges branch) ∧
      (Syntax.edges branch).length=(if branch then 6 else 5) ∧
      (Syntax.edges branch)[0]?=some (Syntax.innerApp branch) ∧
      (Syntax.edges branch)[1]?=some (Syntax.variablePath branch) ∧
      (source (Syntax.innerPosition branch)).fragment.access.val.getLast?=
        some (fanApp.site.net.wire (.inl ⟨.inr (.inr ()),appCtx⟩)) ∧
      (∃port : NodePort signature fanApp.Kept fanApp.kept,
        (targetParent branch).val.getLast?=some (fanApp.site.reduce.wire (.inl ⟨.inl port.1,port.2⟩))) ∧
      ∃copy : Bool,(target (Syntax.innerPosition branch)).fragment.access.val.getLast?=
        some (fanApp.site.reduce.wire (.inl ⟨.inr (.inl copy),appCtx⟩)) := by
  refine ⟨Syntax.initial,Syntax.sourceClosed,Syntax.actualHistory,actual_four_step_trace,
    actual_source_matches,actual_target_matches,
    actual_source_matches.occurrence_fragment_selection Syntax.targetClosed,
    actual_target_matches.occurrence_fragment_selection Syntax.targetClosed,?_⟩
  intro source target branch
  exact ⟨Syntax.actual_chain branch,(Syntax.actual_read_slots branch).1,
    (Syntax.actual_read_slots branch).2.1,(Syntax.actual_read_slots branch).2.2,
    actual_selected_fragment_domain source target branch⟩
end Lamping.Checks.FanAppAllocatedChildReachable.Domain
#print axioms Lamping.Checks.FanAppAllocatedChildReachable.Syntax.actual_chain
#print axioms Lamping.Checks.FanAppAllocatedChildReachable.Syntax.actual_read_slots
#print axioms Lamping.Checks.FanAppAllocatedChildReachable.Domain.actual_next_function
#print axioms Lamping.Checks.FanAppAllocatedChildReachable.Domain.sourceParentFinish
#print axioms Lamping.Checks.FanAppAllocatedChildReachable.Domain.sourceChildFinish
#print axioms Lamping.Checks.FanAppAllocatedChildReachable.Domain.targetParentKept
#print axioms Lamping.Checks.FanAppAllocatedChildReachable.Domain.targetChildCopied
#print axioms Lamping.Checks.FanAppAllocatedChildReachable.Domain.actual_selected_fragment_domain
#print axioms Lamping.Checks.FanAppAllocatedChildReachable.Domain.actual_reachable_allocated_child
