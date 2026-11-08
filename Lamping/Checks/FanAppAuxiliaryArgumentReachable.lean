import Lamping.Checks.OldChainBetaFixture
import Lamping.Checks.FanSuccessfulChains
import Lamping.Lamping.FanAppArgumentLambdaTransport
import Lamping.Lamping.FanControlOccurrenceComparison
import Lamping.Lamping.ActionMatching
import Lamping.Lamping.GraphRootInputPreservation
import Lamping.Lamping.ReachableTransparency
import Lamping.Lamping.FanAppCopiedContextCuts
set_option maxHeartbeats 4000000
namespace Lamping.Checks.FanAppAuxiliaryArgumentReachable.Syntax
open AG Graph Lambda Lambda.Labelled
abbrev I : Term := identity
abbrev payload : Term := .lam (.app I (.app (.var 0) I))
abbrev bare : Term := .app (.app (.lam (.lam (.app (.app (.var 0) (.var 1)) (.var 1)))) payload) I
abbrev original : LTerm := initLabels bare
abbrev current : LTerm := match original with
  | .app b fn arg => .app b (WrappedSuccessfulChains.contractRoot fn) arg
  | t => t
def actualStep : StepAt [.fn] original current := .fn (.root _ _ _ _)
def actualHistory : History [[.fn]] original current := .cons actualStep (.nil _)
theorem initial : INIT original := init_is_INIT _
theorem sourceClosed : Closed original.erase := by
  change (((0<2 ∧1<2) ∧1<2) ∧(0<2 ∧(0<1 ∧0<2))) ∧0<1
  decide
theorem targetClosed : Closed current.erase := actualHistory.closed sourceClosed
abbrev functionLabel : Lambda.Labelled.Label := ((Lambda.Labelled.Label.atom 1).concat (Lambda.Labelled.Label.atom 2).over).concat (.atom 3)
abbrev leftLabel : Lambda.Labelled.Label := ((Lambda.Labelled.Label.atom 7).concat (Lambda.Labelled.Label.atom 2).under).concat (.atom 9)
abbrev rightLabel : Lambda.Labelled.Label := ((Lambda.Labelled.Label.atom 8).concat (Lambda.Labelled.Label.atom 2).under).concat (.atom 9)
abbrev left : Path := [.fn,.body,.fn,.arg]
abbrev right : Path := [.fn,.body,.arg]
abbrev xVar : Path := [.fn,.body,.fn,.fn]
abbrev innerApp (branch : Bool) : Path := (if branch then right else left)++[.body,.arg]
abbrev start (branch : Bool) : Path := (if branch then right else left)++[.body]
abbrev lambdaEdges (branch : Bool) : List Path :=
  if branch then [right,[.fn,.body,.fn],xVar,[.fn]] else [left,xVar,[.fn]]
abbrev sourceEdges (branch : Bool) : List Path := [start branch++[.fn]]
abbrev targetEdges (branch : Bool) : List Path := (innerApp branch++[.fn])::lambdaEdges branch
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
def source_chain (branch : Bool) : PrerequisiteChain current (start branch) (sourceEdges branch) := by
  cases branch <;> exact .redex_app rfl
def target_chain (branch : Bool) : PrerequisiteChain current (innerApp branch) (targetEdges branch) := by
  cases branch
  · exact .app rfl (by intro l b same;cases same)
      (.var (parent:=left) (rest:=[.arg,.fn]) rfl rfl rfl rfl left_lambda_chain)
  · exact .app rfl (by intro l b same;cases same)
      (.var (parent:=right) (rest:=[.arg,.fn]) rfl rfl rfl rfl right_lambda_chain)
theorem endpoint_chain_lengths (branch : Bool) : (sourceEdges branch).length=1 ∧(targetEdges branch).length=(if branch then 5 else 4) := by cases branch <;> decide
abbrev payloadInner : LTerm := .app (.atom 13) (.var (.atom 14) 0) (.lam (.atom 15) (.var (.atom 16) 0))
abbrev payloadOuter : LTerm := .app (.atom 10) (.lam (.atom 11) (.var (.atom 12) 0)) payloadInner
theorem inner_lookup (branch : Bool) : current.subterm (innerApp branch)=some payloadInner := by cases branch <;> rfl
theorem parent_lookup (branch : Bool) : current.subterm (start branch)=some payloadOuter := by cases branch <;> rfl
def innerPosition (branch : Bool) : Position current.erase := ⟨innerApp branch,by cases branch <;> rfl⟩
def parentPosition (branch : Bool) : Position current.erase := ⟨start branch,by cases branch <;> rfl⟩
def inner_occurrence (branch : Bool) : SourceSubterm [] .external current (innerApp branch)
    [if branch then rightLabel else leftLabel,functionLabel] (.appArg (.atom 10)) payloadInner := by
  cases branch
  · exact .fn (.body (.fn (.arg (.body (.arg .nil)))))
  · exact .fn (.body (.arg (.body (.arg .nil))))
end Lamping.Checks.FanAppAuxiliaryArgumentReachable.Syntax
namespace Lamping.Checks.FanAppAuxiliaryArgumentReachable.Base
open AG Graph Lambda Lambda.Labelled

abbrev argument : Term := .lam (.app identity (.app (.var 0) identity))
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
  change (((0<2 ∧1<2) ∧1<2) ∧(0<2 ∧(0<1 ∧0<2))) ∧0<1
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
  have sourceMatches : Matches net (.inl ()) Syntax.original.erase := encode_closed_matches term closed 0
  have matching:=concrete.sourceIso.matches sourceMatches
  obtain ⟨selection,initialJoint⟩:=encode_initial_joint_realization Syntax.original closed Syntax.initial 0
  obtain ⟨targetSelection⟩:=matching.occurrence_fragment_selection closed
  have joint:=(concrete.sourceIso.joint_representation sourceMatches closed selection targetSelection).mpr initialJoint
  have selected : [.fn]∈concrete.site.betaSyntaxFiber (.inl ()) term := by rw [concrete.betaSyntaxFiber_eq];exact member
  let other : RedexOcc term:=⟨[.fn,.arg,.body],_,rfl,True.intro⟩
  have absent : [.fn,.arg,.body]∉concrete.site.betaSyntaxFiber (.inl ()) term := by
    intro occurs
    have degrees:=(concrete.site.beta_fiber_iff_degree (current:=Syntax.original) closed matching targetSelection joint.1 redex selected other).mp occurs
    change some (Lambda.Labelled.Label.atom 11)=some (Lambda.Labelled.Label.atom 2) at degrees
    cases degrees
  let test:=physicalBetaTest concrete.site.net (.inl ()) term (.inr (.inl ())) (.inr (.inr ()))
  have yes : test [.fn]=true := by
    change [.fn]∈([[.fn],[.fn,.arg,.body]] : List Path).filter test at selected
    exact (List.mem_filter.mp selected).2
  have no : test [.fn,.arg,.body]=false := by
    cases decision : test [.fn,.arg,.body] with
    | false => rfl
    | true =>
      apply False.elim;apply absent
      change [.fn,.arg,.body]∈([[.fn],[.fn,.arg,.body]] : List Path).filter test
      exact List.mem_filter.mpr ⟨by simp,decision⟩
  change ([[.fn],[.fn,.arg,.body]] : List Path).filter test=[[.fn]]
  simp [yes,no]
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
def markedI : Marked := .lam (.var 0)
def markedA : Marked := .lam (.app [[.fn,.arg,.body]] markedI (.app [] (.var 0) markedI))
def endpoint : Marked := .app [] (.lam (.app [] (.app [] (.var 0) markedA) markedA)) markedI

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
    relative (by simp [endpoint,markedA,markedI,Marked.Normal]) Syntax.actualHistory
#print axioms beta_matches

def originalArgBra : (encode 1 argument).N := .inr (.inl (.inr (.inl ⟨0,Or.inl rfl⟩)))
def oldArgBra : (encode 0 term).N := .inr (.inl (.inr (.inr originalArgBra)))
def wrapArgWire (w : (encode 1 argument).W) : (encode 0 term).W := .inl (.inr (.inl (.inl (.inr (.inr w)))))
def argBindingWire : (encode 0 term).W := wrapArgWire (.inr (.inr ⟨0,Or.inr (Or.inl rfl)⟩))
theorem actual_first_binding_control : net.label oldArgBra=label .bra 1 := rfl
theorem arg_bind_start : net.wire (.inl ⟨oldArgLam,lamBind⟩)=.inr (.inr (argBindingWire,false)) := rfl
theorem arg_bind_finish : net.wire (.inr (.inr (argBindingWire,true)))=.inl ⟨oldArgBra,.inl ()⟩ := rfl
def braKept : concrete.Kept := ⟨oldArgBra,by constructor <;> intro h <;> cases h⟩
def argBindingOutside : concrete.Outside := ⟨argBindingWire,by
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
theorem beta_arg_bind_finish : concrete.site.reduce.wire (.inr (.inr (.inl (.inl argBindingOutside),true)))=
    .inl ⟨.inl braKept,.inl ()⟩ :=
  beta_lift_wire (.inr (.inr (argBindingOutside,true))) (.inl ⟨braKept,.inl ()⟩) arg_bind_finish

def braKept2 : actualFanPresentation.Kept := ⟨.inl braKept,by
  constructor <;> intro h <;> have same:=congrArg Subtype.val (Sum.inl.inj h) <;> cases same⟩
def argBindingOutside2 : actualFanPresentation.Outside := ⟨.inl (.inl argBindingOutside),by
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
noncomputable def passiveBra : actualFanPresentation.Kept⊕(Bool⊕Bool) := .inl braKept2
noncomputable def lowPrincipal : Endpoint actualFanPresentation.site.reduce := .inl ⟨lowBinding,.inl ()⟩
noncomputable def lowGlue : Endpoint actualFanPresentation.site.reduce := .inr (.inr (.inr (.inr false),false))
noncomputable def lowStep1 : Endpoint actualFanPresentation.site.reduce := .inr (.inr (.inl (.inl argBindingOutside2),true))
theorem low_start : actualFanPresentation.site.reduce.wire lowPrincipal=.inr (.inr (.inr (.inr false),true)) := rfl
theorem low_glue : actualFanPresentation.site.reduce.wire lowGlue=.inr (.inr (.inl (.inl argBindingOutside2),false)) :=
  action2_lift_wire (.inr (.inl (.inr (.inr false)))) (.inr (.inr (argBindingOutside2,false))) beta_arg_bind_start
theorem low_finish : actualFanPresentation.site.reduce.wire lowStep1=.inl ⟨passiveBra,.inl ()⟩ :=
  action2_lift_wire (.inr (.inr (argBindingOutside2,true))) (.inl ⟨braKept2,.inl ()⟩) beta_arg_bind_finish
noncomputable def actualFanBraCorridor : TransparentCorridor actualFanPresentation.site.reduce where
  first:=⟨lowBinding,.inl ()⟩
  last:=⟨passiveBra,.inl ()⟩
  edges:=[lowPrincipal,lowGlue,lowStep1]
  start:=rfl
  finish:=by
    have h:=congrArg actualFanPresentation.site.reduce.wire low_finish
    simp only [Pairing.involutive] at h
    exact congrArg some h
  transparent:=by
    intro e f member
    simp only [List.tail_cons,List.zip_cons_cons,List.zip_nil_right,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h|h
    · cases h;exact ⟨.inr (.inr false),true,low_start,rfl⟩
    · cases h;exact ⟨.inl (.inl argBindingOutside2),false,low_glue,rfl⟩
noncomputable def fanBra:=PhysicalCorridorPresentation.of_corridor actualFanPresentation.site.reduce
  (.fanAction .bra 0 1 (by decide)) actualFanBraCorridor lowBinding passiveBra
  (by intro h;cases h) rfl rfl (.inl ()) (.inl ()) HEq.rfl HEq.rfl rfl rfl
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
theorem bra_certified : Certified (ActualNet.ofNet fanBra.site.reduce) :=
  action_certified fanBra.graph_step (.fan .bra 0 1 (by decide)) lambda_certified

theorem actual_final_matches : Matches fanBra.site.reduce (.inl ()) current.erase := by
  obtain ⟨_,_,_,_,matching⟩ := bra_certified
  exact matching

theorem actual_source_matches : Matches fanBra.site.net (.inl ()) current.erase := by
  obtain ⟨_,_,_,_,matching⟩ := lambda_certified
  exact fanBra.sourceIso.matches matching

theorem actual_three_step_trace : GraphTrace (ActualNet.initial term)
    (ActualNet.ofNet fanBra.site.reduce)
    [.beta 0,.fanAction .lam 0 1 (by decide),.fanAction .bra 0 1 (by decide)] :=
  .cons concrete.graph_step (.cons actualFanPresentation.graph_step (.cons fanBra.graph_step (.refl _)))
#print axioms actual_three_step_trace
#print axioms actual_source_matches
#print axioms actual_final_matches

end Lamping.Checks.FanAppAuxiliaryArgumentReachable.Base

namespace Lamping.Checks.FanAppAuxiliaryArgumentReachable
open AG Graph Lambda Lambda.Labelled Base

def originalY : (encode 1 argument).N := .inr (.inr (.inr (.inr (.inl ()))))
def originalInnerApp : (encode 1 argument).N := .inr (.inr (.inr (.inl (.inl ()))))
def oldY : (encode 0 term).N := .inr (.inl (.inr (.inr originalY)))
def oldInnerApp : (encode 0 term).N := .inr (.inl (.inr (.inr originalInnerApp)))
def bodyWire (w : (encode 1 (.app identity (.app (.var 0) identity))).W) : (encode 1 argument).W := .inl (.inr w)
def innerWire (w : (encode 2 (.app (.var 0) identity)).W) : (encode 1 argument).W := bodyWire (.inl (.inr (.inr w)))
def outerArgFVWire : (encode 0 term).W := wrapArgWire (bodyWire (.inr (.inr (.inr ⟨0,Or.inl rfl⟩))))
def innerFnFVWire : (encode 0 term).W := wrapArgWire (innerWire (.inr (.inl (.inr ⟨0,rfl⟩))))
def innerFnWire : (encode 0 term).W := wrapArgWire (innerWire (.inr (.inl (.inl ()))))

theorem original_y_label : net.label oldY=label .cro 2 := rfl
theorem original_inner_app_label : net.label oldInnerApp=label .app 2 := rfl
theorem original_bra_aux_wire : net.wire (.inl ⟨oldArgBra,.inr ()⟩)=.inr (.inr (outerArgFVWire,false)) := rfl
theorem original_arg_transit : net.wire (.inr (.inr (outerArgFVWire,true)))=.inr (.inr (innerFnFVWire,false)) := rfl
theorem original_y_principal : net.wire (.inr (.inr (innerFnFVWire,true)))=.inl ⟨oldY,.inl ()⟩ := rfl
theorem original_y_aux : net.wire (.inl ⟨oldY,.inr ()⟩)=.inr (.inr (innerFnWire,true)) := rfl
theorem original_inner_fn : net.wire (.inr (.inr (innerFnWire,false)))=.inl ⟨oldInnerApp,.inl ()⟩ := by
  have h : net.wire (.inl ⟨oldInnerApp,.inl ()⟩)=.inr (.inr (innerFnWire,false)) := rfl
  exact (congrArg net.wire h).symm.trans (net.wire.involutive _)
#print axioms original_y_label
#print axioms original_bra_aux_wire
#print axioms original_arg_transit
#print axioms original_y_principal
#print axioms original_y_aux
#print axioms original_inner_fn
def yKept : concrete.Kept := ⟨oldY,by constructor <;> intro h <;> cases h⟩
def yKept2 : actualFanPresentation.Kept := ⟨.inl yKept,by
  constructor <;> intro h <;> have hs:=congrArg Subtype.val (Sum.inl.inj h) <;> cases hs⟩
def yKept3 : fanBra.Kept := ⟨.inl yKept2,by
  constructor
  · intro h;cases h
  · intro h;have hs:=congrArg Subtype.val (Sum.inl.inj h)
    have ht:=congrArg Subtype.val (Sum.inl.inj hs);cases ht⟩
def innerAppKept : concrete.Kept := ⟨oldInnerApp,by constructor <;> intro h <;> cases h⟩
def innerAppKept2 : actualFanPresentation.Kept := ⟨.inl innerAppKept,by
  constructor <;> intro h <;> have hs:=congrArg Subtype.val (Sum.inl.inj h) <;> cases hs⟩
def innerAppKept3 : fanBra.Kept := ⟨.inl innerAppKept2,by
  constructor
  · intro h;cases h
  · intro h;have hs:=congrArg Subtype.val (Sum.inl.inj h)
    have ht:=congrArg Subtype.val (Sum.inl.inj hs);cases ht⟩
def outerArgFVOutside : concrete.Outside := ⟨outerArgFVWire,by
  rintro ⟨d,h⟩;simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h <;> cases h⟩
def outerArgFVOutside2 : actualFanPresentation.Outside := ⟨.inl (.inl outerArgFVOutside),by
  rintro ⟨d,h⟩;simp only [actualFanLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h|h <;> cases h⟩
def outerArgFVOutside3 : fanBra.Outside := ⟨.inl (.inl outerArgFVOutside2),by
  rintro ⟨d,h⟩;simp only [actualFanBraCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h <;> cases h⟩
def innerFnFVOutside : concrete.Outside := ⟨innerFnFVWire,by
  rintro ⟨d,h⟩;simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h <;> cases h⟩
def innerFnFVOutside2 : actualFanPresentation.Outside := ⟨.inl (.inl innerFnFVOutside),by
  rintro ⟨d,h⟩;simp only [actualFanLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h|h <;> cases h⟩
def innerFnFVOutside3 : fanBra.Outside := ⟨.inl (.inl innerFnFVOutside2),by
  rintro ⟨d,h⟩;simp only [actualFanBraCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h <;> cases h⟩
def innerFnOutside : concrete.Outside := ⟨innerFnWire,by
  rintro ⟨d,h⟩;simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h <;> cases h⟩
def innerFnOutside2 : actualFanPresentation.Outside := ⟨.inl (.inl innerFnOutside),by
  rintro ⟨d,h⟩;simp only [actualFanLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h|h <;> cases h⟩
def innerFnOutside3 : fanBra.Outside := ⟨.inl (.inl innerFnOutside2),by
  rintro ⟨d,h⟩;simp only [actualFanBraCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h <;> cases h⟩
theorem beta_bra_aux : concrete.site.reduce.wire (.inl ⟨.inl braKept,.inr ()⟩)=(.inr (.inr (.inl (.inl outerArgFVOutside),false))) :=
  beta_lift_wire (.inl ⟨braKept,.inr ()⟩) (.inr (.inr (outerArgFVOutside,false))) original_bra_aux_wire
theorem lambda_bra_aux : actualFanPresentation.site.reduce.wire (.inl ⟨.inl braKept2,.inr ()⟩)=(.inr (.inr (.inl (.inl outerArgFVOutside2),false))) :=
  action2_lift_wire (.inl ⟨braKept2,.inr ()⟩) (.inr (.inr (outerArgFVOutside2,false))) beta_bra_aux
theorem beta_arg_transit : concrete.site.reduce.wire (.inr (.inr (.inl (.inl outerArgFVOutside),true)))=(.inr (.inr (.inl (.inl innerFnFVOutside),false))) :=
  beta_lift_wire (.inr (.inr (outerArgFVOutside,true))) (.inr (.inr (innerFnFVOutside,false))) original_arg_transit
theorem lambda_arg_transit : actualFanPresentation.site.reduce.wire (.inr (.inr (.inl (.inl outerArgFVOutside2),true)))=(.inr (.inr (.inl (.inl innerFnFVOutside2),false))) :=
  action2_lift_wire (.inr (.inr (outerArgFVOutside2,true))) (.inr (.inr (innerFnFVOutside2,false))) beta_arg_transit
theorem beta_y_principal : concrete.site.reduce.wire (.inr (.inr (.inl (.inl innerFnFVOutside),true)))=(.inl ⟨.inl yKept,.inl ()⟩) :=
  beta_lift_wire (.inr (.inr (innerFnFVOutside,true))) (.inl ⟨yKept,.inl ()⟩) original_y_principal
theorem lambda_y_principal : actualFanPresentation.site.reduce.wire (.inr (.inr (.inl (.inl innerFnFVOutside2),true)))=(.inl ⟨.inl yKept2,.inl ()⟩) :=
  action2_lift_wire (.inr (.inr (innerFnFVOutside2,true))) (.inl ⟨yKept2,.inl ()⟩) beta_y_principal
theorem beta_y_aux : concrete.site.reduce.wire (.inl ⟨.inl yKept,.inr ()⟩)=(.inr (.inr (.inl (.inl innerFnOutside),true))) :=
  beta_lift_wire (.inl ⟨yKept,.inr ()⟩) (.inr (.inr (innerFnOutside,true))) original_y_aux
theorem lambda_y_aux : actualFanPresentation.site.reduce.wire (.inl ⟨.inl yKept2,.inr ()⟩)=(.inr (.inr (.inl (.inl innerFnOutside2),true))) :=
  action2_lift_wire (.inl ⟨yKept2,.inr ()⟩) (.inr (.inr (innerFnOutside2,true))) beta_y_aux
theorem beta_inner_fn : concrete.site.reduce.wire (.inr (.inr (.inl (.inl innerFnOutside),false)))=(.inl ⟨.inl innerAppKept,.inl ()⟩) :=
  beta_lift_wire (.inr (.inr (innerFnOutside,false))) (.inl ⟨innerAppKept,.inl ()⟩) original_inner_fn
theorem lambda_inner_fn : actualFanPresentation.site.reduce.wire (.inr (.inr (.inl (.inl innerFnOutside2),false)))=(.inl ⟨.inl innerAppKept2,.inl ()⟩) :=
  action2_lift_wire (.inr (.inr (innerFnOutside2,false))) (.inl ⟨innerAppKept2,.inl ()⟩) beta_inner_fn
noncomputable abbrev cut3 : Net signature fanBra.Kept (Boundary term⊕(Bool⊕Unit)) fanBra.Outside := cutFragment fanBra.site.net
  (pathPartition (Schema.fanAction .bra 0 1 (by decide)) fanBra.Inside) fanBra.site.closed
theorem outside3_injective : Function.Injective fanBra.site.outsideEnd := by
  intro e f same
  let split := fragmentEnd (B:=Boundary term) (W:=fanBra.Outside) fanBra.site.net.label
    (pathPartition (Schema.fanAction .bra 0 1 (by decide)) fanBra.Inside)
  change split.invFun (.inl e)=split.invFun (.inl f) at same
  have mapped:=congrArg split same
  simpa only [split.right_inv,Sum.inl.injEq] using mapped

theorem action3_lift_wire (e f : Endpoint cut3)
    (h : actualFanPresentation.site.reduce.wire (fanBra.sourceIso.symm.ends (fanBra.site.outsideEnd e))=
      fanBra.sourceIso.symm.ends (fanBra.site.outsideEnd f)) :
    fanBra.site.reduce.wire (AG.plugLeft cut3 (Schema.fanAction .bra 0 1 (by decide)).right.net e)=
      AG.plugLeft cut3 (Schema.fanAction .bra 0 1 (by decide)).right.net f := by
  have old : fanBra.site.net.wire (fanBra.site.outsideEnd e)=fanBra.site.outsideEnd f := by
    apply fanBra.sourceIso.symm.ends.injective
    rw [fanBra.sourceIso.symm.wiring];exact h
  have actual : cut3.wire e=f := outside3_injective ((fanBra.site.outsideEnd_wire e).symm.trans old)
  exact (plugLeft_wire cut3 (Schema.fanAction .bra 0 1 (by decide)).right.net e).trans
    (congrArg (AG.plugLeft cut3 (Schema.fanAction .bra 0 1 (by decide)).right.net) actual)

noncomputable def fanAfterBra : fanBra.Kept⊕(Bool⊕Unit) := .inr (.inr ())
noncomputable def yAfterBra : fanBra.Kept⊕(Bool⊕Unit) := .inl yKept3
noncomputable def croPrincipal : Endpoint fanBra.site.reduce := .inl ⟨fanAfterBra,.inl ()⟩
noncomputable def croGlue : Endpoint fanBra.site.reduce := .inr (.inr (.inr (.inr ()),false))
noncomputable def croStep1 : Endpoint fanBra.site.reduce := .inr (.inr (.inl (.inl outerArgFVOutside3),true))
noncomputable def croStep2 : Endpoint fanBra.site.reduce := .inr (.inr (.inl (.inl innerFnFVOutside3),true))
theorem cro_start : fanBra.site.reduce.wire croPrincipal=.inr (.inr (.inr (.inr ()),true)) := rfl
theorem cro_glue : fanBra.site.reduce.wire croGlue=.inr (.inr (.inl (.inl outerArgFVOutside3),false)) :=
  action3_lift_wire (.inr (.inl (.inr (.inr ())))) (.inr (.inr (outerArgFVOutside3,false))) lambda_bra_aux
theorem cro_transit : fanBra.site.reduce.wire croStep1=.inr (.inr (.inl (.inl innerFnFVOutside3),false)) :=
  action3_lift_wire (.inr (.inr (outerArgFVOutside3,true))) (.inr (.inr (innerFnFVOutside3,false))) lambda_arg_transit
theorem cro_finish : fanBra.site.reduce.wire croStep2=.inl ⟨yAfterBra,.inl ()⟩ :=
  action3_lift_wire (.inr (.inr (innerFnFVOutside3,true))) (.inl ⟨yKept3,.inl ()⟩) lambda_y_principal
noncomputable def croCorridor : TransparentCorridor fanBra.site.reduce where
  first:=⟨fanAfterBra,.inl ()⟩
  last:=⟨yAfterBra,.inl ()⟩
  edges:=[croPrincipal,croGlue,croStep1,croStep2]
  start:=rfl
  finish:=by
    have h:=congrArg fanBra.site.reduce.wire cro_finish
    simp only [Pairing.involutive] at h
    exact congrArg some h
  transparent:=by
    intro e f member
    simp only [List.tail_cons,List.zip_cons_cons,List.zip_nil_right,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h|h|h
    · cases h;exact ⟨.inr (.inr ()),true,cro_start,rfl⟩
    · cases h;exact ⟨.inl (.inl outerArgFVOutside3),false,cro_glue,rfl⟩
    · cases h;exact ⟨.inl (.inl innerFnFVOutside3),false,cro_transit,rfl⟩
noncomputable def fanCro := PhysicalCorridorPresentation.of_corridor fanBra.site.reduce
  (.fanAction .cro 0 2 (by decide)) croCorridor fanAfterBra yAfterBra
  (by intro h;cases h) rfl rfl (.inl ()) (.inl ()) HEq.rfl HEq.rfl rfl rfl
#print axioms fanCro

theorem bra_y_aux : fanBra.site.reduce.wire (.inl ⟨.inl yKept3,.inr ()⟩)=
    .inr (.inr (.inl (.inl innerFnOutside3),true)) :=
  action3_lift_wire (.inl ⟨yKept3,.inr ()⟩) (.inr (.inr (innerFnOutside3,true))) lambda_y_aux
theorem bra_inner_fn : fanBra.site.reduce.wire (.inr (.inr (.inl (.inl innerFnOutside3),false)))=
    .inl ⟨.inl innerAppKept3,.inl ()⟩ :=
  action3_lift_wire (.inr (.inr (innerFnOutside3,false))) (.inl ⟨innerAppKept3,.inl ()⟩) lambda_inner_fn

def innerAppKept4 : fanCro.Kept := ⟨.inl innerAppKept3,by
  constructor
  · intro h;cases h
  · intro h;have hs:=congrArg Subtype.val (Sum.inl.inj h)
    have ht:=congrArg Subtype.val (Sum.inl.inj hs)
    have hu:=congrArg Subtype.val (Sum.inl.inj ht);cases hu⟩
def innerFnOutside4 : fanCro.Outside := ⟨.inl (.inl innerFnOutside3),by
  rintro ⟨d,h⟩;simp only [croCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h <;> cases h⟩
noncomputable abbrev cut4 : Net signature fanCro.Kept (Boundary term⊕(Bool⊕Unit)) fanCro.Outside := cutFragment fanCro.site.net
  (pathPartition (Schema.fanAction .cro 0 2 (by decide)) fanCro.Inside) fanCro.site.closed
theorem outside4_injective : Function.Injective fanCro.site.outsideEnd := by
  intro e f same
  let split := fragmentEnd (B:=Boundary term) (W:=fanCro.Outside) fanCro.site.net.label
    (pathPartition (Schema.fanAction .cro 0 2 (by decide)) fanCro.Inside)
  change split.invFun (.inl e)=split.invFun (.inl f) at same
  have mapped:=congrArg split same
  simpa only [split.right_inv,Sum.inl.injEq] using mapped

theorem action4_lift_wire (e f : Endpoint cut4)
    (h : fanBra.site.reduce.wire (fanCro.sourceIso.symm.ends (fanCro.site.outsideEnd e))=
      fanCro.sourceIso.symm.ends (fanCro.site.outsideEnd f)) :
    fanCro.site.reduce.wire (AG.plugLeft cut4 (Schema.fanAction .cro 0 2 (by decide)).right.net e)=
      AG.plugLeft cut4 (Schema.fanAction .cro 0 2 (by decide)).right.net f := by
  have old : fanCro.site.net.wire (fanCro.site.outsideEnd e)=fanCro.site.outsideEnd f := by
    apply fanCro.sourceIso.symm.ends.injective
    rw [fanCro.sourceIso.symm.wiring];exact h
  have actual : cut4.wire e=f := outside4_injective ((fanCro.site.outsideEnd_wire e).symm.trans old)
  exact (plugLeft_wire cut4 (Schema.fanAction .cro 0 2 (by decide)).right.net e).trans
    (congrArg (AG.plugLeft cut4 (Schema.fanAction .cro 0 2 (by decide)).right.net) actual)

noncomputable def fanAfterCro : fanCro.Kept⊕(Bool⊕Unit) := .inr (.inr ())
noncomputable def innerAppAfterCro : fanCro.Kept⊕(Bool⊕Unit) := .inl innerAppKept4
noncomputable def appPrincipal : Endpoint fanCro.site.reduce := .inl ⟨fanAfterCro,.inl ()⟩
noncomputable def appGlue : Endpoint fanCro.site.reduce := .inr (.inr (.inr (.inr ()),false))
noncomputable def appStep : Endpoint fanCro.site.reduce := .inr (.inr (.inl (.inl innerFnOutside4),false))
theorem app_start : fanCro.site.reduce.wire appPrincipal=.inr (.inr (.inr (.inr ()),true)) := rfl
theorem app_glue : fanCro.site.reduce.wire appGlue=.inr (.inr (.inl (.inl innerFnOutside4),true)) :=
  action4_lift_wire (.inr (.inl (.inr (.inr ())))) (.inr (.inr (innerFnOutside4,true))) bra_y_aux
theorem app_finish : fanCro.site.reduce.wire appStep=.inl ⟨innerAppAfterCro,.inl ()⟩ :=
  action4_lift_wire (.inr (.inr (innerFnOutside4,false))) (.inl ⟨innerAppKept4,.inl ()⟩) bra_inner_fn
noncomputable def appCorridor : TransparentCorridor fanCro.site.reduce where
  first:=⟨fanAfterCro,.inl ()⟩
  last:=⟨innerAppAfterCro,.inl ()⟩
  edges:=[appPrincipal,appGlue,appStep]
  start:=rfl
  finish:=by
    have h:=congrArg fanCro.site.reduce.wire app_finish
    simp only [Pairing.involutive] at h
    exact congrArg some h
  transparent:=by
    intro e f member
    simp only [List.tail_cons,List.zip_cons_cons,List.zip_nil_right,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h|h
    · cases h;exact ⟨.inr (.inr ()),true,app_start,rfl⟩
    · cases h;exact ⟨.inl (.inl innerFnOutside4),true,app_glue,rfl⟩
noncomputable def fanApp := PhysicalCorridorPresentation.of_corridor fanCro.site.reduce
  (.fanAction .app 0 2 (by decide)) appCorridor fanAfterCro innerAppAfterCro
  (by intro h;cases h) rfl rfl (.inl ()) (.inl ()) HEq.rfl HEq.rfl rfl rfl

theorem cro_certified : Certified (ActualNet.ofNet fanCro.site.reduce) :=
  action_certified fanCro.graph_step (.fan .cro 0 2 (by decide)) bra_certified
theorem app_certified : Certified (ActualNet.ofNet fanApp.site.reduce) :=
  action_certified fanApp.graph_step (.fan .app 0 2 (by decide)) cro_certified

theorem actual_source_matches : Matches fanApp.site.net (.inl ()) current.erase := by
  obtain ⟨_,_,_,_,matching⟩ := cro_certified
  exact fanApp.sourceIso.matches matching
theorem actual_target_matches : Matches fanApp.site.reduce (.inl ()) current.erase := by
  obtain ⟨_,_,_,_,matching⟩ := app_certified
  exact matching
theorem actual_five_step_trace : GraphTrace (ActualNet.initial term) (ActualNet.ofNet fanApp.site.reduce)
    [.beta 0,.fanAction .lam 0 1 (by decide),.fanAction .bra 0 1 (by decide),
      .fanAction .cro 0 2 (by decide),.fanAction .app 0 2 (by decide)] :=
  .cons concrete.graph_step (.cons actualFanPresentation.graph_step (.cons fanBra.graph_step
    (.cons fanCro.graph_step (.cons fanApp.graph_step (.refl _)))))
#print axioms fanApp
#print axioms actual_five_step_trace
#print axioms actual_source_matches
#print axioms actual_target_matches
end Lamping.Checks.FanAppAuxiliaryArgumentReachable

namespace Lamping.Checks.FanAppAuxiliaryArgumentReachable.Parents
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

def copiedLambda (b : Bool) : fanBra.Kept := ⟨.inr (.inl b),by constructor <;> intro h <;> cases h⟩
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

noncomputable def sourceParent (b : Bool) : RootAccess fanBra.site.net (.inl ()) :=
  fanBra.sourceIso.rootAccessBij (.inl ()) (chosenParent b)

theorem sourceWord (b : Bool) : accessWord fanBra.site.net (sourceParent b).val=
    if b then Syntax.right else Syntax.left :=
  (fanBra.sourceIso.accessWord (chosenParent b).val).trans (chosenWord b)

theorem sourceFinish (b : Bool) : (sourceParent b).val.getLast?=
    some (fanBra.site.net.wire (.inl ⟨.inl (copiedLambda b),.inl ()⟩)) := by
  change ((chosenParent b).val.map fanBra.sourceIso.ends).getLast?=_
  rw [List.getLast?_map,chosenFinish]
  simp only [Option.map_some]
  apply congrArg some
  rw [fanBra.sourceIso.wiring]
  apply congrArg fanBra.site.net.wire
  apply fanBra.sourceIso.symm.ends.injective
  change fanBra.sourceIso.ends.invFun (fanBra.sourceIso.ends.toFun (.inl ⟨.inr (.inl b),.inl ()⟩)) =
    fanBra.sourceIso.ends.invFun (.inl ⟨.inl (copiedLambda b),.inl ()⟩)
  rw [fanBra.sourceIso.ends.left_inv]
  rfl

def parentPosition (b : Bool) : Position current.erase :=
  ⟨if b then Syntax.right else Syntax.left,by cases b <;> rfl⟩
noncomputable def targetParent (b : Bool) : RootAccess fanBra.site.reduce (.inl ()) :=
  Classical.choose (Matches.observation fanBra.site.reduce Base.actual_final_matches (parentPosition b))

theorem targetWord (b : Bool) : accessWord fanBra.site.reduce (targetParent b).val=
    if b then Syntax.right else Syntax.left :=
  (Classical.choose_spec (Matches.observation fanBra.site.reduce Base.actual_final_matches (parentPosition b))).1

theorem targetFinish (b : Bool) : (targetParent b).val.getLast?=
    some (fanBra.site.reduce.wire (.inl ⟨.inl (copiedLambda b),.inl ()⟩)) := by
  obtain ⟨port,finish⟩ := fanBra.site.fan_control_access_kept (Or.inr (Or.inr rfl)) (targetParent b)
  obtain ⟨a,c,labels⟩ := (targetParent b).property.1.1
  obtain ⟨principal⟩ := fanBra.site.actionPrincipal_exists
  obtain ⟨flow,_,_,_,_⟩ := lambda_certified
  have normalized := fanBra.site.action_kept_canonical_access (.fan .bra 0 1 (by decide))
    (fanBra.sourceIso.flowBalance flow) (.inl ()) rfl Base.actual_source_matches principal
    (sourceParent b) (targetParent b) ((sourceWord b).trans (targetWord b).symm)
    port.1 port.2 finish labels
  have wireEq := Option.some.inj ((sourceFinish b).symm.trans normalized.2.2)
  have endEq := congrArg fanBra.site.net.wire wireEq
  simp only [Pairing.involutive] at endEq
  rcases port with ⟨node,p⟩
  have nodeEq : copiedLambda b=node := Sum.inl.inj (congrArg Sigma.fst (Sum.inl.inj endEq))
  subst node
  have portEq : (Sum.inl () : Port (fanBra.kept (copiedLambda b)).sort)=p :=
    eq_of_heq (Sigma.mk.inj (Sum.inl.inj endEq)).2
  subst p
  exact finish
#print axioms sourceFinish
#print axioms targetFinish


end Lamping.Checks.FanAppAuxiliaryArgumentReachable.Parents

namespace Lamping.Checks.FanAppAuxiliaryArgumentReachable.ThirdDomain
open AG Graph Lambda Lambda.Labelled Base
-- The parent is the payload's OUTER APP. The selected fourth-site APP is its FN child.
def originalOuter : (encode 1 argument).N := .inr (.inl (.inl ()))
def oldOuter : (encode 0 term).N := .inr (.inl (.inr (.inr originalOuter)))
def outerKept : concrete.Kept := ⟨oldOuter,by constructor <;> intro h <;> cases h⟩
def outerKept2 : actualFanPresentation.Kept := ⟨.inl outerKept,by
  constructor <;> intro h <;> have same:=congrArg Subtype.val (Sum.inl.inj h) <;> cases same⟩
def outerKept3 : fanBra.Kept := ⟨.inl outerKept2,by
  constructor
  · intro h;cases h
  · intro h;have same:=congrArg Subtype.val (Sum.inl.inj h)
    have prior:=congrArg Subtype.val (Sum.inl.inj same);cases prior⟩
noncomputable def thirdOuterNode : fanBra.Kept⊕(Bool⊕Unit) := .inl outerKept3
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

def bodyControl3 : fanBra.Kept := ⟨.inr (.inr true),by constructor <;> intro h <;> cases h⟩
def bodyFront3 : fanBra.Outside := ⟨.inr (.inr true),by
  rintro ⟨d,h⟩;simp only [actualFanBraCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h <;> cases h⟩
def bodyRoot3 : fanBra.Outside := ⟨.inl (.inl bodyRootOutside2),by
  rintro ⟨d,h⟩;simp only [actualFanBraCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h <;> cases h⟩
theorem third_body_start (branch : Bool) : fanBra.site.reduce.wire
    (.inl ⟨.inl (Parents.copiedLambda branch),lamBody⟩)=
    .inl ⟨.inl bodyControl3,.inr branch⟩ :=
  action3_lift_wire (.inl ⟨Parents.copiedLambda branch,lamBody⟩) (.inl ⟨bodyControl3,.inr branch⟩) rfl
theorem third_body_control : fanBra.site.reduce.wire (.inl ⟨.inl bodyControl3,.inl ()⟩)=
    .inr (.inr (.inl (.inl bodyFront3),true)) :=
  action3_lift_wire (.inl ⟨bodyControl3,.inl ()⟩) (.inr (.inr (bodyFront3,true))) rfl
theorem third_body_exit : fanBra.site.reduce.wire (.inr (.inr (.inl (.inl bodyFront3),false)))=
    .inr (.inr (.inl (.inl bodyRoot3),false)) :=
  action3_lift_wire (.inr (.inr (bodyFront3,false))) (.inr (.inr (bodyRoot3,false))) lambda_body_exit
theorem third_body_finish : fanBra.site.reduce.wire (.inr (.inr (.inl (.inl bodyRoot3),true)))=
    .inl ⟨thirdOuterNode,appCtx⟩ :=
  action3_lift_wire (.inr (.inr (bodyRoot3,true))) (.inl ⟨outerKept3,appCtx⟩) lambda_body_finish

noncomputable def bodyTail (branch : Bool) : List (Endpoint fanBra.site.reduce) := [
 .inl ⟨.inl (Parents.copiedLambda branch),lamBody⟩,
 .inl ⟨.inl bodyControl3,.inl ()⟩,
 .inr (.inr (.inl (.inl bodyFront3),false)),
 .inr (.inr (.inl (.inl bodyRoot3),true))]
theorem bodyTailLabels (branch : Bool) (a : Context) : Labelling fanBra.site.reduce (bodyTail branch) a (InitialOffsets.fanAt 0 branch a) := by
  apply Labelling.cons (by rw [third_body_start];exact LabelledTurn.node (g:=fanBra.site.reduce) (.inl bodyControl3) _ _ (.direct (InitialOffsets.Event.apply_rel (.fan 0 branch) a)))
  apply Labelling.cons (by rw [third_body_control];exact LabelledTurn.transparent (g:=fanBra.site.reduce) (.inl (.inl bodyFront3)) true _)
  exact .cons (by rw [third_body_exit];exact LabelledTurn.transparent (g:=fanBra.site.reduce) (.inl (.inl bodyRoot3)) false _) (.single _ _)
theorem bodyTailWord (branch : Bool) : (bodyTail branch).flatMap (arrivalWord fanBra.site.reduce)=[.body] := rfl
theorem bodyTailFinish (branch : Bool) : (bodyTail branch).getLast?=some (fanBra.site.reduce.wire (.inl ⟨thirdOuterNode,appCtx⟩)) := by
  have h:=congrArg fanBra.site.reduce.wire third_body_finish
  simp only [Pairing.involutive] at h
  exact congrArg some h
noncomputable def bodyAppEdges (branch : Bool) := (Parents.targetParent branch).val++bodyTail branch

theorem bodyAppWord (branch : Bool) : accessWord fanBra.site.reduce (bodyAppEdges branch)=Syntax.start branch := by
  obtain ⟨a,b,labels⟩ := (Parents.targetParent branch).property.1.1
  rw [bodyAppEdges,accessWord_append _ _ _ labels.nonempty,
    Parents.targetWord,bodyTailWord]

theorem bodyAppAccessProof (branch : Bool) : IsRootAccess fanBra.site.reduce (.inl ()) (bodyAppEdges branch) := by
  obtain ⟨a,b,labels⟩ := (Parents.targetParent branch).property.1.1
  have whole := labels.append_seam (bodyTailLabels branch b) (by
    intro e f last first
    have he:=Option.some.inj (last.symm.trans (Parents.targetFinish branch))
    have hf:=Option.some.inj first
    subst e;subst f;rw [Pairing.involutive]
    exact LabelledTurn.node (g:=fanBra.site.reduce) (.inl (Parents.copiedLambda branch)) (.inl ()) lamBody (.direct (.lamBody b)))
  obtain ⟨flow,_,_,_,_⟩ := bra_certified
  have head : (bodyAppEdges branch).head?=some (.inr (.inl (.inl ()))) := by
    rw [bodyAppEdges,List.head?_append,(Parents.targetParent branch).property.2.1,Option.some_or]
  have last : (bodyAppEdges branch).getLast?=some (fanBra.site.reduce.wire (.inl ⟨thirdOuterNode,appCtx⟩)) := by
    rw [bodyAppEdges,List.getLast?_append,bodyTailFinish,Option.some_or]
  exact ⟨⟨⟨a,_,whole⟩,whole.root_forward_of_flow flow (.inl ()) head rfl⟩,head,⟨.app,by
    unfold accessKind;rw [last];simp only [Option.bind_some,Pairing.involutive];rfl⟩⟩
noncomputable def bodyAppParent (branch : Bool) : RootAccess fanBra.site.reduce (.inl ()) := ⟨bodyAppEdges branch,bodyAppAccessProof branch⟩
def outerArgumentWire : (encode 0 term).W := wrapArgWire (.inl (.inr (.inr (.inr (.inl ())))))
def outerArgOutside : concrete.Outside := ⟨outerArgumentWire,by
  rintro ⟨d,h⟩;simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h <;> cases h⟩
def outerArgOutside2 : actualFanPresentation.Outside := ⟨.inl (.inl outerArgOutside),by
  rintro ⟨d,h⟩;simp only [actualFanLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h|h <;> cases h⟩
def outerArgOutside3 : fanBra.Outside := ⟨.inl (.inl outerArgOutside2),by
  rintro ⟨d,h⟩;simp only [actualFanBraCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h <;> cases h⟩
theorem beta_outer_arg : concrete.site.reduce.wire (.inl ⟨.inl outerKept,appArg⟩)=
    .inr (.inr (.inl (.inl outerArgOutside),false)) :=
  beta_lift_wire (.inl ⟨outerKept,appArg⟩) (.inr (.inr (outerArgOutside,false))) rfl
theorem beta_inner_ctx : concrete.site.reduce.wire (.inr (.inr (.inl (.inl outerArgOutside),true)))=
    .inl ⟨.inl innerAppKept,appCtx⟩ :=
  beta_lift_wire (.inr (.inr (outerArgOutside,true))) (.inl ⟨innerAppKept,appCtx⟩) rfl
theorem lambda_outer_arg : actualFanPresentation.site.reduce.wire (.inl ⟨.inl outerKept2,appArg⟩)=
    .inr (.inr (.inl (.inl outerArgOutside2),false)) :=
  action2_lift_wire (.inl ⟨outerKept2,appArg⟩) (.inr (.inr (outerArgOutside2,false))) beta_outer_arg
theorem lambda_inner_ctx : actualFanPresentation.site.reduce.wire (.inr (.inr (.inl (.inl outerArgOutside2),true)))=
    .inl ⟨.inl innerAppKept2,appCtx⟩ :=
  action2_lift_wire (.inr (.inr (outerArgOutside2,true))) (.inl ⟨innerAppKept2,appCtx⟩) beta_inner_ctx
theorem third_outer_arg : fanBra.site.reduce.wire (.inl ⟨thirdOuterNode,appArg⟩)=
    .inr (.inr (.inl (.inl outerArgOutside3),false)) :=
  action3_lift_wire (.inl ⟨outerKept3,appArg⟩) (.inr (.inr (outerArgOutside3,false))) lambda_outer_arg
theorem third_inner_ctx : fanBra.site.reduce.wire (.inr (.inr (.inl (.inl outerArgOutside3),true)))=
    .inl ⟨.inl innerAppKept3,appCtx⟩ :=
  action3_lift_wire (.inr (.inr (outerArgOutside3,true))) (.inl ⟨innerAppKept3,appCtx⟩) lambda_inner_ctx
noncomputable def innerTail : List (Endpoint fanBra.site.reduce) :=
  [.inl ⟨thirdOuterNode,appArg⟩,.inr (.inr (.inl (.inl outerArgOutside3),true))]
theorem innerTailLabels (a : Context) : Labelling fanBra.site.reduce innerTail a a :=
  .cons (by rw [third_outer_arg];exact .transparent _ false a) (.single _ _)
theorem innerTailFinish : innerTail.getLast?=some (fanBra.site.reduce.wire (.inl ⟨.inl innerAppKept3,appCtx⟩)) := by
  have h:=congrArg fanBra.site.reduce.wire third_inner_ctx
  simp only [Pairing.involutive] at h
  exact congrArg some h
noncomputable def innerEdges (branch : Bool) := (bodyAppParent branch).val++innerTail
theorem innerWord (branch : Bool) : accessWord fanBra.site.reduce (innerEdges branch)=Syntax.innerApp branch := by
  obtain ⟨a,b,labels⟩ := (bodyAppParent branch).property.1.1
  rw [innerEdges,accessWord_append _ _ _ labels.nonempty]
  change accessWord fanBra.site.reduce (bodyAppEdges branch)++_=_
  rw [bodyAppWord]
  cases branch <;> rfl
theorem innerAccessProof (branch : Bool) : IsRootAccess fanBra.site.reduce (.inl ()) (innerEdges branch) := by
  obtain ⟨a,b,labels⟩ := (bodyAppParent branch).property.1.1
  have parentLast : (bodyAppParent branch).val.getLast?=some (fanBra.site.reduce.wire (.inl ⟨thirdOuterNode,appCtx⟩)) := by
    change (bodyAppEdges branch).getLast?=_
    rw [bodyAppEdges,List.getLast?_append,bodyTailFinish,Option.some_or]
  have whole := labels.append_seam (innerTailLabels b) (by
    intro e f last first
    have he:=Option.some.inj (last.symm.trans parentLast)
    have hf:=Option.some.inj first
    subst e;subst f;rw [Pairing.involutive]
    exact LabelledTurn.node (g:=fanBra.site.reduce) thirdOuterNode appCtx appArg (.direct (.appArg b)))
  obtain ⟨flow,_,_,_,_⟩ := bra_certified
  have head : (innerEdges branch).head?=some (.inr (.inl (.inl ()))) := by
    rw [innerEdges,List.head?_append,(bodyAppParent branch).property.2.1,Option.some_or]
  have last : (innerEdges branch).getLast?=some (fanBra.site.reduce.wire (.inl ⟨.inl innerAppKept3,appCtx⟩)) := by
    rw [innerEdges,List.getLast?_append,innerTailFinish,Option.some_or]
  exact ⟨⟨⟨a,b,whole⟩,whole.root_forward_of_flow flow (.inl ()) head rfl⟩,head,⟨.app,by
    unfold accessKind;rw [last];simp only [Option.bind_some,Pairing.involutive];rfl⟩⟩
noncomputable def innerAccess (branch : Bool) : RootAccess fanBra.site.reduce (.inl ()) := ⟨innerEdges branch,innerAccessProof branch⟩
end Lamping.Checks.FanAppAuxiliaryArgumentReachable.ThirdDomain
namespace Lamping.Checks.FanAppAuxiliaryArgumentReachable.Domain
open AG Graph Lambda Lambda.Labelled Base

private theorem certified_flow {g : ActualNet (Boundary term)} (certificate : Certified g) :
    Nonempty (FlowBalance g.net initialBoundaryPolarity) := by
  obtain ⟨flow,_,_,_,_⟩ := certificate
  exact ⟨flow⟩
noncomputable def fourthFlow : FlowBalance fanCro.site.reduce initialBoundaryPolarity :=
  Classical.choice (certified_flow cro_certified)
private theorem iso_node_endpoint
    {N M B W V : Type} [FiniteNames N] [FiniteNames M] [FiniteNames B]
    [FiniteNames W] [FiniteNames V] {g : Net signature N B W} {h : Net signature M B V}
    (iso : NetIso g h) (n : N) (m : M) (nodes : iso.nodes n=m)
    (p : Port (g.label n).sort) (q : Port (h.label m).sort) (sameRole : HEq p q) :
    iso.ends (.inl ⟨n,p⟩)=.inl ⟨m,q⟩ := by
  exact (iso.node_end ⟨n,p⟩).trans
    (congrArg Sum.inl (Sigma.ext ((iso.port_node ⟨n,p⟩).trans nodes)
      ((iso.port_role ⟨n,p⟩).trans sameRole)))
private theorem corridor_kept_endpoint
    {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} {s : Schema} {active passive : N}
    {p : Port (g.label active).sort} {q : Port (g.label passive).sort}
    (presentation : PhysicalCorridorPresentation g s active passive p q)
    (n : N) (port : Port (g.label n).sort) (notActive : n≠active) (notPassive : n≠passive) :
    ∃ keptPort : NodePort signature presentation.Kept presentation.kept,
      presentation.sourceIso.ends (.inl ⟨n,port⟩)=.inl ⟨.inl keptPort.1,keptPort.2⟩ := by
  have activeMap := (presentation.sourceIso.port_node ⟨active,p⟩).symm.trans
    (congrArg Sigma.fst presentation.active_port)
  have passiveMap := (presentation.sourceIso.port_node ⟨passive,q⟩).symm.trans
    (congrArg Sigma.fst presentation.passive_port)
  rcases imageEq : presentation.sourceIso.ports ⟨n,port⟩ with ⟨node,out⟩
  have nodeMap := (presentation.sourceIso.port_node ⟨n,port⟩).symm.trans (congrArg Sigma.fst imageEq)
  cases node with
  | inl keptNode =>
    exact ⟨⟨keptNode,out⟩,(presentation.sourceIso.node_end ⟨n,port⟩).trans (congrArg Sum.inl imageEq)⟩
  | inr tag =>
    cases tag with
    | inl u => cases u;exact False.elim (notActive (presentation.sourceIso.nodes.injective (nodeMap.trans activeMap.symm)))
    | inr u => cases u;exact False.elim (notPassive (presentation.sourceIso.nodes.injective (nodeMap.trans passiveMap.symm)))

private theorem app_target_kept_of_source_kept
    {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
    {kept : K→Label signature} {i j : Nat} {lt : i<j}
    (site : PathSite (.fanAction .app i j lt) kept (B:=B) (W:=W) (V:=V))
    {directions : B→Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {t : LTerm}
    (matching : Matches site.net root t.erase)
    (source : RootAccess site.net root) (target : RootAccess site.reduce root)
    (word : accessWord site.net source.val=accessWord site.reduce target.val)
    (sourceKept : ∃port : NodePort signature K kept,source.val.getLast?=some (site.net.wire (.inl ⟨.inl port.1,port.2⟩))) :
    ∃p : NodePort signature K kept,target.val.getLast?=some (site.reduce.wire (.inl ⟨.inl p.1,p.2⟩)) := by
  obtain ⟨port,sourceAt⟩ := sourceKept
  obtain ⟨principal⟩ := site.actionPrincipal_exists
  rcases site.fan_app_access_cases target with kept|⟨copy,finish⟩
  · exact kept
  · obtain ⟨a,b,labels⟩ := target.property.1.1
    obtain ⟨_,_,_,sourceFinish,_⟩ := site.fan_aux_canonical_access
      flow root positive matching principal source target word copy false finish labels
    have ends:=congrArg site.net.wire (Option.some.inj (sourceAt.symm.trans sourceFinish))
    simp only [Pairing.involutive] at ends
    cases ends
private theorem app_target_copied_of_source_selected
    {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
    {kept : K→Label signature} {i j : Nat} {lt : i<j}
    (site : PathSite (.fanAction .app i j lt) kept (B:=B) (W:=W) (V:=V))
    {directions : B→Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {t : LTerm}
    (matching : Matches site.net root t.erase)
    (source : RootAccess site.net root) (target : RootAccess site.reduce root)
    (word : accessWord site.net source.val=accessWord site.reduce target.val)
    (sourceAt : source.val.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),appCtx⟩))) :
    ∃b : Bool,target.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl b),appCtx⟩)) := by
  obtain ⟨principal⟩ := site.actionPrincipal_exists
  rcases site.fan_app_access_cases target with ⟨port,finish⟩|copied
  · obtain ⟨a,b,labels⟩ := target.property.1.1
    obtain ⟨_,_,sourceFinish⟩ := site.action_kept_canonical_access (.fan .app i j lt)
      flow root positive matching principal source target word port.1 port.2 finish labels
    have ends:=congrArg site.net.wire (Option.some.inj (sourceAt.symm.trans sourceFinish))
    simp only [Pairing.involutive] at ends
    have nodes:=congrArg Sigma.fst (Sum.inl.inj ends)
    cases nodes
  · exact copied
private theorem iso_root_finish
    {N M B W V : Type} [FiniteNames N] [FiniteNames M] [FiniteNames B]
    [FiniteNames W] [FiniteNames V] {g : Net signature N B W} {h : Net signature M B V}
    (iso : NetIso g h) {root : B} (parent : RootAccess g root) (e : Endpoint g)
    (last : parent.val.getLast?=some (g.wire e)) :
    (iso.rootAccessBij root parent).val.getLast?=some (h.wire (iso.ends e)) := by
  change (parent.val.map iso.ends).getLast?=_
  rw [List.getLast?_map,last]
  exact congrArg some (iso.wiring e)


private theorem corridor_root_kept_finish
    {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} {s : Schema} {active passive : N}
    {p : Port (g.label active).sort} {q : Port (g.label passive).sort}
    (presentation : PhysicalCorridorPresentation g s active passive p q)
    {root : B} (parent : RootAccess g root) (n : N) (port : Port (g.label n).sort)
    (last : parent.val.getLast?=some (g.wire (.inl ⟨n,port⟩)))
    (notActive : n≠active) (notPassive : n≠passive) :
    ∃keptPort : NodePort signature presentation.Kept presentation.kept,
      (presentation.sourceIso.rootAccessBij root parent).val.getLast?=
        some (presentation.site.net.wire (.inl ⟨.inl keptPort.1,keptPort.2⟩)) := by
  have mapped := iso_root_finish presentation.sourceIso parent (.inl ⟨n,port⟩) last
  obtain ⟨keptPort,endpoint⟩ := corridor_kept_endpoint presentation n port notActive notPassive
  exact ⟨keptPort,mapped.trans (congrArg (fun e=>some (presentation.site.net.wire e)) endpoint)⟩
theorem fourthMatches : Matches fanCro.site.reduce (.inl ()) current.erase := by
  obtain ⟨_,_,_,_,m⟩ := cro_certified;exact m
theorem fourthSourceMatches : Matches fanCro.site.net (.inl ()) current.erase := by
  obtain ⟨_,_,_,_,m⟩ := bra_certified;exact fanCro.sourceIso.matches m

noncomputable def outerKept4 : fanCro.Kept := ⟨ThirdDomain.thirdOuterNode,by
  constructor
  · intro h;cases h
  · intro h;have hs:=congrArg Subtype.val (Sum.inl.inj h)
    have ht:=congrArg Subtype.val (Sum.inl.inj hs)
    have hu:=congrArg Subtype.val (Sum.inl.inj ht);cases hu⟩
noncomputable def fourthSourceParent (branch : Bool) : RootAccess fanCro.site.net (.inl ()) :=
  fanCro.sourceIso.rootAccessBij (.inl ()) (ThirdDomain.bodyAppParent branch)
theorem fourthSourceParentWord (branch : Bool) : accessWord fanCro.site.net (fourthSourceParent branch).val=Syntax.start branch :=
  (fanCro.sourceIso.accessWord (ThirdDomain.bodyAppParent branch).val).trans (ThirdDomain.bodyAppWord branch)
theorem fourthSourceParentFinish (branch : Bool) : (fourthSourceParent branch).val.getLast?=
    some (fanCro.site.net.wire (.inl ⟨.inl outerKept4,appCtx⟩)) := by
  change ((ThirdDomain.bodyAppParent branch).val.map fanCro.sourceIso.ends).getLast?=_
  have last : (ThirdDomain.bodyAppParent branch).val.getLast?=some (fanBra.site.reduce.wire (.inl ⟨ThirdDomain.thirdOuterNode,appCtx⟩)) := by
    change (ThirdDomain.bodyAppEdges branch).getLast?=_
    rw [ThirdDomain.bodyAppEdges,List.getLast?_append,ThirdDomain.bodyTailFinish,Option.some_or]
  rw [List.getLast?_map,last];simp only [Option.map_some]
  apply congrArg some
  rw [fanCro.sourceIso.wiring]
  apply congrArg fanCro.site.net.wire
  apply fanCro.sourceIso.symm.ends.injective
  change fanCro.sourceIso.ends.invFun (fanCro.sourceIso.ends.toFun (.inl ⟨ThirdDomain.thirdOuterNode,appCtx⟩))=_
  rw [fanCro.sourceIso.ends.left_inv];rfl
noncomputable def fourthParent (branch : Bool) : RootAccess fanCro.site.reduce (.inl ()) :=
  Classical.choose (Matches.observation fanCro.site.reduce fourthMatches (Syntax.parentPosition branch))
theorem fourthParentWord (branch : Bool) : accessWord fanCro.site.reduce (fourthParent branch).val=Syntax.start branch :=
  (Classical.choose_spec (Matches.observation fanCro.site.reduce fourthMatches (Syntax.parentPosition branch))).1
theorem fourthParentFinish (branch : Bool) : (fourthParent branch).val.getLast?=
    some (fanCro.site.reduce.wire (.inl ⟨.inl outerKept4,appCtx⟩)) := by
  obtain ⟨port,finish⟩ := fanCro.site.fan_control_access_kept (Or.inr (Or.inl rfl)) (fourthParent branch)
  obtain ⟨a,c,labels⟩ := (fourthParent branch).property.1.1
  obtain ⟨principal⟩ := fanCro.site.actionPrincipal_exists
  obtain ⟨flow,_,_,_,_⟩ := bra_certified
  have normalized := fanCro.site.action_kept_canonical_access (.fan .cro 0 2 (by decide))
    (fanCro.sourceIso.flowBalance flow) (.inl ()) rfl fourthSourceMatches principal
    (fourthSourceParent branch) (fourthParent branch) ((fourthSourceParentWord branch).trans (fourthParentWord branch).symm)
    port.1 port.2 finish labels
  have endEq:=congrArg fanCro.site.net.wire (Option.some.inj ((fourthSourceParentFinish branch).symm.trans normalized.2.2))
  simp only [Pairing.involutive] at endEq
  rcases port with ⟨node,p⟩
  have nodeEq : outerKept4=node := Sum.inl.inj (congrArg Sigma.fst (Sum.inl.inj endEq))
  subst node
  have portEq : (appCtx : Port (fanCro.kept outerKept4).sort)=p := eq_of_heq (Sigma.mk.inj (Sum.inl.inj endEq)).2
  subst p;exact finish
#print axioms fourthParentFinish
noncomputable def fourthSourceChild (branch : Bool) : RootAccess fanCro.site.net (.inl ()) :=
  fanCro.sourceIso.rootAccessBij (.inl ()) (ThirdDomain.innerAccess branch)
theorem fourthSourceChildWord (branch : Bool) : accessWord fanCro.site.net (fourthSourceChild branch).val=Syntax.innerApp branch :=
  (fanCro.sourceIso.accessWord (ThirdDomain.innerAccess branch).val).trans (ThirdDomain.innerWord branch)
theorem fourthSourceChildFinish (branch : Bool) : (fourthSourceChild branch).val.getLast?=
    some (fanCro.site.net.wire (.inl ⟨.inl innerAppKept4,appCtx⟩)) := by
  change ((ThirdDomain.innerAccess branch).val.map fanCro.sourceIso.ends).getLast?=_
  have last : (ThirdDomain.innerAccess branch).val.getLast?=some (fanBra.site.reduce.wire (.inl ⟨.inl innerAppKept3,appCtx⟩)) := by
    change (ThirdDomain.innerEdges branch).getLast?=_
    rw [ThirdDomain.innerEdges,List.getLast?_append,ThirdDomain.innerTailFinish,Option.some_or]
  rw [List.getLast?_map,last];simp only [Option.map_some]
  apply congrArg some
  rw [fanCro.sourceIso.wiring]
  apply congrArg fanCro.site.net.wire
  apply fanCro.sourceIso.symm.ends.injective
  change fanCro.sourceIso.ends.invFun (fanCro.sourceIso.ends.toFun (.inl ⟨.inl innerAppKept3,appCtx⟩))=_
  rw [fanCro.sourceIso.ends.left_inv];rfl
noncomputable def fourthChild (branch : Bool) : RootAccess fanCro.site.reduce (.inl ()) :=
  Classical.choose (Matches.observation fanCro.site.reduce fourthMatches (Syntax.innerPosition branch))
theorem fourthChildWord (branch : Bool) : accessWord fanCro.site.reduce (fourthChild branch).val=Syntax.innerApp branch :=
  (Classical.choose_spec (Matches.observation fanCro.site.reduce fourthMatches (Syntax.innerPosition branch))).1
theorem fourthChildFinish (branch : Bool) : (fourthChild branch).val.getLast?=
    some (fanCro.site.reduce.wire (.inl ⟨.inl innerAppKept4,appCtx⟩)) := by
  obtain ⟨port,finish⟩ := fanCro.site.fan_control_access_kept (Or.inr (Or.inl rfl)) (fourthChild branch)
  obtain ⟨a,c,labels⟩ := (fourthChild branch).property.1.1
  obtain ⟨principal⟩ := fanCro.site.actionPrincipal_exists
  obtain ⟨flow,_,_,_,_⟩ := bra_certified
  have normalized := fanCro.site.action_kept_canonical_access (.fan .cro 0 2 (by decide))
    (fanCro.sourceIso.flowBalance flow) (.inl ()) rfl fourthSourceMatches principal
    (fourthSourceChild branch) (fourthChild branch) ((fourthSourceChildWord branch).trans (fourthChildWord branch).symm)
    port.1 port.2 finish labels
  have endEq:=congrArg fanCro.site.net.wire (Option.some.inj ((fourthSourceChildFinish branch).symm.trans normalized.2.2))
  simp only [Pairing.involutive] at endEq
  rcases port with ⟨node,p⟩
  have nodeEq : innerAppKept4=node := Sum.inl.inj (congrArg Sigma.fst (Sum.inl.inj endEq))
  subst node
  have portEq : (appCtx : Port (fanCro.kept innerAppKept4).sort)=p := eq_of_heq (Sigma.mk.inj (Sum.inl.inj endEq)).2
  subst p;exact finish
#print axioms fourthChildFinish
end Lamping.Checks.FanAppAuxiliaryArgumentReachable.Domain
namespace Lamping.Checks.FanAppAuxiliaryArgumentReachable.Domain
open AG Graph Lambda Lambda.Labelled Base
noncomputable def sourceParent (branch : Bool) : RootAccess fanApp.site.net (.inl ()) :=
  fanApp.sourceIso.rootAccessBij (.inl ()) (fourthParent branch)
noncomputable def sourceChild (branch : Bool) : RootAccess fanApp.site.net (.inl ()) :=
  fanApp.sourceIso.rootAccessBij (.inl ()) (fourthChild branch)
theorem sourceParentWord (branch : Bool) : accessWord fanApp.site.net (sourceParent branch).val=Syntax.start branch :=
  (fanApp.sourceIso.accessWord (fourthParent branch).val).trans (fourthParentWord branch)
theorem sourceChildWord (branch : Bool) : accessWord fanApp.site.net (sourceChild branch).val=Syntax.innerApp branch :=
  (fanApp.sourceIso.accessWord (fourthChild branch).val).trans (fourthChildWord branch)
theorem sourceChildFinish (branch : Bool) : (sourceChild branch).val.getLast?=
    some (fanApp.site.net.wire (.inl ⟨.inr (.inr ()),appCtx⟩)) := by
  have mapped := iso_root_finish (g:=fanCro.site.reduce) (h:=fanApp.site.net)
    fanApp.sourceIso (fourthChild branch) (.inl ⟨.inl innerAppKept4,appCtx⟩) (fourthChildFinish branch)
  have nodeMap := (fanApp.sourceIso.port_node ⟨innerAppAfterCro,.inl ()⟩).symm.trans
    (congrArg Sigma.fst fanApp.passive_port)
  have endpoint := iso_node_endpoint fanApp.sourceIso innerAppAfterCro (.inr (.inr ())) nodeMap appCtx appCtx HEq.rfl
  exact mapped.trans (congrArg (fun e=>some (fanApp.site.net.wire e)) endpoint)
noncomputable def outerKept5 : fanApp.Kept := ⟨.inl outerKept4,by
  constructor
  · intro same;cases same
  · intro same
    have h:=congrArg Subtype.val (Sum.inl.inj same)
    have h2:=congrArg Subtype.val (Sum.inl.inj h)
    have h3:=congrArg Subtype.val (Sum.inl.inj h2)
    have h4:=congrArg Subtype.val (Sum.inl.inj h3)
    cases h4⟩

theorem sourceParentFinish (branch : Bool) : ∃port : NodePort signature fanApp.Kept fanApp.kept,
    (sourceParent branch).val.getLast?=some (fanApp.site.net.wire (.inl ⟨.inl port.1,port.2⟩)) := by
  have notActive : (.inl outerKept4 : fanCro.Kept⊕(Bool⊕Unit))≠fanAfterCro := by
    intro same;cases same
  have notPassive : (.inl outerKept4 : fanCro.Kept⊕(Bool⊕Unit))≠innerAppAfterCro := by
    intro same
    have h:=congrArg Subtype.val (Sum.inl.inj same)
    have h2:=congrArg Subtype.val (Sum.inl.inj h)
    have h3:=congrArg Subtype.val (Sum.inl.inj h2)
    have h4:=congrArg Subtype.val (Sum.inl.inj h3)
    cases h4
  exact corridor_root_kept_finish (g:=fanCro.site.reduce)
    (s:=Schema.fanAction .app 0 2 (by decide)) (active:=fanAfterCro) (passive:=innerAppAfterCro)
    (p:=.inl ()) (q:=.inl ()) fanApp (fourthParent branch) (.inl outerKept4) appCtx
    (fourthParentFinish branch) notActive notPassive
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
  exact app_target_kept_of_source_kept fanApp.site (fanApp.sourceIso.flowBalance fourthFlow)
    (.inl ()) rfl actual_source_matches (sourceParent branch) (targetParent branch)
    ((sourceParentWord branch).trans (targetParentWord branch).symm) (sourceParentFinish branch)
/-- The selected SOURCE child's context forces the allocated APP target case. -/
theorem targetChildCopied (branch : Bool) : ∃copy : Bool,
    (targetChild branch).val.getLast?=some (fanApp.site.reduce.wire (.inl ⟨.inr (.inl copy),appCtx⟩)) := by
  exact app_target_copied_of_source_selected fanApp.site (fanApp.sourceIso.flowBalance fourthFlow)
    (.inl ()) rfl actual_source_matches (sourceChild branch) (targetChild branch)
    ((sourceChildWord branch).trans (targetChildWord branch).symm) (sourceChildFinish branch)
end Lamping.Checks.FanAppAuxiliaryArgumentReachable.Domain

namespace Lamping.Checks.FanAppAuxiliaryArgumentReachable.Syntax
open AG Graph Lambda Lambda.Labelled

def sourceVertex (b : Bool) : SyntaxIncidence.Vertex current :=
  some ⟨start b,Or.inl ⟨_,_,_,parent_lookup b⟩⟩
def targetVertex (b : Bool) : SyntaxIncidence.Vertex current :=
  some ⟨innerApp b,Or.inl ⟨_,_,_,inner_lookup b⟩⟩
theorem actual_source_endpoint (b : Bool) : SyntaxIncidence.source current (innerPosition b)=sourceVertex b :=
  SyntaxIncidence.source_eq_of_spec current (innerPosition b)
    ⟨.arg,payloadOuter,.appArg (.atom 10),(by cases b <;> rfl),parent_lookup b,.arg⟩
theorem actual_target_endpoint (b : Bool) : SyntaxIncidence.target current targetClosed (innerPosition b)=targetVertex b :=
  SyntaxIncidence.target_eq_of_spec current targetClosed (innerPosition b) (Or.inl rfl)
theorem auxiliary_argument (b : Bool) : AuxiliaryAt current (innerApp b) := by
  constructor
  · rintro ⟨parent,stamp,fn,arg,split,_⟩
    have last:=congrArg List.getLast? split
    cases b <;> simp [innerApp,left,right] at last
  · rintro ⟨stamp,body,lookup⟩
    rw [inner_lookup b] at lookup;cases lookup
theorem two_actual_successful_endpoints (b : Bool) :
    EndpointChain current (SyntaxIncidence.source current (innerPosition b)) (sourceEdges b) ∧
    EndpointChain current (SyntaxIncidence.target current targetClosed (innerPosition b)) (targetEdges b) := by
  rw [actual_source_endpoint,actual_target_endpoint]
  exact ⟨source_chain b,target_chain b⟩
theorem same_pair_successful_endpoint_isos (b : Bool) :
    SuccessfulEndpointIso current targetClosed
      (SyntaxIncidence.source current (innerPosition b)) (SyntaxIncidence.source current (innerPosition b)) ∧
    SuccessfulEndpointIso current targetClosed
      (SyntaxIncidence.target current targetClosed (innerPosition b)) (SyntaxIncidence.target current targetClosed (innerPosition b)) :=
  ⟨.refl_of_chain (two_actual_successful_endpoints b).1,.refl_of_chain (two_actual_successful_endpoints b).2⟩
#print axioms auxiliary_argument
#print axioms two_actual_successful_endpoints
#print axioms same_pair_successful_endpoint_isos
end Lamping.Checks.FanAppAuxiliaryArgumentReachable.Syntax

namespace Lamping.Checks.FanAppAuxiliaryArgumentReachable.Domain
open AG Graph Lambda Lambda.Labelled Base

private theorem access_last_transport
    {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} {root : B} (first second : RootAccess g root)
    (same : first=second) {P : Option (Endpoint g)→Prop}
    (known : P second.val.getLast?) : P first.val.getLast? := by
  cases same;exact known

theorem actual_selected_argument_domain
    (source : OccurrenceFragmentSelection current fanApp.site.net (.inl ()))
    (target : OccurrenceFragmentSelection current fanApp.site.reduce (.inl ())) (branch : Bool) :
    (∃port : NodePort signature fanApp.Kept fanApp.kept,
      (source (Syntax.parentPosition branch)).fragment.access.val.getLast?=
        some (fanApp.site.net.wire (.inl ⟨.inl port.1,port.2⟩))) ∧
    (source (Syntax.innerPosition branch)).fragment.access.val.getLast?=
      some (fanApp.site.net.wire (.inl ⟨.inr (.inr ()),appCtx⟩)) ∧
    (∃port : NodePort signature fanApp.Kept fanApp.kept,
      (target (Syntax.parentPosition branch)).fragment.access.val.getLast?=
        some (fanApp.site.reduce.wire (.inl ⟨.inl port.1,port.2⟩))) ∧
    ∃copy : Bool,(target (Syntax.innerPosition branch)).fragment.access.val.getLast?=
      some (fanApp.site.reduce.wire (.inl ⟨.inr (.inl copy),appCtx⟩)) := by
  have sp : (source (Syntax.parentPosition branch)).fragment.access=sourceParent branch :=
    actual_source_matches.accessWord_injective
      ((source (Syntax.parentPosition branch)).fragment.word.trans (sourceParentWord branch).symm)
  have sc : (source (Syntax.innerPosition branch)).fragment.access=sourceChild branch :=
    actual_source_matches.accessWord_injective
      ((source (Syntax.innerPosition branch)).fragment.word.trans (sourceChildWord branch).symm)
  have tp : (target (Syntax.parentPosition branch)).fragment.access=targetParent branch :=
    actual_target_matches.accessWord_injective
      ((target (Syntax.parentPosition branch)).fragment.word.trans (targetParentWord branch).symm)
  have tc : (target (Syntax.innerPosition branch)).fragment.access=targetChild branch :=
    actual_target_matches.accessWord_injective
      ((target (Syntax.innerPosition branch)).fragment.word.trans (targetChildWord branch).symm)
  refine ⟨?_,?_,?_,?_⟩
  · exact access_last_transport _ _ sp
      (P:=fun last=>∃port : NodePort signature fanApp.Kept fanApp.kept,
        last=some (fanApp.site.net.wire (.inl ⟨.inl port.1,port.2⟩))) (sourceParentFinish branch)
  · exact access_last_transport _ _ sc
      (P:=fun last=>last=some (fanApp.site.net.wire (.inl ⟨.inr (.inr ()),appCtx⟩))) (sourceChildFinish branch)
  · exact access_last_transport _ _ tp
      (P:=fun last=>∃port : NodePort signature fanApp.Kept fanApp.kept,
        last=some (fanApp.site.reduce.wire (.inl ⟨.inl port.1,port.2⟩))) (targetParentKept branch)
  · exact access_last_transport _ _ tc
      (P:=fun last=>∃copy : Bool,last=some (fanApp.site.reduce.wire (.inl ⟨.inr (.inl copy),appCtx⟩))) (targetChildCopied branch)
theorem actual_selections_nonempty :
    Nonempty (OccurrenceFragmentSelection current fanApp.site.net (.inl ())) ∧
    Nonempty (OccurrenceFragmentSelection current fanApp.site.reduce (.inl ())) :=
  ⟨actual_source_matches.occurrence_fragment_selection Syntax.targetClosed,
   actual_target_matches.occurrence_fragment_selection Syntax.targetClosed⟩
#print axioms sourceParentFinish
#print axioms sourceChildFinish
#print axioms targetParentKept
#print axioms targetChildCopied
#print axioms actual_selected_argument_domain
#print axioms actual_selections_nonempty
#print axioms Syntax.actualHistory
#print axioms Syntax.endpoint_chain_lengths
end Lamping.Checks.FanAppAuxiliaryArgumentReachable.Domain

namespace Lamping.Checks.FanAppAuxiliaryArgumentReachable.Domain
open AG Graph Lambda Lambda.Labelled Base

private theorem argument_kc_cut_from_actual_ends
    {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
    {kept : K→Label signature} {i j : Nat} {lt : i<j}
    (site : PathSite (.fanAction .app i j lt) kept (B:=B) (W:=W) (V:=V))
    {directions : B→Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {term : LTerm}
    (sourceMatches : Matches site.net root term.erase) (targetMatches : Matches site.reduce root term.erase)
    {edge : SourceEdge} {position : Path} {parentTerm : LTerm} {step : Step}
    (source : SourceEdgeFragment term site.net root edge position)
    (target : SourceEdgeFragment term site.reduce root edge position)
    (role : SourceDeparture parentTerm step edge.fromPort)
    (sourceParent : RootAccess site.net root) (targetParent : RootAccess site.reduce root)
    (sourceWord : position=accessWord site.net sourceParent.val++[step])
    (targetWord : position=accessWord site.reduce targetParent.val++[step])
    (parentKept : ∃port : NodePort signature K kept,targetParent.val.getLast?=
      some (site.reduce.wire (.inl ⟨.inl port.1,port.2⟩)))
    (childCopied : ∃copy : Bool,target.access.val.getLast?=
      some (site.reduce.wire (.inl ⟨.inr (.inl copy),appCtx⟩))) :
    let c := cutFragment site.net (pathPartition (Schema.fanAction .app i j lt) V) site.closed
    let rhs := (Schema.fanAction .app i j lt).right.net
    ∃principal : SiteActionPrincipal site,∃copy : Bool,
    ∃pivot : Endpoint c,∃raw : List (PlugSegment c rhs),∃seam output : Context,
      target.segments.map (plugEnd c.label rhs.label).invFun=raw++
        [.inr (.inr (.inl (.inr false))),.inr (.inl ⟨.inr false,.inr copy⟩)] ∧
      ActionCanonicalBlocks site principal (.inl pivot::raw)
        (site.outsideEnd pivot::source.segments) ∧
      PlugLabelling c rhs (.inl pivot::raw) seam output := by
  obtain ⟨principal⟩ := site.actionPrincipal_exists
  obtain ⟨copy,childAt⟩ := childCopied
  obtain ⟨port,parentAt⟩ := parentKept
  obtain ⟨a,b,wholeLabels⟩ := target.access.property.1.1
  obtain ⟨pivot,raw,seam,output,_oldParent,_newParent,shape,relation,labels⟩ :=
    source.fan_kept_parent_copied_app_context_cut site flow root positive sourceMatches targetMatches
      principal target role sourceParent targetParent sourceWord targetWord port.1 port.2 parentAt copy childAt wholeLabels
  exact ⟨principal,copy,pivot,raw,seam,output,shape,relation,labels⟩

private theorem occurrence_argument_kc_cut_from_actual_ends
    {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
    {kept : K→Label signature} {i j : Nat} {lt : i<j}
    (site : PathSite (.fanAction .app i j lt) kept (B:=B) (W:=W) (V:=V))
    {directions : B→Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {term : LTerm} {position : Path}
    {environment : List Lambda.Labelled.Label} {context : SourcePort} {subterm parentTerm : LTerm} {step : Step}
    (sourceMatches : Matches site.net root term.erase) (targetMatches : Matches site.reduce root term.erase)
    (source : OccurrenceFragment term site.net root position)
    (target : OccurrenceFragment term site.reduce root position)
    (expected : SourceSubterm [] .external term position environment context subterm)
    (role : SourceDeparture parentTerm step context)
    (sourceParent : RootAccess site.net root) (targetParent : RootAccess site.reduce root)
    (sourceWord : position=accessWord site.net sourceParent.val++[step])
    (targetWord : position=accessWord site.reduce targetParent.val++[step])
    (parentKept : ∃port : NodePort signature K kept,targetParent.val.getLast?=
      some (site.reduce.wire (.inl ⟨.inl port.1,port.2⟩)))
    (childCopied : ∃copy : Bool,target.fragment.access.val.getLast?=
      some (site.reduce.wire (.inl ⟨.inr (.inl copy),appCtx⟩))) :
    let c := cutFragment site.net (pathPartition (Schema.fanAction .app i j lt) V) site.closed
    let rhs := (Schema.fanAction .app i j lt).right.net
    ∃principal : SiteActionPrincipal site,∃copy : Bool,
    ∃pivot : Endpoint c,∃raw : List (PlugSegment c rhs),∃seam output : Context,
      target.fragment.segments.map (plugEnd c.label rhs.label).invFun=raw++
        [.inr (.inr (.inl (.inr false))),.inr (.inl ⟨.inr false,.inr copy⟩)] ∧
      ActionCanonicalBlocks site principal (.inl pivot::raw)
        (site.outsideEnd pivot::source.fragment.segments) ∧
      PlugLabelling c rhs (.inl pivot::raw) seam output := by
  rcases source with ⟨sub,env,ctx,occ,source⟩
  rcases target with ⟨_,_,_,other,target⟩
  obtain ⟨rfl,rfl,rfl⟩ := occ.same_occurrence other
  obtain ⟨rfl,rfl,rfl⟩ := occ.same_occurrence expected
  have fromEq : (sourceEdge env ctx sub).fromPort=ctx := by cases sub <;> rfl
  have actualRole : SourceDeparture parentTerm step (sourceEdge env ctx sub).fromPort := by
    rw [fromEq];exact role
  exact argument_kc_cut_from_actual_ends site flow root positive sourceMatches targetMatches
    source target actualRole sourceParent targetParent sourceWord targetWord parentKept childCopied

noncomputable abbrev argumentCut : Net signature fanApp.Kept (Boundary term⊕(Bool⊕Bool)) fanApp.Outside :=
  cutFragment fanApp.site.net
    (pathPartition (Schema.fanAction .app 0 2 (by decide)) fanApp.Inside) fanApp.site.closed
private abbrev argumentRight := (Schema.fanAction .app 0 2 (by decide)).right.net

theorem actual_argument_kept_copied_cut (branch : Bool)
    (source : OccurrenceFragment current fanApp.site.net (.inl ()) (Syntax.innerApp branch))
    (target : OccurrenceFragment current fanApp.site.reduce (.inl ()) (Syntax.innerApp branch)) :
    ∃principal : SiteActionPrincipal fanApp.site,∃copy : Bool,
    ∃pivot : Endpoint argumentCut,∃raw : List (PlugSegment argumentCut argumentRight),∃seam output : Context,
      target.fragment.segments.map (plugEnd argumentCut.label argumentRight.label).invFun=raw++
        [.inr (.inr (.inl (.inr false))),.inr (.inl ⟨.inr false,.inr copy⟩)] ∧
      ActionCanonicalBlocks fanApp.site principal (.inl pivot::raw)
        (fanApp.site.outsideEnd pivot::source.fragment.segments) ∧
      PlugLabelling argumentCut argumentRight (.inl pivot::raw) seam output := by
  have targetEq : target.fragment.access=targetChild branch :=
    actual_target_matches.accessWord_injective (target.fragment.word.trans (targetChildWord branch).symm)
  have childCopied : ∃copy : Bool,target.fragment.access.val.getLast?=
      some (fanApp.site.reduce.wire (.inl ⟨.inr (.inl copy),appCtx⟩)) :=
    access_last_transport _ _ targetEq
      (P:=fun last=>∃copy : Bool,last=some (fanApp.site.reduce.wire (.inl ⟨.inr (.inl copy),appCtx⟩))) (targetChildCopied branch)
  exact occurrence_argument_kc_cut_from_actual_ends (parentTerm:=Syntax.payloadOuter) fanApp.site (fanApp.sourceIso.flowBalance fourthFlow)
    (.inl ()) rfl actual_source_matches actual_target_matches source target (Syntax.inner_occurrence branch)
    (SourceDeparture.arg) (sourceParent branch) (targetParent branch)
    (by rw [sourceParentWord];cases branch <;> rfl)
    (by rw [targetParentWord];cases branch <;> rfl)
    (targetParentKept branch) childCopied
#print axioms actual_argument_kept_copied_cut
end Lamping.Checks.FanAppAuxiliaryArgumentReachable.Domain
