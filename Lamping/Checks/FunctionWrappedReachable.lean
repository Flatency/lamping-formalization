import Lamping.Checks.OldChainBetaFixture
import Lamping.Checks.WrappedSuccessfulChains
import Lamping.Lamping.ActionMatching
import Lamping.Lamping.GraphRootInputPreservation
import Lamping.Lamping.ReachableTransparency

/-! Actual wrapped unary-APP candidate.  No AuxiliarySeparation premise.
The outer application is retained throughout the intended administrative actions.
-/
namespace Lamping.Checks.FunctionWrappedReachable
open AG Graph Lambda Lambda.Labelled

abbrev argument : Term := .lam (.app (.var 0) identity)
abbrev inner : Term := .app identity argument
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
  change ((0<1) ∧ ((0<1) ∧ (0<2))) ∧ (0<1)
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
def oldCro : (encode 0 term).N := .inr (.inl (.inr (.inl (.inr ()))))
def oldArgLam : (encode 0 term).N := .inr (.inl (.inr (.inr (.inl ()))))
def croKept : RemainingNodes app lam := ⟨oldCro,by constructor <;> intro h <;> cases h⟩
def argKept : RemainingNodes app lam := ⟨oldArgLam,by constructor <;> intro h <;> cases h⟩
theorem actual_kept_cro_label : concrete.kept croKept=label .cro 0 := rfl
theorem actual_kept_arg_label : concrete.kept argKept=label .lam 1 := rfl
noncomputable def next (e : Endpoint concrete.site.reduce) : Endpoint concrete.site.reduce :=
  match concrete.site.reduce.wire e with
  | .inr (.inr (w,d)) => .inr (.inr (w,!d))
  | _ => e
noncomputable def croPrincipal : Endpoint concrete.site.reduce := .inl ⟨.inl croKept,.inl ()⟩
def bindingWire : (encode 0 term).W := .inl (.inr (.inl (.inl (.inr (.inl (.inr (.inr ⟨0,rfl⟩)))))))
def argumentWire : (encode 0 term).W := .inl (.inr (.inl (.inr (.inr (.inl ())))))
def bindingOutside : concrete.Outside := ⟨bindingWire,by
  rintro ⟨d,h⟩
  simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h <;> cases h⟩
def argumentOutside : concrete.Outside := ⟨argumentWire,by
  rintro ⟨d,h⟩
  simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h <;> cases h⟩
theorem actual_old_cro_wire : concrete.site.net.wire (.inl ⟨.inl croKept,.inl ()⟩)=
    .inr (.inr (.inl bindingOutside,true)) := by
  apply concrete.sourceIso.symm.ends.injective
  rw [concrete.sourceIso.symm.wiring]
  rfl
theorem actual_old_binding_wire : concrete.site.net.wire (.inr (.inr (.inl bindingOutside,false)))=
    .inl ⟨.inr (.inr ()),lamBind⟩ := by
  apply concrete.sourceIso.symm.ends.injective
  rw [concrete.sourceIso.symm.wiring]
  rfl
theorem actual_old_argument_wire : concrete.site.net.wire (.inl ⟨.inr (.inl ()),appArg⟩)=
    .inr (.inr (.inl argumentOutside,false)) := by
  apply concrete.sourceIso.symm.ends.injective
  rw [concrete.sourceIso.symm.wiring]
  rfl
theorem actual_old_argument_finish : concrete.site.net.wire (.inr (.inr (.inl argumentOutside,true)))=
    .inl ⟨.inl argKept,.inl ()⟩ := by
  apply concrete.sourceIso.symm.ends.injective
  rw [concrete.sourceIso.symm.wiring]
  rfl
noncomputable abbrev actualCut := cutFragment concrete.site.net (pathPartition (Schema.beta 0) concrete.Inside) concrete.site.closed

theorem cut_cro_wire : actualCut.wire (.inl ⟨croKept,.inl ()⟩)=.inr (.inr (bindingOutside,true)) := by
  apply concrete.site.outsideEnd_injective
  exact (concrete.site.outsideEnd_wire _).symm.trans actual_old_cro_wire
theorem cut_binding_wire : actualCut.wire (.inr (.inr (bindingOutside,false)))=
    .inr (.inl (.inr (.inr false))) := by
  apply concrete.site.outsideEnd_injective
  exact (concrete.site.outsideEnd_wire _).symm.trans actual_old_binding_wire
theorem cut_argument_wire : actualCut.wire (.inr (.inl (.inr (.inl true))))=
    .inr (.inr (argumentOutside,false)) := by
  apply concrete.site.outsideEnd_injective
  exact (concrete.site.outsideEnd_wire _).symm.trans actual_old_argument_wire
theorem cut_argument_finish : actualCut.wire (.inr (.inr (argumentOutside,true)))=
    .inl ⟨argKept,.inl ()⟩ := by
  apply concrete.site.outsideEnd_injective
  exact (concrete.site.outsideEnd_wire _).symm.trans actual_old_argument_finish
noncomputable def rhsCro : concrete.Kept⊕Empty := .inl croKept
noncomputable def rhsLambda : concrete.Kept⊕Empty := .inl argKept
noncomputable def bindingStep : Endpoint concrete.site.reduce := .inr (.inr (.inl (.inl bindingOutside),false))
noncomputable def bindFront : Endpoint concrete.site.reduce := .inr (.inr (.inr (.inr false),true))
noncomputable def argFront : Endpoint concrete.site.reduce := .inr (.inr (.inr (.inl true),false))
noncomputable def argStep : Endpoint concrete.site.reduce := .inr (.inr (.inl (.inl argumentOutside),true))
theorem after_beta_cro_wire : concrete.site.reduce.wire croPrincipal=
    .inr (.inr (.inl (.inl bindingOutside),true)) := by
  exact (plugLeft_wire actualCut (Schema.beta 0).right.net (.inl ⟨croKept,.inl ()⟩)).trans
    (congrArg (AG.plugLeft actualCut (Schema.beta 0).right.net) cut_cro_wire)
theorem after_beta_binding_wire : concrete.site.reduce.wire bindingStep=
    .inr (.inr (.inr (.inr false),false)) := by
  exact (plugLeft_wire actualCut (Schema.beta 0).right.net (.inr (.inr (bindingOutside,false)))).trans
    (congrArg (AG.plugLeft actualCut (Schema.beta 0).right.net) cut_binding_wire)
theorem after_beta_glue_wire : concrete.site.reduce.wire bindFront=
    .inr (.inr (.inr (.inl true),true)) := rfl
theorem after_beta_arg_wire : concrete.site.reduce.wire argFront=
    .inr (.inr (.inl (.inl argumentOutside),false)) := by
  exact (plugLeft_wire actualCut (Schema.beta 0).right.net (.inr (.inl (.inr (.inl true))))).trans
    (congrArg (AG.plugLeft actualCut (Schema.beta 0).right.net) cut_argument_wire)
theorem after_beta_arg_finish : concrete.site.reduce.wire argStep=
    .inl ⟨rhsLambda,.inl ()⟩ := by
  exact (plugLeft_wire actualCut (Schema.beta 0).right.net (.inr (.inr (argumentOutside,true)))).trans
    (congrArg (AG.plugLeft actualCut (Schema.beta 0).right.net) cut_argument_finish)
noncomputable def actualCroLambdaCorridor : TransparentCorridor concrete.site.reduce where
  first := ⟨rhsCro,.inl ()⟩
  last := ⟨rhsLambda,.inl ()⟩
  edges := [croPrincipal,bindingStep,bindFront,argFront,argStep]
  start := rfl
  finish := by
    have h:=congrArg concrete.site.reduce.wire after_beta_arg_finish
    simp only [Pairing.involutive] at h
    exact congrArg some h
  transparent := by
    intro e f member
    simp only [List.tail_cons,List.zip_cons_cons,List.zip_nil_right,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h|h|h|h
    · cases h;exact ⟨.inl (.inl bindingOutside),true,after_beta_cro_wire,rfl⟩
    · cases h;exact ⟨.inr (.inr false),false,after_beta_binding_wire,rfl⟩
    · cases h;exact ⟨.inr (.inl true),true,after_beta_glue_wire,rfl⟩
    · cases h;exact ⟨.inl (.inl argumentOutside),false,after_beta_arg_wire,rfl⟩

#print axioms actualCroLambdaCorridor

noncomputable def croLambda := PhysicalCorridorPresentation.of_corridor concrete.site.reduce
  (.croAction .lam 0 1 (by decide)) actualCroLambdaCorridor rhsCro rhsLambda
  (by intro h;have same:=congrArg Subtype.val (Sum.inl.inj h);cases same)
  rfl rfl (.inl ()) (.inl ()) HEq.rfl HEq.rfl rfl rfl
theorem actual_two_step_trace : GraphTrace (ActualNet.initial term)
    (ActualNet.ofNet croLambda.site.reduce) [.beta 0,.croAction .lam 0 1 (by decide)] :=
  .cons concrete.graph_step (.cons croLambda.graph_step (.refl _))
#print axioms actual_two_step_trace

abbrev original := WrappedSuccessfulChains.original
abbrev current := WrappedSuccessfulChains.current
def endpoint : Marked := .app [] (.lam (.app [] (.var 0) (.lam (.var 0)))) (.lam (.var 0))
theorem relative : Marked.RelativeHistory [[.fn]]
    (Marked.mark (concrete.site.betaSyntaxFiber (.inl ()) term) term) endpoint := by
  rw [actual_fiber]
  exact .cons (.appL (.root _ _ _)) (.nil _)
theorem beta_matches : Matches concrete.site.reduce (.inl ()) current.erase := by
  obtain ⟨flow⟩ := encode_flowBalance term 0
  obtain ⟨balance⟩ := encode_indexed_balance term 0
  exact concrete.site.beta_complete_matches WrappedSuccessfulChains.initial closed
    (concrete.sourceIso.matches (encode_closed_matches term closed 0))
    (concrete.sourceIso.rootInputs (encode_closed_independence term closed 0).rootInputs)
    (concrete.sourceIso.flowBalance flow) rfl
    (concrete.sourceIso.indexed_balance balance) rfl
    (concrete.sourceIso.transparency (encode_closed_transparency term closed 0))
    relative (by simp [endpoint,Marked.Normal]) WrappedSuccessfulChains.actualHistory
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

def varKept2 : croLambda.Kept := ⟨.inl varKept,by
  constructor
  · intro h;have hs:=congrArg Subtype.val (Sum.inl.inj h);cases hs
  · intro h;have hs:=congrArg Subtype.val (Sum.inl.inj h);cases hs⟩
def argBindingOutside2 : croLambda.Outside := ⟨.inl (.inl argBindingOutside),by
  rintro ⟨d,h⟩
  simp only [actualCroLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h <;> cases h⟩
def argVariableOutside2 : croLambda.Outside := ⟨.inl (.inl argVariableOutside),by
  rintro ⟨d,h⟩
  simp only [actualCroLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h <;> cases h⟩
noncomputable abbrev cut2 : Net signature croLambda.Kept (Boundary term⊕(Unit⊕Bool)) croLambda.Outside := cutFragment croLambda.site.net
  (pathPartition (Schema.croAction .lam 0 1 (by decide)) croLambda.Inside) croLambda.site.closed
theorem outside2_injective : Function.Injective croLambda.site.outsideEnd := by
  intro e f same
  let split := fragmentEnd (B:=Boundary term) (W:=croLambda.Outside) croLambda.site.net.label
    (pathPartition (Schema.croAction .lam 0 1 (by decide)) croLambda.Inside)
  change split.invFun (.inl e)=split.invFun (.inl f) at same
  have mapped:=congrArg split same
  simpa only [split.right_inv,Sum.inl.injEq] using mapped
theorem action2_lift_wire (e f : Endpoint cut2)
    (h : concrete.site.reduce.wire (croLambda.sourceIso.symm.ends (croLambda.site.outsideEnd e))=
      croLambda.sourceIso.symm.ends (croLambda.site.outsideEnd f)) :
    croLambda.site.reduce.wire (AG.plugLeft cut2 (Schema.croAction .lam 0 1 (by decide)).right.net e)=
      AG.plugLeft cut2 (Schema.croAction .lam 0 1 (by decide)).right.net f := by
  have old : croLambda.site.net.wire (croLambda.site.outsideEnd e)=croLambda.site.outsideEnd f := by
    apply croLambda.sourceIso.symm.ends.injective
    rw [croLambda.sourceIso.symm.wiring]
    exact h
  have cut : cut2.wire e=f := outside2_injective
    ((croLambda.site.outsideEnd_wire e).symm.trans old)
  exact (plugLeft_wire cut2 (Schema.croAction .lam 0 1 (by decide)).right.net e).trans
    (congrArg (AG.plugLeft cut2 (Schema.croAction .lam 0 1 (by decide)).right.net) cut)

noncomputable def lowBinding : croLambda.Kept⊕(Unit⊕Bool) := .inr (.inr false)
noncomputable def passiveVar : croLambda.Kept⊕(Unit⊕Bool) := .inl varKept2
noncomputable def lowPrincipal : Endpoint croLambda.site.reduce := .inl ⟨lowBinding,.inl ()⟩
noncomputable def lowGlue : Endpoint croLambda.site.reduce := .inr (.inr (.inr (.inr false),false))
noncomputable def lowStep1 : Endpoint croLambda.site.reduce := .inr (.inr (.inl (.inl argBindingOutside2),true))
noncomputable def lowStep2 : Endpoint croLambda.site.reduce := .inr (.inr (.inl (.inl argVariableOutside2),true))
theorem low_start : croLambda.site.reduce.wire lowPrincipal=
    .inr (.inr (.inr (.inr false),true)) := rfl
theorem low_glue : croLambda.site.reduce.wire lowGlue=
    .inr (.inr (.inl (.inl argBindingOutside2),false)) :=
  action2_lift_wire (.inr (.inl (.inr (.inr false))))
    (.inr (.inr (argBindingOutside2,false))) beta_arg_bind_start
theorem low_transit : croLambda.site.reduce.wire lowStep1=
    .inr (.inr (.inl (.inl argVariableOutside2),false)) :=
  action2_lift_wire (.inr (.inr (argBindingOutside2,true)))
    (.inr (.inr (argVariableOutside2,false))) beta_arg_bind_transit
theorem low_finish : croLambda.site.reduce.wire lowStep2=.inl ⟨passiveVar,.inl ()⟩ :=
  action2_lift_wire (.inr (.inr (argVariableOutside2,true)))
    (.inl ⟨varKept2,.inl ()⟩) beta_arg_var_finish
noncomputable def actualCroCroCorridor : TransparentCorridor croLambda.site.reduce where
  first := ⟨lowBinding,.inl ()⟩
  last := ⟨passiveVar,.inl ()⟩
  edges := [lowPrincipal,lowGlue,lowStep1,lowStep2]
  start := rfl
  finish := by
    have h:=congrArg croLambda.site.reduce.wire low_finish
    simp only [Pairing.involutive] at h
    exact congrArg some h
  transparent := by
    intro e f member
    simp only [List.tail_cons,List.zip_cons_cons,List.zip_nil_right,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h|h|h
    · cases h;exact ⟨.inr (.inr false),true,low_start,rfl⟩
    · cases h;exact ⟨.inl (.inl argBindingOutside2),false,low_glue,rfl⟩
    · cases h;exact ⟨.inl (.inl argVariableOutside2),false,low_transit,rfl⟩
noncomputable def croCro := PhysicalCorridorPresentation.of_corridor croLambda.site.reduce
  (.croAction .cro 0 1 (by decide)) actualCroCroCorridor lowBinding passiveVar
  (by intro h;cases h) rfl rfl (.inl ()) (.inl ()) HEq.rfl HEq.rfl rfl rfl
#print axioms actualCroCroCorridor

def originalBodyApp : (encode 1 argument).N := .inr (.inl (.inl ()))
def oldBodyApp : (encode 0 term).N := .inr (.inl (.inr (.inr originalBodyApp)))
def appKept : concrete.Kept := ⟨oldBodyApp,by constructor <;> intro h <;> cases h⟩
def argFnWire : (encode 0 term).W := wrapArgWire (.inl (.inr (.inr (.inl (.inl ())))))
theorem arg_var_aux : net.wire (.inl ⟨oldArgVar,.inr ()⟩)=.inr (.inr (argFnWire,true)) := rfl
theorem arg_app_fn : net.wire (.inr (.inr (argFnWire,false)))=.inl ⟨oldBodyApp,.inl ()⟩ := rfl
def argFnOutside : concrete.Outside := ⟨argFnWire,by
  rintro ⟨d,h⟩;simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h <;> cases h⟩
theorem beta_var_aux : concrete.site.reduce.wire (.inl ⟨.inl varKept,.inr ()⟩)=
    .inr (.inr (.inl (.inl argFnOutside),true)) :=
  beta_lift_wire (.inl ⟨varKept,.inr ()⟩) (.inr (.inr (argFnOutside,true))) arg_var_aux
theorem beta_app_fn : concrete.site.reduce.wire (.inr (.inr (.inl (.inl argFnOutside),false)))=
    .inl ⟨.inl appKept,.inl ()⟩ :=
  beta_lift_wire (.inr (.inr (argFnOutside,false))) (.inl ⟨appKept,.inl ()⟩) arg_app_fn
def appKept2 : croLambda.Kept := ⟨.inl appKept,by
  constructor <;> intro h <;> have hs:=congrArg Subtype.val (Sum.inl.inj h) <;> cases hs⟩
def argFnOutside2 : croLambda.Outside := ⟨.inl (.inl argFnOutside),by
  rintro ⟨d,h⟩
  simp only [actualCroLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h <;> cases h⟩
theorem lambda_var_aux : croLambda.site.reduce.wire (.inl ⟨passiveVar,.inr ()⟩)=
    .inr (.inr (.inl (.inl argFnOutside2),true)) :=
  action2_lift_wire (.inl ⟨varKept2,.inr ()⟩) (.inr (.inr (argFnOutside2,true))) beta_var_aux
theorem lambda_app_fn : croLambda.site.reduce.wire (.inr (.inr (.inl (.inl argFnOutside2),false)))=
    .inl ⟨.inl appKept2,.inl ()⟩ :=
  action2_lift_wire (.inr (.inr (argFnOutside2,false))) (.inl ⟨appKept2,.inl ()⟩) beta_app_fn

def appKept3 : croCro.Kept := ⟨.inl appKept2,by constructor <;> intro h <;> cases h⟩
def argFnOutside3 : croCro.Outside := ⟨.inl (.inl argFnOutside2),by
  rintro ⟨d,h⟩
  simp only [actualCroCroCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h <;> cases h⟩
noncomputable abbrev cut3 : Net signature croCro.Kept (Boundary term⊕(Unit⊕Unit)) croCro.Outside :=
  cutFragment croCro.site.net (pathPartition (Schema.croAction .cro 0 1 (by decide)) croCro.Inside) croCro.site.closed
theorem outside3_injective : Function.Injective croCro.site.outsideEnd := by
  intro e f same
  let split := fragmentEnd (B:=Boundary term) (W:=croCro.Outside) croCro.site.net.label
    (pathPartition (Schema.croAction .cro 0 1 (by decide)) croCro.Inside)
  change split.invFun (.inl e)=split.invFun (.inl f) at same
  have mapped:=congrArg split same
  simpa only [split.right_inv,Sum.inl.injEq] using mapped
theorem action3_lift_wire (e f : Endpoint cut3)
    (h : croLambda.site.reduce.wire (croCro.sourceIso.symm.ends (croCro.site.outsideEnd e))=
      croCro.sourceIso.symm.ends (croCro.site.outsideEnd f)) :
    croCro.site.reduce.wire (AG.plugLeft cut3 (Schema.croAction .cro 0 1 (by decide)).right.net e)=
      AG.plugLeft cut3 (Schema.croAction .cro 0 1 (by decide)).right.net f := by
  have old : croCro.site.net.wire (croCro.site.outsideEnd e)=croCro.site.outsideEnd f := by
    apply croCro.sourceIso.symm.ends.injective
    rw [croCro.sourceIso.symm.wiring];exact h
  have cut : cut3.wire e=f := outside3_injective ((croCro.site.outsideEnd_wire e).symm.trans old)
  exact (plugLeft_wire cut3 (Schema.croAction .cro 0 1 (by decide)).right.net e).trans
    (congrArg (AG.plugLeft cut3 (Schema.croAction .cro 0 1 (by decide)).right.net) cut)
noncomputable def lowFunction : croCro.Kept⊕(Unit⊕Unit) := .inr (.inr ())
noncomputable def passiveApp : croCro.Kept⊕(Unit⊕Unit) := .inl appKept3
noncomputable def functionPrincipal : Endpoint croCro.site.reduce := .inl ⟨lowFunction,.inl ()⟩
noncomputable def functionGlue : Endpoint croCro.site.reduce := .inr (.inr (.inr (.inr ()),false))
noncomputable def functionStep : Endpoint croCro.site.reduce := .inr (.inr (.inl (.inl argFnOutside3),false))
theorem function_start : croCro.site.reduce.wire functionPrincipal=
    .inr (.inr (.inr (.inr ()),true)) := rfl
theorem function_glue : croCro.site.reduce.wire functionGlue=
    .inr (.inr (.inl (.inl argFnOutside3),true)) :=
  action3_lift_wire (.inr (.inl (.inr (.inr ()))))
    (.inr (.inr (argFnOutside3,true))) lambda_var_aux
theorem function_finish : croCro.site.reduce.wire functionStep=.inl ⟨passiveApp,.inl ()⟩ :=
  action3_lift_wire (.inr (.inr (argFnOutside3,false))) (.inl ⟨appKept3,.inl ()⟩) lambda_app_fn
noncomputable def actualCroAppCorridor : TransparentCorridor croCro.site.reduce where
  first := ⟨lowFunction,.inl ()⟩
  last := ⟨passiveApp,.inl ()⟩
  edges := [functionPrincipal,functionGlue,functionStep]
  start := rfl
  finish := by
    have h:=congrArg croCro.site.reduce.wire function_finish
    simp only [Pairing.involutive] at h
    exact congrArg some h
  transparent := by
    intro e f member
    simp only [List.tail_cons,List.zip_cons_cons,List.zip_nil_right,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h|h
    · cases h;exact ⟨.inr (.inr ()),true,function_start,rfl⟩
    · cases h;exact ⟨.inl (.inl argFnOutside3),true,function_glue,rfl⟩
noncomputable def croApp := PhysicalCorridorPresentation.of_corridor croCro.site.reduce
  (.croAction .app 0 1 (by decide)) actualCroAppCorridor lowFunction passiveApp
  (by intro h;cases h) rfl rfl (.inl ()) (.inl ()) HEq.rfl HEq.rfl rfl rfl
theorem actual_four_step_trace : GraphTrace (ActualNet.initial term) (ActualNet.ofNet croApp.site.reduce)
    [.beta 0,.croAction .lam 0 1 (by decide),.croAction .cro 0 1 (by decide),.croAction .app 0 1 (by decide)] :=
  .cons concrete.graph_step (.cons croLambda.graph_step (.cons croCro.graph_step (.cons croApp.graph_step (.refl _))))
#print axioms actualCroAppCorridor
#print axioms actual_four_step_trace

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
theorem lambda_certified : Certified (ActualNet.ofNet croLambda.site.reduce) :=
  action_certified croLambda.graph_step (.cro .lam 0 1 (by decide)) beta_certified
theorem cro_certified : Certified (ActualNet.ofNet croCro.site.reduce) :=
  action_certified croCro.graph_step (.cro .cro 0 1 (by decide)) lambda_certified
theorem app_certified : Certified (ActualNet.ofNet croApp.site.reduce) :=
  action_certified croApp.graph_step (.cro .app 0 1 (by decide)) cro_certified
theorem actual_final_matches : Matches croApp.site.reduce (.inl ()) current.erase := by
  obtain ⟨_,_,_,_,matching⟩ := app_certified
  exact matching
#print axioms actual_final_matches
end Lamping.Checks.FunctionWrappedReachable
