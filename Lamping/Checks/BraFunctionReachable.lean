import Lamping.Checks.OldChainBetaFixture
import Lamping.Lamping.ActionMatching
import Lamping.Lamping.GraphRootInputPreservation
import Lamping.Lamping.ReachableTransparency
import Lamping.Checks.BraSuccessfulChains

namespace Lamping.Checks.BraFunctionReachable
open AG Graph Lambda Lambda.Labelled
abbrev argument : Term := .lam (.app (.var 0) identity)
abbrev function : Term := .lam (.app identity (.var 0))
abbrev term : Term := .app function argument
abbrev net := (encode 0 term).net
def app : (encode 0 term).N := .inl (.inl ())
def lam : (encode 0 term).N := .inr (.inl (.inl ()))
def principalWire : (encode 0 term).W := .inr (.inl (.inl ()))
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
noncomputable def concrete := PhysicalCorridorPresentation.of_corridor net (.beta 0) corridor app lam
  (by intro h;cases h) rfl rfl (.inl ()) (.inl ()) HEq.rfl HEq.rfl rfl rfl
theorem actual_beta_step : GraphStep (.beta 0) (ActualNet.initial term)
    (ActualNet.ofNet concrete.site.reduce) := concrete.graph_step

def parent : RootAccess net (.inl ()) :=
  ⟨[.inr (.inl (.inl ()))],⟨⟨⟨Context.empty,Context.empty,.single _ _⟩,.single _⟩,rfl,⟨.app,rfl⟩⟩⟩
theorem principalLabels (a : Context) : Labelling net corridor.edges a a :=
  .cons (LabelledTurn.transparent (g:=net) principalWire false a) (.single _ _)
theorem principalForward : Forward net corridor.edges :=
  .transparent principalWire false rfl rfl (.single _)
def childEdges : List (Endpoint net) := [.inr (.inl (.inl ())),.inl ⟨app,.inl ()⟩,.inr (.inr (principalWire,true))]
def child : RootAccess net (.inl ()) :=
  ⟨childEdges,⟨⟨⟨Context.empty,Context.empty,
    .cons (LabelledTurn.node (g:=net) app appCtx (.inl ()) (.direct (.appFun _))) (principalLabels _)⟩,
    .node app appCtx (.inl ()) rfl rfl ⟨rfl,Or.inl rfl⟩ principalForward⟩,rfl,⟨.lam,rfl⟩⟩⟩
def redex : RedexOcc term := ⟨[],_,rfl,True.intro⟩
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
theorem closed : Closed term := by
  change ((0<2) ∧ (0<1)) ∧ ((0<1) ∧ (0<2))
  decide
theorem actual_root_member : []∈physicalBetaFiberPaths net (.inl ()) term app lam :=
  (mem_physicalBetaFiberPaths net (.inl ()) term app lam []).mpr ⟨redex,rich,rfl,rfl,rfl⟩

def oldBra : (encode 0 term).N := .inr (.inl (.inr (.inl (.inr (.inl ⟨0,rfl⟩)))))
def oldArgLam : (encode 0 term).N := .inr (.inr (.inl ()))
def braKept : concrete.Kept := ⟨oldBra,by constructor <;> intro h <;> cases h⟩
def argKept : concrete.Kept := ⟨oldArgLam,by constructor <;> intro h <;> cases h⟩
theorem actual_bra_label : concrete.kept braKept=label .bra 0 := rfl
theorem actual_arg_label : concrete.kept argKept=label .lam 1 := rfl
def bindingWire : (encode 0 term).W := .inl (.inr (.inl (.inr (.inr ⟨0,Or.inr rfl⟩))))
def argumentWire : (encode 0 term).W := .inr (.inr (.inl ()))
theorem old_bra_wire : net.wire (.inl ⟨oldBra,.inl ()⟩)=.inr (.inr (bindingWire,true)) := rfl
theorem old_binding_wire : net.wire (.inr (.inr (bindingWire,false)))=.inl ⟨lam,lamBind⟩ := rfl
#print axioms actual_beta_step
#print axioms actual_bra_label

abbrev original := BraSuccessfulChains.original
abbrev current := BraSuccessfulChains.current
theorem actual_fiber : concrete.site.betaSyntaxFiber (.inl ()) term=[[]] := by
  have sourceMatches : Matches net (.inl ()) original.erase := encode_closed_matches term closed 0
  have matching := concrete.sourceIso.matches sourceMatches
  obtain ⟨sourceSelection,initialJoint⟩ := encode_initial_joint_realization original closed BraSuccessfulChains.initial 0
  obtain ⟨targetSelection⟩ := matching.occurrence_fragment_selection closed
  have joint := (concrete.sourceIso.joint_representation sourceMatches closed sourceSelection targetSelection).mpr initialJoint
  have member : []∈concrete.site.betaSyntaxFiber (.inl ()) term := by
    rw [concrete.betaSyntaxFiber_eq];exact actual_root_member
  let other : RedexOcc term := ⟨[.fn,.body],_,rfl,True.intro⟩
  have absent : [.fn,.body]∉concrete.site.betaSyntaxFiber (.inl ()) term := by
    intro occurs
    have degrees := (concrete.site.beta_fiber_iff_degree (current:=original) closed matching targetSelection joint.1
      redex member other).mp occurs
    change some (Label.atom 3)=some (Label.atom 1) at degrees
    cases degrees
  let test := physicalBetaTest concrete.site.net (.inl ()) term (.inr (.inl ())) (.inr (.inr ()))
  have yes : test []=true := by
    change []∈([[],[.fn,.body]] : List Path).filter test at member
    exact (List.mem_filter.mp member).2
  have no : test [.fn,.body]=false := by
    cases decision : test [.fn,.body] with
    | false => rfl
    | true =>
      apply False.elim;apply absent
      change [.fn,.body]∈([[],[.fn,.body]] : List Path).filter test
      exact List.mem_filter.mpr ⟨by simp,decision⟩
  change ([[],[.fn,.body]] : List Path).filter test=[[]]
  simp [yes,no]
def endpoint : Marked := .app [[.fn,.body]] (.lam (.var 0)) (.lam (.app [] (.var 0) (.lam (.var 0))))
theorem relative : Marked.RelativeHistory [[]]
    (Marked.mark (concrete.site.betaSyntaxFiber (.inl ()) term) term) endpoint := by
  rw [actual_fiber]
  exact .cons (.root _ _ _) (.nil _)
theorem beta_matches : Matches concrete.site.reduce (.inl ()) current.erase := by
  obtain ⟨flow⟩ := encode_flowBalance term 0
  obtain ⟨balance⟩ := encode_indexed_balance term 0
  exact concrete.site.beta_complete_matches BraSuccessfulChains.initial closed
    (concrete.sourceIso.matches (encode_closed_matches term closed 0))
    (concrete.sourceIso.rootInputs (encode_closed_independence term closed 0).rootInputs)
    (concrete.sourceIso.flowBalance flow) rfl (concrete.sourceIso.indexed_balance balance) rfl
    (concrete.sourceIso.transparency (encode_closed_transparency term closed 0))
    relative (by simp [endpoint,Marked.Normal]) BraSuccessfulChains.actualHistory
#print axioms actual_fiber
#print axioms beta_matches
noncomputable def braPrincipal : Endpoint concrete.site.reduce := .inl ⟨.inl braKept,.inl ()⟩
def bindingOutside : concrete.Outside := ⟨bindingWire,by
  rintro ⟨d,h⟩
  simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h <;> cases h⟩
def argumentOutside : concrete.Outside := ⟨argumentWire,by
  rintro ⟨d,h⟩
  simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h <;> cases h⟩
theorem actual_old_bra_wire : concrete.site.net.wire (.inl ⟨.inl braKept,.inl ()⟩)=
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

theorem cut_bra_wire : actualCut.wire (.inl ⟨braKept,.inl ()⟩)=.inr (.inr (bindingOutside,true)) := by
  apply concrete.site.outsideEnd_injective
  exact (concrete.site.outsideEnd_wire _).symm.trans actual_old_bra_wire
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
noncomputable def rhsBra : concrete.Kept⊕Empty := .inl braKept
noncomputable def rhsLambda : concrete.Kept⊕Empty := .inl argKept
noncomputable def bindingStep : Endpoint concrete.site.reduce := .inr (.inr (.inl (.inl bindingOutside),false))
noncomputable def bindFront : Endpoint concrete.site.reduce := .inr (.inr (.inr (.inr false),true))
noncomputable def argFront : Endpoint concrete.site.reduce := .inr (.inr (.inr (.inl true),false))
noncomputable def argStep : Endpoint concrete.site.reduce := .inr (.inr (.inl (.inl argumentOutside),true))
theorem after_beta_bra_wire : concrete.site.reduce.wire braPrincipal=
    .inr (.inr (.inl (.inl bindingOutside),true)) := by
  exact (plugLeft_wire actualCut (Schema.beta 0).right.net (.inl ⟨braKept,.inl ()⟩)).trans
    (congrArg (AG.plugLeft actualCut (Schema.beta 0).right.net) cut_bra_wire)
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
noncomputable def actualBraLambdaCorridor : TransparentCorridor concrete.site.reduce where
  first := ⟨rhsBra,.inl ()⟩
  last := ⟨rhsLambda,.inl ()⟩
  edges := [braPrincipal,bindingStep,bindFront,argFront,argStep]
  start := rfl
  finish := by
    have h:=congrArg concrete.site.reduce.wire after_beta_arg_finish
    simp only [Pairing.involutive] at h
    exact congrArg some h
  transparent := by
    intro e f member
    simp only [List.tail_cons,List.zip_cons_cons,List.zip_nil_right,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h|h|h|h
    · cases h;exact ⟨.inl (.inl bindingOutside),true,after_beta_bra_wire,rfl⟩
    · cases h;exact ⟨.inr (.inr false),false,after_beta_binding_wire,rfl⟩
    · cases h;exact ⟨.inr (.inl true),true,after_beta_glue_wire,rfl⟩
    · cases h;exact ⟨.inl (.inl argumentOutside),false,after_beta_arg_wire,rfl⟩

#print axioms actualBraLambdaCorridor
noncomputable def braLambda := PhysicalCorridorPresentation.of_corridor concrete.site.reduce
  (.braAction .lam 0 1 (by decide)) actualBraLambdaCorridor rhsBra rhsLambda
  (by intro h;have hs:=congrArg Subtype.val (Sum.inl.inj h);cases hs)
  rfl rfl (.inl ()) (.inl ()) HEq.rfl HEq.rfl rfl rfl
def originalArgVar : (encode 1 argument).N := .inr (.inr (.inl ()))
def oldArgVar : (encode 0 term).N := .inr (.inr originalArgVar)
example : net.label oldArgVar=label .cro 1 := rfl
def wrapArgWire (w : (encode 1 argument).W) : (encode 0 term).W :=
  .inl (.inr (.inr w))
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

def varKept2 : braLambda.Kept := ⟨.inl varKept,by
  constructor
  · intro h;have hs:=congrArg Subtype.val (Sum.inl.inj h);cases hs
  · intro h;have hs:=congrArg Subtype.val (Sum.inl.inj h);cases hs⟩
def argBindingOutside2 : braLambda.Outside := ⟨.inl (.inl argBindingOutside),by
  rintro ⟨d,h⟩
  simp only [actualBraLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h <;> cases h⟩
def argVariableOutside2 : braLambda.Outside := ⟨.inl (.inl argVariableOutside),by
  rintro ⟨d,h⟩
  simp only [actualBraLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h <;> cases h⟩
noncomputable abbrev cut2 : Net signature braLambda.Kept (Boundary term⊕(Unit⊕Bool)) braLambda.Outside := cutFragment braLambda.site.net
  (pathPartition (Schema.braAction .lam 0 1 (by decide)) braLambda.Inside) braLambda.site.closed
theorem outside2_injective : Function.Injective braLambda.site.outsideEnd := by
  intro e f same
  let split := fragmentEnd (B:=Boundary term) (W:=braLambda.Outside) braLambda.site.net.label
    (pathPartition (Schema.braAction .lam 0 1 (by decide)) braLambda.Inside)
  change split.invFun (.inl e)=split.invFun (.inl f) at same
  have mapped:=congrArg split same
  simpa only [split.right_inv,Sum.inl.injEq] using mapped
theorem action2_lift_wire (e f : Endpoint cut2)
    (h : concrete.site.reduce.wire (braLambda.sourceIso.symm.ends (braLambda.site.outsideEnd e))=
      braLambda.sourceIso.symm.ends (braLambda.site.outsideEnd f)) :
    braLambda.site.reduce.wire (AG.plugLeft cut2 (Schema.braAction .lam 0 1 (by decide)).right.net e)=
      AG.plugLeft cut2 (Schema.braAction .lam 0 1 (by decide)).right.net f := by
  have old : braLambda.site.net.wire (braLambda.site.outsideEnd e)=braLambda.site.outsideEnd f := by
    apply braLambda.sourceIso.symm.ends.injective
    rw [braLambda.sourceIso.symm.wiring]
    exact h
  have cut : cut2.wire e=f := outside2_injective
    ((braLambda.site.outsideEnd_wire e).symm.trans old)
  exact (plugLeft_wire cut2 (Schema.braAction .lam 0 1 (by decide)).right.net e).trans
    (congrArg (AG.plugLeft cut2 (Schema.braAction .lam 0 1 (by decide)).right.net) cut)

noncomputable def lowBinding : braLambda.Kept⊕(Unit⊕Bool) := .inr (.inr false)
noncomputable def passiveVar : braLambda.Kept⊕(Unit⊕Bool) := .inl varKept2
noncomputable def lowPrincipal : Endpoint braLambda.site.reduce := .inl ⟨lowBinding,.inl ()⟩
noncomputable def lowGlue : Endpoint braLambda.site.reduce := .inr (.inr (.inr (.inr false),false))
noncomputable def lowStep1 : Endpoint braLambda.site.reduce := .inr (.inr (.inl (.inl argBindingOutside2),true))
noncomputable def lowStep2 : Endpoint braLambda.site.reduce := .inr (.inr (.inl (.inl argVariableOutside2),true))
theorem low_start : braLambda.site.reduce.wire lowPrincipal=
    .inr (.inr (.inr (.inr false),true)) := rfl
theorem low_glue : braLambda.site.reduce.wire lowGlue=
    .inr (.inr (.inl (.inl argBindingOutside2),false)) :=
  action2_lift_wire (.inr (.inl (.inr (.inr false))))
    (.inr (.inr (argBindingOutside2,false))) beta_arg_bind_start
theorem low_transit : braLambda.site.reduce.wire lowStep1=
    .inr (.inr (.inl (.inl argVariableOutside2),false)) :=
  action2_lift_wire (.inr (.inr (argBindingOutside2,true)))
    (.inr (.inr (argVariableOutside2,false))) beta_arg_bind_transit
theorem low_finish : braLambda.site.reduce.wire lowStep2=.inl ⟨passiveVar,.inl ()⟩ :=
  action2_lift_wire (.inr (.inr (argVariableOutside2,true)))
    (.inl ⟨varKept2,.inl ()⟩) beta_arg_var_finish
noncomputable def actualBraCroCorridor : TransparentCorridor braLambda.site.reduce where
  first := ⟨lowBinding,.inl ()⟩
  last := ⟨passiveVar,.inl ()⟩
  edges := [lowPrincipal,lowGlue,lowStep1,lowStep2]
  start := rfl
  finish := by
    have h:=congrArg braLambda.site.reduce.wire low_finish
    simp only [Pairing.involutive] at h
    exact congrArg some h
  transparent := by
    intro e f member
    simp only [List.tail_cons,List.zip_cons_cons,List.zip_nil_right,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h|h|h
    · cases h;exact ⟨.inr (.inr false),true,low_start,rfl⟩
    · cases h;exact ⟨.inl (.inl argBindingOutside2),false,low_glue,rfl⟩
    · cases h;exact ⟨.inl (.inl argVariableOutside2),false,low_transit,rfl⟩
noncomputable def braCro := PhysicalCorridorPresentation.of_corridor braLambda.site.reduce
  (.braAction .cro 0 1 (by decide)) actualBraCroCorridor lowBinding passiveVar
  (by intro h;cases h) rfl rfl (.inl ()) (.inl ()) HEq.rfl HEq.rfl rfl rfl

#print axioms actualBraCroCorridor
def originalBodyApp : (encode 1 argument).N := .inr (.inl (.inl ()))
def oldBodyApp : (encode 0 term).N := .inr (.inr originalBodyApp)
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
def appKept2 : braLambda.Kept := ⟨.inl appKept,by
  constructor <;> intro h <;> have hs:=congrArg Subtype.val (Sum.inl.inj h) <;> cases hs⟩
def argFnOutside2 : braLambda.Outside := ⟨.inl (.inl argFnOutside),by
  rintro ⟨d,h⟩
  simp only [actualBraLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h <;> cases h⟩
theorem lambda_var_aux : braLambda.site.reduce.wire (.inl ⟨passiveVar,.inr ()⟩)=
    .inr (.inr (.inl (.inl argFnOutside2),true)) :=
  action2_lift_wire (.inl ⟨varKept2,.inr ()⟩) (.inr (.inr (argFnOutside2,true))) beta_var_aux
theorem lambda_app_fn : braLambda.site.reduce.wire (.inr (.inr (.inl (.inl argFnOutside2),false)))=
    .inl ⟨.inl appKept2,.inl ()⟩ :=
  action2_lift_wire (.inr (.inr (argFnOutside2,false))) (.inl ⟨appKept2,.inl ()⟩) beta_app_fn

def appKept3 : braCro.Kept := ⟨.inl appKept2,by constructor <;> intro h <;> cases h⟩
def argFnOutside3 : braCro.Outside := ⟨.inl (.inl argFnOutside2),by
  rintro ⟨d,h⟩
  simp only [actualBraCroCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h <;> cases h⟩
noncomputable abbrev cut3 : Net signature braCro.Kept (Boundary term⊕(Unit⊕Unit)) braCro.Outside :=
  cutFragment braCro.site.net (pathPartition (Schema.braAction .cro 0 1 (by decide)) braCro.Inside) braCro.site.closed
theorem outside3_injective : Function.Injective braCro.site.outsideEnd := by
  intro e f same
  let split := fragmentEnd (B:=Boundary term) (W:=braCro.Outside) braCro.site.net.label
    (pathPartition (Schema.braAction .cro 0 1 (by decide)) braCro.Inside)
  change split.invFun (.inl e)=split.invFun (.inl f) at same
  have mapped:=congrArg split same
  simpa only [split.right_inv,Sum.inl.injEq] using mapped
theorem action3_lift_wire (e f : Endpoint cut3)
    (h : braLambda.site.reduce.wire (braCro.sourceIso.symm.ends (braCro.site.outsideEnd e))=
      braCro.sourceIso.symm.ends (braCro.site.outsideEnd f)) :
    braCro.site.reduce.wire (AG.plugLeft cut3 (Schema.braAction .cro 0 1 (by decide)).right.net e)=
      AG.plugLeft cut3 (Schema.braAction .cro 0 1 (by decide)).right.net f := by
  have old : braCro.site.net.wire (braCro.site.outsideEnd e)=braCro.site.outsideEnd f := by
    apply braCro.sourceIso.symm.ends.injective
    rw [braCro.sourceIso.symm.wiring];exact h
  have cut : cut3.wire e=f := outside3_injective ((braCro.site.outsideEnd_wire e).symm.trans old)
  exact (plugLeft_wire cut3 (Schema.braAction .cro 0 1 (by decide)).right.net e).trans
    (congrArg (AG.plugLeft cut3 (Schema.braAction .cro 0 1 (by decide)).right.net) cut)
noncomputable def lowFunction : braCro.Kept⊕(Unit⊕Unit) := .inr (.inr ())
noncomputable def passiveApp : braCro.Kept⊕(Unit⊕Unit) := .inl appKept3
noncomputable def functionPrincipal : Endpoint braCro.site.reduce := .inl ⟨lowFunction,.inl ()⟩
noncomputable def functionGlue : Endpoint braCro.site.reduce := .inr (.inr (.inr (.inr ()),false))
noncomputable def functionStep : Endpoint braCro.site.reduce := .inr (.inr (.inl (.inl argFnOutside3),false))
theorem function_start : braCro.site.reduce.wire functionPrincipal=
    .inr (.inr (.inr (.inr ()),true)) := rfl
theorem function_glue : braCro.site.reduce.wire functionGlue=
    .inr (.inr (.inl (.inl argFnOutside3),true)) :=
  action3_lift_wire (.inr (.inl (.inr (.inr ()))))
    (.inr (.inr (argFnOutside3,true))) lambda_var_aux
theorem function_finish : braCro.site.reduce.wire functionStep=.inl ⟨passiveApp,.inl ()⟩ :=
  action3_lift_wire (.inr (.inr (argFnOutside3,false))) (.inl ⟨appKept3,.inl ()⟩) lambda_app_fn
noncomputable def actualBraAppCorridor : TransparentCorridor braCro.site.reduce where
  first := ⟨lowFunction,.inl ()⟩
  last := ⟨passiveApp,.inl ()⟩
  edges := [functionPrincipal,functionGlue,functionStep]
  start := rfl
  finish := by
    have h:=congrArg braCro.site.reduce.wire function_finish
    simp only [Pairing.involutive] at h
    exact congrArg some h
  transparent := by
    intro e f member
    simp only [List.tail_cons,List.zip_cons_cons,List.zip_nil_right,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h|h
    · cases h;exact ⟨.inr (.inr ()),true,function_start,rfl⟩
    · cases h;exact ⟨.inl (.inl argFnOutside3),true,function_glue,rfl⟩
noncomputable def braApp := PhysicalCorridorPresentation.of_corridor braCro.site.reduce
  (.braAction .app 0 1 (by decide)) actualBraAppCorridor lowFunction passiveApp
  (by intro h;cases h) rfl rfl (.inl ()) (.inl ()) HEq.rfl HEq.rfl rfl rfl
theorem actual_four_step_trace : GraphTrace (ActualNet.initial term) (ActualNet.ofNet braApp.site.reduce)
    [.beta 0,.braAction .lam 0 1 (by decide),.braAction .cro 0 1 (by decide),.braAction .app 0 1 (by decide)] :=
  .cons concrete.graph_step (.cons braLambda.graph_step (.cons braCro.graph_step (.cons braApp.graph_step (.refl _))))
#print axioms actualBraAppCorridor
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
theorem lambda_certified : Certified (ActualNet.ofNet braLambda.site.reduce) :=
  action_certified braLambda.graph_step (.bra .lam 0 1 (by decide)) beta_certified
theorem cro_certified : Certified (ActualNet.ofNet braCro.site.reduce) :=
  action_certified braCro.graph_step (.bra .cro 0 1 (by decide)) lambda_certified
theorem app_certified : Certified (ActualNet.ofNet braApp.site.reduce) :=
  action_certified braApp.graph_step (.bra .app 0 1 (by decide)) cro_certified
theorem actual_final_matches : Matches braApp.site.reduce (.inl ()) current.erase := by
  obtain ⟨_,_,_,_,matching⟩ := app_certified
  exact matching
#print axioms actual_final_matches

end Lamping.Checks.BraFunctionReachable
