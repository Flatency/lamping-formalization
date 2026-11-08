/-
A genuine closed INIT -> beta -> fan-lambda instance refutes the additional
historical both-undefined endpoint equivalence retained as LegacyAuxiliarySeparation
specification. All graph sites, labels, Matches, rooted accesses and fragment
heads are constructed. This does not refute the rewrite algorithm or assert
an additional erratum in AG98. The frozen specification is not changed here.
-/
import Lamping.Lamping.CanonicalChildDeparture
import Lamping.Lambda.PrerequisiteUndefined
import Lamping.Lamping.GraphRootInputPreservation
import Lamping.Lamping.ReachableTransparency
import Lamping.Lamping.GraphFlowPreservation
import Lamping.Lamping.GraphIndexedBalance
import Lamping.Lamping.ActionMatching
import Lamping.Checks.OldChainBetaFixture
namespace Lamping.Checks.FanUndefinedReachable
open AG Graph Lambda Lambda.Labelled
abbrev fnBody : Term := .lam (.app (.app (.var 0) (.var 1)) (.var 1))
abbrev fnTerm : Term := .lam fnBody
abbrev argument : Term := identity
abbrev term : Term := .app fnTerm argument
abbrev net := (encode 0 term).net
def app : (encode 0 term).N := .inl (.inl ())
def lam : (encode 0 term).N := .inr (.inl (.inl ()))
def rootWire : (encode 0 term).W := .inr (.inl (.inl ()))
def route : TransparentCorridor net where
  first := ⟨app,.inl ()⟩
  last := ⟨lam,.inl ()⟩
  edges := [.inl ⟨app,.inl ()⟩,.inr (.inr (rootWire,true))]
  start := rfl
  finish := rfl
  transparent := by
    intro e f member
    have same := List.mem_singleton.mp member
    cases same
    exact ⟨rootWire,false,rfl,rfl⟩
theorem presentation_exists : Nonempty (PhysicalCorridorPresentation net (.beta 0) app lam (.inl ()) (.inl ())) :=
  physical_corridor_presentation net (.beta 0) route app lam (by intro same;cases same)
    rfl rfl (.inl ()) (.inl ()) HEq.rfl HEq.rfl rfl rfl

def parent : RootAccess net (.inl ()) :=
  ⟨[.inr (.inl (.inl ()))],⟨⟨⟨Context.empty,Context.empty,.single _ _⟩,.single _⟩,rfl,⟨.app,rfl⟩⟩⟩
theorem principalLabels (a : Context) : Labelling net route.edges a a :=
  .cons (LabelledTurn.transparent (g:=net) rootWire false a) (.single _ _)
theorem principalForward : Forward net route.edges :=
  .transparent rootWire false rfl rfl (.single _)
def childEdges : List (Endpoint net) := [.inr (.inl (.inl ())),.inl ⟨app,.inl ()⟩,.inr (.inr (rootWire,true))]
def child : RootAccess net (.inl ()) :=
  ⟨childEdges,⟨⟨⟨Context.empty,Context.empty,
    .cons (LabelledTurn.node (g:=net) app appCtx (.inl ()) (.direct (.appFun _))) (principalLabels _)⟩,
    .node app appCtx (.inl ()) rfl rfl ⟨rfl,Or.inl rfl⟩ principalForward⟩,rfl,⟨.lam,rfl⟩⟩⟩
def redex : RedexOcc term := ⟨[],_,rfl,True.intro⟩
def rich : ActualRedexAccess net (.inl ()) redex where
  connection := {
    app := app,lam := lam,appPort := .inl (),lamPort := .inl (),appIndex := 0,lamIndex := 0
    appLabel := rfl,lamLabel := rfl,appPrincipal := HEq.rfl,lamPrincipal := HEq.rfl
    edges := route.edges,proper := ⟨⟨Context.empty,Context.empty,principalLabels _⟩,principalForward⟩,start := rfl,finish := rfl,emptyWord := rfl }
  parent := parent
  child := child
  ctx := appCtx
  contextPrincipal := HEq.rfl
  parentWord := rfl
  childWord := rfl
  parentFinish := rfl
  split := rfl
theorem closed : Closed term := by change ((0<2 ∧1<2) ∧1<2) ∧0<1;decide
theorem root_member : []∈physicalBetaFiberPaths net (.inl ()) term app lam :=
  (mem_physicalBetaFiberPaths net (.inl ()) term app lam []).mpr ⟨redex,rich,rfl,rfl,rfl⟩
theorem actual_fiber (presentation : PhysicalCorridorPresentation net (.beta 0) app lam (.inl ()) (.inl ())) :
    presentation.site.betaSyntaxFiber (.inl ()) term=[[]] := by
  rw [presentation.betaSyntaxFiber_eq]
  have member := root_member
  let test := physicalBetaTest net (.inl ()) term app lam
  have yes : test []=true := (List.mem_filter.mp member).2
  change ([[]] : List Path).filter test=[[]]
  simp [yes]
abbrev initial := initLabels term
abbrev result : LTerm := LTerm.contract (.atom 0) (.atom 1)
  (.lam (.atom 2) (.app (.atom 3) (.app (.atom 4) (.var (.atom 5) 0) (.var (.atom 6) 1)) (.var (.atom 7) 1)))
  (.lam (.atom 8) (.var (.atom 9) 0))
def turn : StepAt [] initial result := .root _ _ _ _
def history : History [[]] initial result := .cons turn (.nil _)
def endpoint : Marked := .lam (.app [] (.app [] (.var 0) (.lam (.var 0))) (.lam (.var 0)))
theorem relative (presentation : PhysicalCorridorPresentation net (.beta 0) app lam (.inl ()) (.inl ())) :
    Marked.RelativeHistory [[]] (Marked.mark (presentation.site.betaSyntaxFiber (.inl ()) term) term) endpoint := by
  rw [actual_fiber presentation]
  exact .cons (.root _ _ _) (.nil _)
theorem target_matches (presentation : PhysicalCorridorPresentation net (.beta 0) app lam (.inl ()) (.inl ())) :
    Matches presentation.site.reduce (.inl ()) result.erase := by
  obtain ⟨originalFlow⟩ := encode_flowBalance term 0
  obtain ⟨originalBalance⟩ := encode_indexed_balance term 0
  exact presentation.site.beta_complete_matches (init_is_INIT term) closed
    (presentation.sourceIso.matches (encode_closed_matches term closed 0))
    (presentation.sourceIso.rootInputs (encode_closed_independence term closed 0).rootInputs)
    (presentation.sourceIso.flowBalance originalFlow) rfl
    (presentation.sourceIso.indexed_balance originalBalance) rfl
    (presentation.sourceIso.transparency (encode_closed_transparency term closed 0))
    (relative presentation) (by simp [endpoint,Marked.Normal]) history
#print axioms presentation_exists
#print axioms target_matches
noncomputable def concrete := PhysicalCorridorPresentation.of_corridor net (.beta 0) route app lam
  (by intro same;cases same) rfl rfl (.inl ()) (.inl ()) HEq.rfl HEq.rfl rfl rfl
def sharedInput : Shared (.app (.var 0) (.var 1)) (.var 1) := ⟨⟨1,rfl⟩,Or.inr rfl⟩
def oldFan : (encode 0 term).N := .inr (.inl (.inr (.inr (.inl (.inr (.inr sharedInput))))))
def oldArgLam : (encode 0 term).N := .inr (.inr (.inl ()))
def fanKept : RemainingNodes app lam := ⟨oldFan,by constructor <;> intro h <;> cases h⟩
def argKept : RemainingNodes app lam := ⟨oldArgLam,by constructor <;> intro h <;> cases h⟩
theorem actual_kept_fan_label : concrete.kept fanKept=label .fan 0 := rfl
theorem actual_kept_arg_label : concrete.kept argKept=label .lam 1 := rfl

def bindingWire1 : (encode 0 term).W := .inl (.inr (.inl (.inl (.inr (.inr (.inr ⟨1,Or.inr rfl⟩))))))
def bindingWire2 : (encode 0 term).W := .inl (.inr (.inl (.inr (.inr ⟨0,Or.inr rfl⟩))))
def argumentWire : (encode 0 term).W := .inr (.inr (.inl ()))
theorem old_fan_wire : net.wire (.inl ⟨oldFan,.inl ()⟩)=.inr (.inr (bindingWire1,true)) := rfl
theorem old_binding_transit : net.wire (.inr (.inr (bindingWire1,false)))=.inr (.inr (bindingWire2,true)) := rfl
theorem old_binding_finish : net.wire (.inr (.inr (bindingWire2,false)))=.inl ⟨lam,lamBind⟩ := rfl
def outside1 : concrete.Outside := ⟨bindingWire1,by rintro ⟨d,h⟩;simp only [route,List.mem_cons,List.not_mem_nil,or_false] at h;rcases h with h|h <;> cases h⟩
def outside2 : concrete.Outside := ⟨bindingWire2,by rintro ⟨d,h⟩;simp only [route,List.mem_cons,List.not_mem_nil,or_false] at h;rcases h with h|h <;> cases h⟩
def outsideArg : concrete.Outside := ⟨argumentWire,by rintro ⟨d,h⟩;simp only [route,List.mem_cons,List.not_mem_nil,or_false] at h;rcases h with h|h <;> cases h⟩
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
theorem actual_two_rule_trace : GraphTrace (ActualNet.initial term) (ActualNet.ofNet actualFanPresentation.site.reduce)
    [.beta 0,.fanAction .lam 0 1 (by decide)] :=
  .cons concrete.graph_step (.cons actualFanPresentation.graph_step (.refl _))
#print axioms actual_two_rule_trace
theorem actual_final_matches : Matches actualFanPresentation.site.reduce (.inl ()) result.erase := by
  obtain ⟨flow⟩ := encode_flowBalance term 0
  obtain ⟨balance⟩ := encode_indexed_balance term 0
  have matching := encode_closed_matches term closed 0
  have inputs := (encode_closed_independence term closed 0).rootInputs
  have transparency := encode_closed_transparency term closed 0
  have firstInputs := concrete.graph_step.rootInputs flow rfl balance rfl inputs transparency matching
  have firstT := concrete.graph_step.transparency_indexed flow rfl balance rfl transparency
  obtain ⟨firstFlow⟩ := concrete.graph_step.flowBalance flow
  obtain ⟨firstBalance⟩ := concrete.graph_step.indexed_balance balance
  exact actualFanPresentation.graph_step.action_matches_rootInputs (.fan .lam 0 1 (by decide))
    firstFlow rfl firstBalance rfl firstInputs firstT (target_matches concrete)
#print axioms actual_final_matches
end Lamping.Checks.FanUndefinedReachable
namespace Lamping.Checks.FanUndefinedReachable
open AG Graph Lambda Lambda.Labelled
def oldOuterApp : (encode 0 term).N := .inr (.inl (.inr (.inr (.inl (.inl ())))))
def oldVarRight : (encode 0 term).N := .inr (.inl (.inr (.inr (.inr (.inr ())))))
def oldBraRight : (encode 0 term).N := .inr (.inl (.inr (.inr (.inl (.inr (.inl ⟨1,rfl⟩))))))
theorem original_right_bra_fan : net.wire (.inl ⟨oldBraRight,.inl ()⟩)=.inl ⟨oldFan,.inr true⟩ := rfl
def varRightWire : (encode 0 term).W := .inl (.inr (.inl (.inl (.inr (.inl (.inr (.inr (.inr (.inl ())))))))))
def inputRightWire : (encode 0 term).W := .inl (.inr (.inl (.inl (.inr (.inl (.inr (.inr (.inr (.inr ⟨1,rfl⟩)))))))))
def varRightOutside : concrete.Outside := ⟨varRightWire,by rintro ⟨d,h⟩;simp only [route,List.mem_cons,List.not_mem_nil,or_false] at h;rcases h with h|h <;> cases h⟩
def inputRightOutside : concrete.Outside := ⟨inputRightWire,by rintro ⟨d,h⟩;simp only [route,List.mem_cons,List.not_mem_nil,or_false] at h;rcases h with h|h <;> cases h⟩
def outerAppKept : RemainingNodes app lam := ⟨oldOuterApp,by constructor <;> intro h <;> cases h⟩
def varRightKept : RemainingNodes app lam := ⟨oldVarRight,by constructor <;> intro h <;> cases h⟩
def braRightKept : RemainingNodes app lam := ⟨oldBraRight,by constructor <;> intro h <;> cases h⟩
theorem beta_wire_from_original (e f : Endpoint actualCut)
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
theorem beta_outer_arg : concrete.site.reduce.wire (.inl ⟨.inl outerAppKept,appArg⟩)=
    .inr (.inr (.inl (.inl varRightOutside),false)) :=
  beta_wire_from_original (.inl ⟨outerAppKept,appArg⟩) (.inr (.inr (varRightOutside,false))) rfl
theorem beta_var_aux : concrete.site.reduce.wire (.inr (.inr (.inl (.inl varRightOutside),true)))=
    .inl ⟨.inl varRightKept,.inr ()⟩ :=
  beta_wire_from_original (.inr (.inr (varRightOutside,true))) (.inl ⟨varRightKept,.inr ()⟩) rfl
theorem beta_var_principal : concrete.site.reduce.wire (.inl ⟨.inl varRightKept,.inl ()⟩)=
    .inr (.inr (.inl (.inl inputRightOutside),true)) :=
  beta_wire_from_original (.inl ⟨varRightKept,.inl ()⟩) (.inr (.inr (inputRightOutside,true))) rfl
theorem beta_bra_aux : concrete.site.reduce.wire (.inr (.inr (.inl (.inl inputRightOutside),false)))=
    .inl ⟨.inl braRightKept,.inr ()⟩ :=
  beta_wire_from_original (.inr (.inr (inputRightOutside,false))) (.inl ⟨braRightKept,.inr ()⟩) rfl
theorem beta_bra_fan : concrete.site.reduce.wire (.inl ⟨.inl braRightKept,.inl ()⟩)=
    .inl ⟨rhsFan,.inr true⟩ :=
  beta_wire_from_original (.inl ⟨braRightKept,.inl ()⟩) (.inl ⟨fanKept,.inr true⟩) rfl
noncomputable def finalouterAppKept : actualFanPresentation.Kept := ⟨.inl outerAppKept,by
  constructor <;> intro h <;> have same:=congrArg Subtype.val (Sum.inl.inj h) <;> cases same⟩
noncomputable def finalvarRightKept : actualFanPresentation.Kept := ⟨.inl varRightKept,by
  constructor <;> intro h <;> have same:=congrArg Subtype.val (Sum.inl.inj h) <;> cases same⟩
noncomputable def finalbraRightKept : actualFanPresentation.Kept := ⟨.inl braRightKept,by
  constructor <;> intro h <;> have same:=congrArg Subtype.val (Sum.inl.inj h) <;> cases same⟩
noncomputable def finalvarRightOutside : actualFanPresentation.Outside := ⟨.inl (.inl varRightOutside),by
  rintro ⟨d,h⟩
  simp only [actualFanLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h|h <;> cases h⟩
noncomputable def finalinputRightOutside : actualFanPresentation.Outside := ⟨.inl (.inl inputRightOutside),by
  rintro ⟨d,h⟩
  simp only [actualFanLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h|h <;> cases h⟩
noncomputable abbrev fanCut : Net signature actualFanPresentation.Kept (Boundary term⊕(Bool⊕Bool)) actualFanPresentation.Outside := cutFragment actualFanPresentation.site.net
  (pathPartition (Schema.fanAction .lam 0 1 (by decide)) actualFanPresentation.Inside) actualFanPresentation.site.closed
theorem fan_outside_injective : Function.Injective actualFanPresentation.site.outsideEnd := by
  intro e f same
  let split := fragmentEnd (B:=Boundary term) (W:=actualFanPresentation.Outside) actualFanPresentation.site.net.label
    (pathPartition (Schema.fanAction .lam 0 1 (by decide)) actualFanPresentation.Inside)
  change split.invFun (.inl e)=split.invFun (.inl f) at same
  have mapped := congrArg split same
  simpa only [split.right_inv,Sum.inl.injEq] using mapped
theorem fan_wire_from_beta (e f : Endpoint fanCut)
    (h : concrete.site.reduce.wire (actualFanPresentation.sourceIso.symm.ends (actualFanPresentation.site.outsideEnd e))=
      actualFanPresentation.sourceIso.symm.ends (actualFanPresentation.site.outsideEnd f)) :
    actualFanPresentation.site.reduce.wire (AG.plugLeft fanCut (Schema.fanAction .lam 0 1 (by decide)).right.net e)=
      AG.plugLeft fanCut (Schema.fanAction .lam 0 1 (by decide)).right.net f := by
  have old : actualFanPresentation.site.net.wire (actualFanPresentation.site.outsideEnd e)=actualFanPresentation.site.outsideEnd f := by
    apply actualFanPresentation.sourceIso.symm.ends.injective
    rw [actualFanPresentation.sourceIso.symm.wiring]
    exact h
  have cut : fanCut.wire e=f := fan_outside_injective
    ((actualFanPresentation.site.outsideEnd_wire e).symm.trans old)
  exact (plugLeft_wire fanCut (Schema.fanAction .lam 0 1 (by decide)).right.net e).trans
    (congrArg (AG.plugLeft fanCut (Schema.fanAction .lam 0 1 (by decide)).right.net) cut)
theorem final_outer_arg : actualFanPresentation.site.reduce.wire (.inl ⟨.inl finalouterAppKept,appArg⟩)=
    .inr (.inr (.inl (.inl finalvarRightOutside),false)) :=
  fan_wire_from_beta (.inl ⟨finalouterAppKept,appArg⟩) (.inr (.inr (finalvarRightOutside,false))) beta_outer_arg
theorem final_var_aux : actualFanPresentation.site.reduce.wire (.inr (.inr (.inl (.inl finalvarRightOutside),true)))=
    .inl ⟨.inl finalvarRightKept,.inr ()⟩ :=
  fan_wire_from_beta (.inr (.inr (finalvarRightOutside,true))) (.inl ⟨finalvarRightKept,.inr ()⟩) beta_var_aux
theorem final_var_principal : actualFanPresentation.site.reduce.wire (.inl ⟨.inl finalvarRightKept,.inl ()⟩)=
    .inr (.inr (.inl (.inl finalinputRightOutside),true)) :=
  fan_wire_from_beta (.inl ⟨finalvarRightKept,.inl ()⟩) (.inr (.inr (finalinputRightOutside,true))) beta_var_principal
theorem final_bra_aux : actualFanPresentation.site.reduce.wire (.inr (.inr (.inl (.inl finalinputRightOutside),false)))=
    .inl ⟨.inl finalbraRightKept,.inr ()⟩ :=
  fan_wire_from_beta (.inr (.inr (finalinputRightOutside,false))) (.inl ⟨finalbraRightKept,.inr ()⟩) beta_bra_aux
theorem final_bra_front : actualFanPresentation.site.reduce.wire (.inl ⟨.inl finalbraRightKept,.inl ()⟩)=
    .inr (.inr (.inr (.inl true),false)) :=
  fan_wire_from_beta (.inl ⟨finalbraRightKept,.inl ()⟩) (.inr (.inl (.inr (.inl true)))) beta_bra_fan
noncomputable abbrev finalNet := actualFanPresentation.site.reduce
noncomputable def rightSuffix : List (Endpoint finalNet) :=
  [finalNet.wire (.inl ⟨.inl finalouterAppKept,appCtx⟩),.inl ⟨.inl finalouterAppKept,appArg⟩,
   .inr (.inr (.inl (.inl finalvarRightOutside),true)),.inl ⟨.inl finalvarRightKept,.inl ()⟩,
   .inr (.inr (.inl (.inl finalinputRightOutside),false)),.inl ⟨.inl finalbraRightKept,.inl ()⟩,
   .inr (.inr (.inr (.inl true),true))]
abbrev pairContext := Context.empty.cons (.pair .empty .empty)
theorem rightSuffix_labels : Labelling finalNet rightSuffix Context.empty pairContext := by
  have cro : Traversal 1 (.op .cro) (.inr ()) (.inl ()) Context.empty Context.empty := by
    simpa only [Context.cons_empty,empty_replace_empty] using
      (Traversal.direct (Passage.cro (i:=1) Context.empty Context.empty))
  have bra : Traversal 0 (.op .bra) (.inr ()) (.inl ()) Context.empty pairContext := by
    simpa only [Context.cons_empty,Context.replace_zero] using
      (Traversal.direct (Passage.bra (i:=0) Context.empty Context.empty .empty .empty))
  apply Labelling.cons
  · rw [Pairing.involutive]
    exact LabelledTurn.node (g:=finalNet) (.inl finalouterAppKept) _ _ (.direct (.appArg Context.empty))
  · apply Labelling.cons
    · rw [final_outer_arg];exact LabelledTurn.transparent (g:=finalNet) (.inl (.inl finalvarRightOutside)) false Context.empty
    · apply Labelling.cons
      · rw [final_var_aux];exact LabelledTurn.node (g:=finalNet) (.inl finalvarRightKept) _ _ cro
      · apply Labelling.cons
        · rw [final_var_principal];exact LabelledTurn.transparent (g:=finalNet) (.inl (.inl finalinputRightOutside)) true Context.empty
        · apply Labelling.cons
          · rw [final_bra_aux];exact LabelledTurn.node (g:=finalNet) (.inl finalbraRightKept) _ _ bra
          · apply Labelling.cons
            · rw [final_bra_front];exact LabelledTurn.transparent (g:=finalNet) (.inr (.inl true)) false pairContext
            · exact .single _ _
theorem rightSuffix_finish : rightSuffix.getLast?=some (finalNet.wire (.inl ⟨.inr (.inl true),.inl ()⟩)) := rfl
theorem rightSuffix_word : accessWord finalNet rightSuffix=[Lambda.Step.arg] := rfl
#print axioms rightSuffix_labels
#print axioms rightSuffix_finish
#print axioms rightSuffix_word
end Lamping.Checks.FanUndefinedReachable

set_option maxHeartbeats 4000000
namespace Lamping.Checks.RootFanShared
open AG Graph Lambda Lambda.Labelled FanUndefinedReachable
abbrev outerBody : Term := .app (.app (.var 0) (.var 1)) (.var 1)
def liftRootFnW (w : (encode 0 fnTerm).W) : (encode 0 term).W := .inl (.inr (.inl w))
def liftFBodyW (w : (encode 0 fnBody).W) : (encode 0 fnTerm).W := .inl (.inr w)
def liftXBodyW (w : (encode 0 outerBody).W) : (encode 0 fnBody).W := .inl (.inr w)
def oldX : (encode 0 term).N := .inr (.inl (.inr (.inl ())))
def oldOuter : (encode 0 term).N := .inr (.inl (.inr (.inr (.inl (.inl ())))))
def xRootWire : (encode 0 term).W := liftRootFnW (.inr (.inl ()))
def outerRootWire : (encode 0 term).W := liftRootFnW (liftFBodyW (.inr (.inl ())))
def innerRootWire : (encode 0 term).W := liftRootFnW (liftFBodyW (liftXBodyW (.inr (.inl (.inl ())))))
example : net.wire (.inl ⟨lam,lamBody⟩)=.inr (.inr (xRootWire,false)) := rfl
example : net.wire (.inr (.inr (xRootWire,true)))=.inl ⟨oldX,.inl ()⟩ := rfl
example : net.wire (.inl ⟨oldX,lamBody⟩)=.inr (.inr (outerRootWire,false)) := rfl
example : net.wire (.inr (.inr (outerRootWire,true)))=.inl ⟨oldOuter,appCtx⟩ := rfl
example : net.wire (.inl ⟨oldOuter,.inl ()⟩)=.inr (.inr (innerRootWire,false)) := rfl

def xKept : RemainingNodes app lam := ⟨oldX,by constructor <;> intro h <;> cases h⟩
def outerKept : RemainingNodes app lam := ⟨oldOuter,by constructor <;> intro h <;> cases h⟩
def outsideX : concrete.Outside := ⟨xRootWire,by
  rintro ⟨d,h⟩
  simp only [route,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h <;> cases h⟩
def outsideOuter : concrete.Outside := ⟨outerRootWire,by
  rintro ⟨d,h⟩
  simp only [route,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h <;> cases h⟩
theorem first_cut_wire (e f : Endpoint actualCut)
    (wire : net.wire (concrete.sourceIso.symm.ends (concrete.site.outsideEnd e))=
      concrete.sourceIso.symm.ends (concrete.site.outsideEnd f)) : actualCut.wire e=f := by
  apply concrete.site.outsideEnd_injective
  rw [←concrete.site.outsideEnd_wire]
  apply concrete.sourceIso.symm.ends.injective
  rw [concrete.sourceIso.symm.wiring]
  exact wire

theorem first_root_wire : concrete.site.reduce.wire (.inr (.inl (.inl ())))=
    .inr (.inr (.inr (.inl false),false)) := by
  have c : actualCut.wire (.inr (.inl (.inl (.inl ()))))=.inr (.inl (.inr (.inl false))) :=
    first_cut_wire _ _ rfl
  exact (plugLeft_wire actualCut (Schema.beta 0).right.net _).trans
    (congrArg (AG.plugLeft actualCut (Schema.beta 0).right.net) c)
theorem first_root_glue : concrete.site.reduce.wire (.inr (.inr (.inr (.inl false),true)))=
    .inr (.inr (.inr (.inr true),true)) := rfl
theorem first_body_wire : concrete.site.reduce.wire (.inr (.inr (.inr (.inr true),false)))=
    .inr (.inr (.inl (.inl outsideX),false)) := by
  have c : actualCut.wire (.inr (.inl (.inr (.inr true))))=.inr (.inr (outsideX,false)) :=
    first_cut_wire _ _ rfl
  exact (plugLeft_wire actualCut (Schema.beta 0).right.net _).trans
    (congrArg (AG.plugLeft actualCut (Schema.beta 0).right.net) c)
theorem first_x_finish : concrete.site.reduce.wire (.inr (.inr (.inl (.inl outsideX),true)))=
    .inl ⟨.inl xKept,.inl ()⟩ := by
  have c : actualCut.wire (.inr (.inr (outsideX,true)))=.inl ⟨xKept,.inl ()⟩ :=
    first_cut_wire _ _ rfl
  exact (plugLeft_wire actualCut (Schema.beta 0).right.net _).trans
    (congrArg (AG.plugLeft actualCut (Schema.beta 0).right.net) c)
theorem first_x_body : concrete.site.reduce.wire (.inl ⟨.inl xKept,lamBody⟩)=
    .inr (.inr (.inl (.inl outsideOuter),false)) := by
  have c : actualCut.wire (.inl ⟨xKept,lamBody⟩)=.inr (.inr (outsideOuter,false)) :=
    first_cut_wire _ _ rfl
  exact (plugLeft_wire actualCut (Schema.beta 0).right.net _).trans
    (congrArg (AG.plugLeft actualCut (Schema.beta 0).right.net) c)
theorem first_outer_finish : concrete.site.reduce.wire (.inr (.inr (.inl (.inl outsideOuter),true)))=
    .inl ⟨.inl outerKept,appCtx⟩ := by
  have c : actualCut.wire (.inr (.inr (outsideOuter,true)))=.inl ⟨outerKept,appCtx⟩ :=
    first_cut_wire _ _ rfl
  exact (plugLeft_wire actualCut (Schema.beta 0).right.net _).trans
    (congrArg (AG.plugLeft actualCut (Schema.beta 0).right.net) c)

noncomputable abbrev finalCut := cutFragment actualFanPresentation.site.net
  (pathPartition (Schema.fanAction Op.lam 0 1 (Nat.zero_lt_succ 0)) actualFanPresentation.Inside) actualFanPresentation.site.closed
def xSecond : RemainingNodes rhsFan rhsLambda := ⟨.inl xKept,by
  constructor <;> intro h
  · have same:=congrArg Subtype.val (Sum.inl.inj h);cases same
  · have same:=congrArg Subtype.val (Sum.inl.inj h);cases same⟩
def outerSecond : RemainingNodes rhsFan rhsLambda := ⟨.inl outerKept,by
  constructor <;> intro h
  · have same:=congrArg Subtype.val (Sum.inl.inj h);cases same
  · have same:=congrArg Subtype.val (Sum.inl.inj h);cases same⟩
def finalOutsideCtx : actualFanPresentation.Outside := ⟨.inr (.inl false),by
  rintro ⟨d,h⟩
  simp only [actualFanLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h|h <;> cases h⟩
def finalOutsideBody : actualFanPresentation.Outside := ⟨.inr (.inr true),by
  rintro ⟨d,h⟩
  simp only [actualFanLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h|h <;> cases h⟩
def finalOutsideX : actualFanPresentation.Outside := ⟨.inl (.inl outsideX),by
  rintro ⟨d,h⟩
  simp only [actualFanLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h|h <;> cases h⟩
def finalOutsideOuter : actualFanPresentation.Outside := ⟨.inl (.inl outsideOuter),by
  rintro ⟨d,h⟩
  simp only [actualFanLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h|h <;> cases h⟩
noncomputable abbrev finalNet := actualFanPresentation.site.reduce
noncomputable def finalX : actualFanPresentation.Kept ⊕ (Bool ⊕ Aux .lam) := .inl xSecond
noncomputable def finalOuter : actualFanPresentation.Kept ⊕ (Bool ⊕ Aux .lam) := .inl outerSecond

private theorem final_outside_injective (e f : Endpoint finalCut)
    (same : actualFanPresentation.site.outsideEnd e=actualFanPresentation.site.outsideEnd f) : e=f := by
  let split := fragmentEnd (B:=Boundary term) (W:=actualFanPresentation.Outside) actualFanPresentation.site.net.label
    (pathPartition (Schema.fanAction Op.lam 0 1 (Nat.zero_lt_succ 0)) actualFanPresentation.Inside)
  change split.invFun (.inl e)=split.invFun (.inl f) at same
  have mapped:=congrArg split same
  simpa only [split.right_inv,Sum.inl.injEq] using mapped

theorem second_lift_wire (e f : Endpoint finalCut)
    (wire : concrete.site.reduce.wire (actualFanPresentation.sourceIso.symm.ends (actualFanPresentation.site.outsideEnd e))=
      actualFanPresentation.sourceIso.symm.ends (actualFanPresentation.site.outsideEnd f)) :
    finalNet.wire (AG.plugLeft finalCut (Schema.fanAction Op.lam 0 1 (Nat.zero_lt_succ 0)).right.net e)=
      AG.plugLeft finalCut (Schema.fanAction Op.lam 0 1 (Nat.zero_lt_succ 0)).right.net f := by
  have c : finalCut.wire e=f := by
    apply final_outside_injective
    rw [←actualFanPresentation.site.outsideEnd_wire]
    apply actualFanPresentation.sourceIso.symm.ends.injective
    rw [actualFanPresentation.sourceIso.symm.wiring]
    exact wire
  exact (plugLeft_wire finalCut (Schema.fanAction Op.lam 0 1 (Nat.zero_lt_succ 0)).right.net e).trans
    (congrArg (AG.plugLeft finalCut (Schema.fanAction Op.lam 0 1 (Nat.zero_lt_succ 0)).right.net) c)

theorem final_root_wire : finalNet.wire (.inr (.inl (.inl ())))=
    .inr (.inr (.inl (.inl finalOutsideCtx),false)) :=
  second_lift_wire (.inr (.inl (.inl (.inl ())))) (.inr (.inr (finalOutsideCtx,false))) first_root_wire
theorem final_root_glue : finalNet.wire (.inr (.inr (.inl (.inl finalOutsideCtx),true)))=
    .inr (.inr (.inl (.inl finalOutsideBody),true)) :=
  second_lift_wire (.inr (.inr (finalOutsideCtx,true))) (.inr (.inr (finalOutsideBody,true))) first_root_glue
theorem final_body_wire : finalNet.wire (.inr (.inr (.inl (.inl finalOutsideBody),false)))=
    .inr (.inr (.inl (.inl finalOutsideX),false)) :=
  second_lift_wire (.inr (.inr (finalOutsideBody,false))) (.inr (.inr (finalOutsideX,false))) first_body_wire
theorem final_x_finish : finalNet.wire (.inr (.inr (.inl (.inl finalOutsideX),true)))=
    .inl ⟨finalX,.inl ()⟩ :=
  second_lift_wire (.inr (.inr (finalOutsideX,true))) (.inl ⟨xSecond,.inl ()⟩) first_x_finish
theorem final_x_body : finalNet.wire (.inl ⟨finalX,lamBody⟩)=
    .inr (.inr (.inl (.inl finalOutsideOuter),false)) :=
  second_lift_wire (.inl ⟨xSecond,lamBody⟩) (.inr (.inr (finalOutsideOuter,false))) first_x_body
theorem final_outer_finish : finalNet.wire (.inr (.inr (.inl (.inl finalOutsideOuter),true)))=
    .inl ⟨finalOuter,appCtx⟩ :=
  second_lift_wire (.inr (.inr (finalOutsideOuter,true))) (.inl ⟨outerSecond,appCtx⟩) first_outer_finish

noncomputable def rootLambdaEdges : List (Endpoint finalNet) :=
  [.inr (.inl (.inl ())),.inr (.inr (.inl (.inl finalOutsideCtx),true)),
    .inr (.inr (.inl (.inl finalOutsideBody),false)),.inr (.inr (.inl (.inl finalOutsideX),true))]
noncomputable def outerEdges : List (Endpoint finalNet) := rootLambdaEdges++
  [.inl ⟨finalX,lamBody⟩,.inr (.inr (.inl (.inl finalOutsideOuter),true))]
theorem outerLabels (a : Context) : Labelling finalNet outerEdges a a := by
  apply Labelling.cons (by rw [final_root_wire];exact .transparent _ false a)
  apply Labelling.cons (by rw [final_root_glue];exact .transparent _ true a)
  apply Labelling.cons (by rw [final_body_wire];exact .transparent _ false a)
  apply Labelling.cons (by rw [final_x_finish];exact LabelledTurn.node (g:=finalNet) finalX (Sum.inl ()) lamBody (.direct (.lamBody a)))
  exact .cons (by rw [final_x_body];exact .transparent _ false a) (.single _ a)
theorem outerWord : accessWord finalNet outerEdges=[.body] := rfl
theorem outerFinish : outerEdges.getLast?=some (finalNet.wire (.inl ⟨finalOuter,appCtx⟩)) := by
  have inverse := congrArg finalNet.wire final_outer_finish
  simp only [Pairing.involutive] at inverse
  simpa only [outerEdges,rootLambdaEdges,List.cons_append,List.nil_append,List.getLast?_cons_cons,List.getLast?_singleton] using (congrArg some inverse)
theorem finalFlow : Nonempty (FlowBalance finalNet initialBoundaryPolarity) := by
  obtain ⟨flow⟩ := encode_flowBalance term 0
  obtain ⟨first⟩ := concrete.graph_step.flowBalance flow
  obtain ⟨last⟩ := actualFanPresentation.graph_step.flowBalance first
  exact ⟨last⟩
noncomputable def outerAccess : RootAccess finalNet (.inl ()) := by
  let flow := Classical.choice finalFlow
  exact ⟨outerEdges,⟨⟨⟨Context.empty,Context.empty,outerLabels _⟩,
    (outerLabels Context.empty).root_forward_of_flow flow (.inl ()) rfl rfl⟩,rfl,⟨.app,by
      unfold accessKind
      rw [outerFinish]
      simp only [Option.bind_some,Pairing.involutive]
      rfl⟩⟩⟩
end Lamping.Checks.RootFanShared

namespace Lamping.Checks.FanUndefinedReachable
open AG Graph Lambda Lambda.Labelled
noncomputable def rightEdges : List (Endpoint finalNet) := RootFanShared.outerEdges++rightSuffix.tail
theorem rightLabels : Labelling finalNet rightEdges Context.empty pairContext := by
  have tailLabels : Labelling finalNet rightSuffix.tail Context.empty pairContext := by
    cases rightSuffix_labels with
    | cons turn rest =>
      have reference : LabelledTurn finalNet
          (finalNet.wire (finalNet.wire (.inl ⟨.inl finalouterAppKept,appCtx⟩)))
          (.inl ⟨.inl finalouterAppKept,appArg⟩) Context.empty Context.empty := by
        rw [Pairing.involutive]
        exact LabelledTurn.node (g:=finalNet) (.inl finalouterAppKept) _ _ (.direct (.appArg Context.empty))
      have same := turn.output_unique reference
      rw [same] at rest
      exact rest
  exact (RootFanShared.outerLabels Context.empty).append_seam tailLabels (by
    intro e f atLast atHead
    have eEq:=Option.some.inj (atLast.symm.trans RootFanShared.outerFinish)
    have fEq:=Option.some.inj atHead
    subst e;subst f
    rw [Pairing.involutive]
    exact LabelledTurn.node (g:=finalNet) (.inl finalouterAppKept) _ _ (.direct (.appArg Context.empty)))
theorem rightWord : accessWord finalNet rightEdges=[.body,.arg] := by
  rw [rightEdges,accessWord_append finalNet _ _ (RootFanShared.outerLabels Context.empty).nonempty]
  change accessWord finalNet RootFanShared.outerEdges++accessWord finalNet rightSuffix=_
  rw [RootFanShared.outerWord,rightSuffix_word];rfl
theorem rightFinish : rightEdges.getLast?=some (finalNet.wire (.inl ⟨.inr (.inl true),.inl ()⟩)) := by
  change (RootFanShared.outerEdges++rightSuffix.tail).getLast?=_
  simp only [List.getLast?_append,rightSuffix,List.tail_cons,List.getLast?_cons_cons,List.getLast?_singleton,Option.some_or]
  rfl
noncomputable def rightParent : RootAccess finalNet (.inl ()) := by
  let flow:=Classical.choice RootFanShared.finalFlow
  refine ⟨rightEdges,⟨⟨⟨Context.empty,pairContext,rightLabels⟩,
    rightLabels.root_forward_of_flow flow (.inl ()) rfl rfl⟩,rfl,⟨.lam,?_⟩⟩⟩
  unfold accessKind
  rw [rightFinish]
  simp only [Option.bind_some,Pairing.involutive]
  rfl
#print axioms rightParent
#print axioms rightWord
end Lamping.Checks.FanUndefinedReachable

namespace Lamping.Checks.FanUndefinedReachable
open AG Graph Lambda Lambda.Labelled
theorem right_body_head (selection : OccurrenceFragmentSelection result finalNet (.inl ())) :
    ∃ departure : Port (finalNet.label (.inr (.inl true))).sort,
      (selection ⟨[.body,.arg,.body],rfl⟩).fragment.segments.head?=
        some (.inl ⟨.inr (.inl true),departure⟩) := by
  let chosen := selection ⟨[.body,.arg,.body],rfl⟩
  have actual : SourceSubterm [] .external result [.body,.arg,.body] _ _ _ := .body (.arg (.body .nil))
  obtain ⟨_env,context,_term⟩ := chosen.occurrence.same_occurrence actual
  have fromCtx : (sourceEdge chosen.environment chosen.context chosen.term).fromPort=chosen.context := by
    cases chosen.term <;> rfl
  have role : SourceDeparture (.lam ((Labelled.Label.atom 7).concat ((Labelled.Label.atom 1).under.concat (.atom 8))) chosen.term) .body (sourceEdge chosen.environment chosen.context chosen.term).fromPort := by
    rw [fromCtx,context]
    exact .body
  have word : [.body,.arg,.body]=accessWord finalNet rightParent.val++[.body] := by
    change [.body,.arg,.body]=accessWord finalNet rightEdges++[.body]
    rw [rightWord];rfl
  exact chosen.fragment.head_node_of_parent actual_final_matches role rightParent
    word (.inr (.inl true)) (.inl ()) rightFinish
#print axioms right_body_head
end Lamping.Checks.FanUndefinedReachable

namespace Lamping.Checks.RootFanLeft
open AG Graph Lambda Lambda.Labelled FanUndefinedReachable RootFanShared
abbrev innerBody : Term := .app (.var 0) (.var 1)
def liftOuterFnN (n : (encode 0 innerBody).N) : (encode 0 term).N := .inr (.inl (.inr (.inr (.inr (.inl n)))))
def liftOuterFnW (w : (encode 0 innerBody).W) : (encode 0 outerBody).W := .inl (.inr (.inl w))
def oldInner := liftOuterFnN (.inl (.inl ()))
def oldVar := liftOuterFnN (.inr (.inr ()))
def oldBra := liftOuterFnN (.inl (.inr (.inl ⟨1,rfl⟩)))
def varWire := liftRootFnW (liftFBodyW (liftXBodyW (liftOuterFnW (.inr (.inr (.inl ()))))))
def inputWire := liftRootFnW (liftFBodyW (liftXBodyW (liftOuterFnW (.inr (.inr (.inr ⟨1,rfl⟩))))))
def fanWire := liftRootFnW (liftFBodyW (liftXBodyW (.inr (.inl (.inr ⟨1,Or.inr rfl⟩)))))
def innerKept : RemainingNodes app lam := ⟨oldInner,by constructor <;> intro h <;> cases h⟩
noncomputable def finalInnerKept : actualFanPresentation.Kept := ⟨.inl innerKept,by
  constructor <;> intro h <;> have same:=congrArg Subtype.val (Sum.inl.inj h) <;> cases same⟩
def varKept : RemainingNodes app lam := ⟨oldVar,by constructor <;> intro h <;> cases h⟩
noncomputable def finalVarKept : actualFanPresentation.Kept := ⟨.inl varKept,by
  constructor <;> intro h <;> have same:=congrArg Subtype.val (Sum.inl.inj h) <;> cases same⟩
def braKept : RemainingNodes app lam := ⟨oldBra,by constructor <;> intro h <;> cases h⟩
noncomputable def finalBraKept : actualFanPresentation.Kept := ⟨.inl braKept,by
  constructor <;> intro h <;> have same:=congrArg Subtype.val (Sum.inl.inj h) <;> cases same⟩
def innerOutside : concrete.Outside := ⟨innerRootWire,by
  rintro ⟨d,h⟩
  simp only [route,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h <;> cases h⟩
noncomputable def finalInnerOutside : actualFanPresentation.Outside := ⟨.inl (.inl innerOutside),by
  rintro ⟨d,h⟩
  simp only [actualFanLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h|h <;> cases h⟩
def varOutside : concrete.Outside := ⟨varWire,by
  rintro ⟨d,h⟩
  simp only [route,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h <;> cases h⟩
noncomputable def finalVarOutside : actualFanPresentation.Outside := ⟨.inl (.inl varOutside),by
  rintro ⟨d,h⟩
  simp only [actualFanLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h|h <;> cases h⟩
def inputOutside : concrete.Outside := ⟨inputWire,by
  rintro ⟨d,h⟩
  simp only [route,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h <;> cases h⟩
noncomputable def finalInputOutside : actualFanPresentation.Outside := ⟨.inl (.inl inputOutside),by
  rintro ⟨d,h⟩
  simp only [actualFanLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h|h <;> cases h⟩
def fanOutside : concrete.Outside := ⟨fanWire,by
  rintro ⟨d,h⟩
  simp only [route,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h <;> cases h⟩
noncomputable def finalFanOutside : actualFanPresentation.Outside := ⟨.inl (.inl fanOutside),by
  rintro ⟨d,h⟩
  simp only [actualFanLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h|h <;> cases h⟩
theorem beta_outer_fn : concrete.site.reduce.wire (AG.plugLeft actualCut (Schema.beta 0).right.net (.inl ⟨outerKept,.inl ()⟩))=
    AG.plugLeft actualCut (Schema.beta 0).right.net (.inr (.inr (innerOutside,false))) := beta_wire_from_original _ _ rfl
theorem beta_inner_ctx : concrete.site.reduce.wire (AG.plugLeft actualCut (Schema.beta 0).right.net (.inr (.inr (innerOutside,true))))=
    AG.plugLeft actualCut (Schema.beta 0).right.net (.inl ⟨innerKept,appCtx⟩) := beta_wire_from_original _ _ rfl
theorem beta_inner_arg : concrete.site.reduce.wire (AG.plugLeft actualCut (Schema.beta 0).right.net (.inl ⟨innerKept,appArg⟩))=
    AG.plugLeft actualCut (Schema.beta 0).right.net (.inr (.inr (varOutside,false))) := beta_wire_from_original _ _ rfl
theorem beta_var_aux : concrete.site.reduce.wire (AG.plugLeft actualCut (Schema.beta 0).right.net (.inr (.inr (varOutside,true))))=
    AG.plugLeft actualCut (Schema.beta 0).right.net (.inl ⟨varKept,.inr ()⟩) := beta_wire_from_original _ _ rfl
theorem beta_var_principal : concrete.site.reduce.wire (AG.plugLeft actualCut (Schema.beta 0).right.net (.inl ⟨varKept,.inl ()⟩))=
    AG.plugLeft actualCut (Schema.beta 0).right.net (.inr (.inr (inputOutside,true))) := beta_wire_from_original _ _ rfl
theorem beta_bra_aux : concrete.site.reduce.wire (AG.plugLeft actualCut (Schema.beta 0).right.net (.inr (.inr (inputOutside,false))))=
    AG.plugLeft actualCut (Schema.beta 0).right.net (.inl ⟨braKept,.inr ()⟩) := beta_wire_from_original _ _ rfl
theorem beta_bra_principal : concrete.site.reduce.wire (AG.plugLeft actualCut (Schema.beta 0).right.net (.inl ⟨braKept,.inl ()⟩))=
    AG.plugLeft actualCut (Schema.beta 0).right.net (.inr (.inr (fanOutside,true))) := beta_wire_from_original _ _ rfl
theorem beta_fan_aux : concrete.site.reduce.wire (AG.plugLeft actualCut (Schema.beta 0).right.net (.inr (.inr (fanOutside,false))))=
    AG.plugLeft actualCut (Schema.beta 0).right.net (.inl ⟨fanKept,.inr false⟩) := beta_wire_from_original _ _ rfl
theorem final_outer_fn : RootFanShared.finalNet.wire (AG.plugLeft finalCut (Schema.fanAction .lam 0 1 (by decide)).right.net (.inl ⟨outerSecond,.inl ()⟩))=
    AG.plugLeft finalCut (Schema.fanAction .lam 0 1 (by decide)).right.net (.inr (.inr (finalInnerOutside,false))) :=
  second_lift_wire _ _ beta_outer_fn
theorem final_inner_ctx : RootFanShared.finalNet.wire (AG.plugLeft finalCut (Schema.fanAction .lam 0 1 (by decide)).right.net (.inr (.inr (finalInnerOutside,true))))=
    AG.plugLeft finalCut (Schema.fanAction .lam 0 1 (by decide)).right.net (.inl ⟨finalInnerKept,appCtx⟩) :=
  second_lift_wire _ _ beta_inner_ctx
theorem final_inner_arg : RootFanShared.finalNet.wire (AG.plugLeft finalCut (Schema.fanAction .lam 0 1 (by decide)).right.net (.inl ⟨finalInnerKept,appArg⟩))=
    AG.plugLeft finalCut (Schema.fanAction .lam 0 1 (by decide)).right.net (.inr (.inr (finalVarOutside,false))) :=
  second_lift_wire _ _ beta_inner_arg
theorem final_var_aux : RootFanShared.finalNet.wire (AG.plugLeft finalCut (Schema.fanAction .lam 0 1 (by decide)).right.net (.inr (.inr (finalVarOutside,true))))=
    AG.plugLeft finalCut (Schema.fanAction .lam 0 1 (by decide)).right.net (.inl ⟨finalVarKept,.inr ()⟩) :=
  second_lift_wire _ _ beta_var_aux
theorem final_var_principal : RootFanShared.finalNet.wire (AG.plugLeft finalCut (Schema.fanAction .lam 0 1 (by decide)).right.net (.inl ⟨finalVarKept,.inl ()⟩))=
    AG.plugLeft finalCut (Schema.fanAction .lam 0 1 (by decide)).right.net (.inr (.inr (finalInputOutside,true))) :=
  second_lift_wire _ _ beta_var_principal
theorem final_bra_aux : RootFanShared.finalNet.wire (AG.plugLeft finalCut (Schema.fanAction .lam 0 1 (by decide)).right.net (.inr (.inr (finalInputOutside,false))))=
    AG.plugLeft finalCut (Schema.fanAction .lam 0 1 (by decide)).right.net (.inl ⟨finalBraKept,.inr ()⟩) :=
  second_lift_wire _ _ beta_bra_aux
theorem final_bra_principal : RootFanShared.finalNet.wire (AG.plugLeft finalCut (Schema.fanAction .lam 0 1 (by decide)).right.net (.inl ⟨finalBraKept,.inl ()⟩))=
    AG.plugLeft finalCut (Schema.fanAction .lam 0 1 (by decide)).right.net (.inr (.inr (finalFanOutside,true))) :=
  second_lift_wire _ _ beta_bra_principal
theorem final_fan_aux : RootFanShared.finalNet.wire (AG.plugLeft finalCut (Schema.fanAction .lam 0 1 (by decide)).right.net (.inr (.inr (finalFanOutside,false))))=
    AG.plugLeft finalCut (Schema.fanAction .lam 0 1 (by decide)).right.net (.inr (.inl (.inr (.inl false)))) :=
  second_lift_wire _ _ beta_fan_aux

end Lamping.Checks.RootFanLeft


namespace Lamping.Checks.RootFanLeft
open AG Graph Lambda Lambda.Labelled FanUndefinedReachable RootFanShared
theorem outer_fn_eq : RootFanShared.finalNet.wire (.inl ⟨finalOuter,.inl ()⟩)=(.inr (.inr (.inl (.inl finalInnerOutside),false))) := final_outer_fn
theorem inner_ctx_eq : RootFanShared.finalNet.wire (.inr (.inr (.inl (.inl finalInnerOutside),true)))=(.inl ⟨.inl finalInnerKept,appCtx⟩) := final_inner_ctx
theorem inner_arg_eq : RootFanShared.finalNet.wire (.inl ⟨.inl finalInnerKept,appArg⟩)=(.inr (.inr (.inl (.inl finalVarOutside),false))) := final_inner_arg
theorem var_aux_eq : RootFanShared.finalNet.wire (.inr (.inr (.inl (.inl finalVarOutside),true)))=(.inl ⟨.inl finalVarKept,.inr ()⟩) := final_var_aux
theorem var_principal_eq : RootFanShared.finalNet.wire (.inl ⟨.inl finalVarKept,.inl ()⟩)=(.inr (.inr (.inl (.inl finalInputOutside),true))) := final_var_principal
theorem bra_aux_eq : RootFanShared.finalNet.wire (.inr (.inr (.inl (.inl finalInputOutside),false)))=(.inl ⟨.inl finalBraKept,.inr ()⟩) := final_bra_aux
theorem bra_principal_eq : RootFanShared.finalNet.wire (.inl ⟨.inl finalBraKept,.inl ()⟩)=(.inr (.inr (.inl (.inl finalFanOutside),true))) := final_bra_principal
theorem fan_aux_eq : RootFanShared.finalNet.wire (.inr (.inr (.inl (.inl finalFanOutside),false)))=(.inr (.inr (.inr (.inl false),false))) := final_fan_aux
noncomputable def leftTail : List (Endpoint RootFanShared.finalNet) :=
  [.inl ⟨finalOuter,.inl ()⟩,.inr (.inr (.inl (.inl finalInnerOutside),true)),
   .inl ⟨.inl finalInnerKept,appArg⟩,.inr (.inr (.inl (.inl finalVarOutside),true)),
   .inl ⟨.inl finalVarKept,.inl ()⟩,.inr (.inr (.inl (.inl finalInputOutside),false)),
   .inl ⟨.inl finalBraKept,.inl ()⟩,.inr (.inr (.inl (.inl finalFanOutside),false)),
   .inr (.inr (.inr (.inl false),true))]
theorem leftTailLabels : Labelling RootFanShared.finalNet leftTail Context.empty pairContext := by
  have cro : Traversal 1 (.op .cro) (.inr ()) (.inl ()) Context.empty Context.empty := by
    simpa only [Context.cons_empty,empty_replace_empty] using
      (Traversal.direct (Passage.cro (i:=1) Context.empty Context.empty))
  have bra : Traversal 0 (.op .bra) (.inr ()) (.inl ()) Context.empty pairContext := by
    simpa only [Context.cons_empty,Context.replace_zero] using
      (Traversal.direct (Passage.bra (i:=0) Context.empty Context.empty .empty .empty))
  apply Labelling.cons (by rw [outer_fn_eq];exact .transparent _ false Context.empty)
  apply Labelling.cons (by rw [inner_ctx_eq];exact LabelledTurn.node (g:=RootFanShared.finalNet) (.inl finalInnerKept) _ _ (.direct (.appArg Context.empty)))
  apply Labelling.cons (by rw [inner_arg_eq];exact .transparent _ false Context.empty)
  apply Labelling.cons (by rw [var_aux_eq];exact LabelledTurn.node (g:=RootFanShared.finalNet) (.inl finalVarKept) _ _ cro)
  apply Labelling.cons (by rw [var_principal_eq];exact .transparent _ true Context.empty)
  apply Labelling.cons (by rw [bra_aux_eq];exact LabelledTurn.node (g:=RootFanShared.finalNet) (.inl finalBraKept) _ _ bra)
  apply Labelling.cons (by rw [bra_principal_eq];exact .transparent _ true pairContext)
  exact .cons (by rw [fan_aux_eq];exact .transparent _ false pairContext) (.single _ _)
noncomputable def leftEdges : List (Endpoint RootFanShared.finalNet) := RootFanShared.outerEdges++leftTail
theorem leftLabels : Labelling RootFanShared.finalNet leftEdges Context.empty pairContext :=
  (RootFanShared.outerLabels Context.empty).append_seam leftTailLabels (by
    intro e f atLast atHead
    have eEq := Option.some.inj (atLast.symm.trans RootFanShared.outerFinish)
    have fEq := Option.some.inj atHead
    subst e;subst f
    rw [Pairing.involutive]
    exact LabelledTurn.node (g:=RootFanShared.finalNet) finalOuter _ _ (.direct (.appFun Context.empty)))
theorem leftWord : accessWord RootFanShared.finalNet leftEdges=[.body,.fn,.arg] := by
  rw [leftEdges,accessWord_append RootFanShared.finalNet _ _ (RootFanShared.outerLabels Context.empty).nonempty]
  change accessWord RootFanShared.finalNet RootFanShared.outerEdges++[.fn,.arg]=_
  rw [RootFanShared.outerWord];rfl
theorem leftFinish : leftEdges.getLast?=some (RootFanShared.finalNet.wire (.inl ⟨.inr (.inl false),.inl ()⟩)) := by
  simp only [leftEdges,List.getLast?_append,leftTail,List.getLast?_cons_cons,List.getLast?_singleton,Option.some_or]
  rfl
noncomputable def leftParent : RootAccess RootFanShared.finalNet (.inl ()) := by
  let flow:=Classical.choice RootFanShared.finalFlow
  refine ⟨leftEdges,⟨⟨⟨Context.empty,pairContext,leftLabels⟩,
    leftLabels.root_forward_of_flow flow (.inl ()) rfl rfl⟩,rfl,⟨.lam,?_⟩⟩⟩
  unfold accessKind
  rw [leftFinish]
  simp only [Option.bind_some,Pairing.involutive]
  rfl
#print axioms leftTailLabels
#print axioms leftParent
#print axioms leftWord
end Lamping.Checks.RootFanLeft

namespace Lamping.Checks.NormalAuxiliaryCandidate
open AG Graph Lambda Lambda.Labelled
abbrev identity : Term := .lam (.var 0)
abbrev bare : Term := .app (.lam (.lam (.app (.app (.var 0) (.var 1)) (.var 1)))) identity
abbrev original : LTerm := initLabels bare
abbrev current : LTerm := match original with
  | .app b (.lam a body) arg => LTerm.contract b a body arg
  | t => t
def actualStep : StepAt [] original current := .root _ _ _ _
def actualHistory : History [[]] original current := .cons actualStep (.nil _)
theorem closed : Closed current.erase := actualHistory.closed (by change ((0<2 ∧ 1<2) ∧1<2) ∧0<1;decide)
def left : Path := [.body,.fn,.arg,.body]
def right : Path := [.body,.arg,.body]
theorem noRedex : redexPositions current.erase=[] := rfl

theorem noChain (p : Path) : NoPrerequisite current p := by
  rintro ⟨es,chain⟩
  obtain ⟨edge,_last,parent,appStamp,lamStamp,body,arg,_split,lookup⟩ := chain.last_redex
  have bareLookup : subtermAt current.erase parent=some (.app (.lam body.erase) arg.erase) := by
    rw [←LTerm.erase_subterm,lookup];rfl
  have member := (mem_redexPositions current.erase parent).mpr ⟨_,bareLookup,True.intro⟩
  rw [noRedex] at member
  cases member

theorem noEndpointChain (v : SyntaxIncidence.Vertex current) : ¬∃es,EndpointChain current v es := by
  cases v with
  | none => rintro ⟨es,chain⟩;exact chain
  | some p => exact noChain p.val

theorem allPartial (l r : SyntaxIncidence.Vertex current) : PartialEndpointIso current closed l r :=
  Or.inl ⟨noEndpointChain l,noEndpointChain r⟩

theorem leftAux : AuxiliaryAt current left := by
  constructor
  · rintro ⟨p,stamp,fn,arg,split,_lookup⟩
    have last := congrArg List.getLast? split
    simp [left] at last
  · rintro ⟨stamp,body,lookup⟩
    cases lookup

theorem rightAux : AuxiliaryAt current right := by
  constructor
  · rintro ⟨p,stamp,fn,arg,split,_lookup⟩
    have last := congrArg List.getLast? split
    simp [right] at last
  · rintro ⟨stamp,body,lookup⟩
    cases lookup

theorem sameLabel : SyntaxIncidence.label current ⟨left,rfl⟩=SyntaxIncidence.label current ⟨right,rfl⟩ := rfl

/-- This is only a conditional physical obstruction, not an actual graph
counterexample. The two real fragment heads must still be constructed on a
reachable graph before any specification conclusion is drawn. -/
theorem auxiliary_failure_of_different_heads
    {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} {root : B}
    (selection : OccurrenceFragmentSelection current g root)
    (different : (selection ⟨left,rfl⟩).fragment.segments.head?≠
      (selection ⟨right,rfl⟩).fragment.segments.head?) : ¬LegacyAuxiliarySeparation closed selection := by
  intro separation
  have notBoth := separation ⟨left,rfl⟩ ⟨right,rfl⟩ leftAux rightAux sameLabel
    (fun same=>different (congrArg List.head? same))
  exact notBoth ⟨allPartial _ _,allPartial _ _⟩
#print axioms actualHistory
#print axioms noChain
#print axioms auxiliary_failure_of_different_heads
end Lamping.Checks.NormalAuxiliaryCandidate

namespace Lamping.Checks.FanUndefinedReachable
open AG Graph Lambda Lambda.Labelled
theorem left_body_head (selection : OccurrenceFragmentSelection result finalNet (.inl ())) :
    ∃ departure : Port (finalNet.label (.inr (.inl false))).sort,
      (selection ⟨[.body,.fn,.arg,.body],rfl⟩).fragment.segments.head?=
        some (.inl ⟨.inr (.inl false),departure⟩) := by
  let chosen := selection ⟨[.body,.fn,.arg,.body],rfl⟩
  have actual : SourceSubterm [] .external result [.body,.fn,.arg,.body] _ _ _ := .body (.fn (.arg (.body .nil)))
  obtain ⟨_env,context,_term⟩ := chosen.occurrence.same_occurrence actual
  have fromCtx : (sourceEdge chosen.environment chosen.context chosen.term).fromPort=chosen.context := by
    cases chosen.term <;> rfl
  have role : SourceDeparture (.lam ((Labelled.Label.atom 6).concat ((Labelled.Label.atom 1).under.concat (.atom 8))) chosen.term)
      .body (sourceEdge chosen.environment chosen.context chosen.term).fromPort := by
    rw [fromCtx,context]
    exact .body
  have word : [.body,.fn,.arg,.body]=accessWord finalNet RootFanLeft.leftParent.val++[.body] := by
    change [.body,.fn,.arg,.body]=accessWord finalNet RootFanLeft.leftEdges++[.body]
    rw [RootFanLeft.leftWord];rfl
  exact chosen.fragment.head_node_of_parent actual_final_matches role RootFanLeft.leftParent
    word (.inr (.inl false)) (.inl ()) RootFanLeft.leftFinish
theorem two_body_heads_different (selection : OccurrenceFragmentSelection result finalNet (.inl ())) :
    (selection ⟨[.body,.fn,.arg,.body],rfl⟩).fragment.segments.head?≠
      (selection ⟨[.body,.arg,.body],rfl⟩).fragment.segments.head? := by
  obtain ⟨leftPort,leftEq⟩:=left_body_head selection
  obtain ⟨rightPort,rightEq⟩:=right_body_head selection
  intro same
  rw [leftEq,rightEq] at same
  have nodes := congrArg Sigma.fst (Sum.inl.inj (Option.some.inj same))
  cases nodes
theorem actual_auxiliary_failure (selection : OccurrenceFragmentSelection result finalNet (.inl ())) :
    ¬LegacyAuxiliarySeparation (history.closed closed) selection :=
  NormalAuxiliaryCandidate.auxiliary_failure_of_different_heads selection (two_body_heads_different selection)
#print axioms left_body_head
#print axioms two_body_heads_different
#print axioms actual_auxiliary_failure
end Lamping.Checks.FanUndefinedReachable
namespace Lamping.Checks.FanUndefinedReachable
open AG Graph Lambda Lambda.Labelled
/-- One actual closed initial instance violates the historical overstrong
both-undefined endpoint equivalence in LegacyAuxiliarySeparation. This is not a
counterexample to the seven rewrite schemas or erased correctness. -/
theorem actual_auxiliary_counterexample :
    INIT initial ∧Closed term ∧History [[]] initial result ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet finalNet) [.beta 0,.fanAction .lam 0 1 (by decide)] ∧
    Matches finalNet (.inl ()) result.erase ∧redexPositions result.erase=[] ∧
    Nonempty (OccurrenceFragmentSelection result finalNet (.inl ())) ∧
    ∀selection : OccurrenceFragmentSelection result finalNet (.inl ()),
      ¬LegacyAuxiliarySeparation (history.closed closed) selection := by
  refine ⟨init_is_INIT term,closed,history,actual_two_rule_trace,actual_final_matches,rfl,?_,actual_auxiliary_failure⟩
  exact actual_final_matches.occurrence_fragment_selection (current:=result) (history.closed closed)
#print axioms actual_auxiliary_counterexample
end Lamping.Checks.FanUndefinedReachable
namespace Lamping.Checks.FanUndefinedReachable
open AG Graph Lambda Lambda.Labelled

/-- This normal-form test is deliberately a vacuous successful-domain boundary
regression. It does not establish general auxiliary or Joint preservation. -/
theorem corrected_auxiliary_domain_regression
    (selection : OccurrenceFragmentSelection result finalNet (.inl ())) :
    AuxiliarySeparation (history.closed closed) selection := by
  intro left right _leftAux _rightAux _sameLabel _different both
  exact NormalAuxiliaryCandidate.noEndpointChain _ both.1.left_available

/-- The same actual INIT/two-event graph still witnesses the legacy failure,
but lies outside the successful endpoint comparison domain of the correction. -/
theorem actual_legacy_failure_and_corrected_domain :
    INIT initial ∧Closed term ∧History [[]] initial result ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet finalNet)
      [.beta 0,.fanAction .lam 0 1 (by decide)] ∧
    Matches finalNet (.inl ()) result.erase ∧
    Nonempty (OccurrenceFragmentSelection result finalNet (.inl ())) ∧
    ∀ selection : OccurrenceFragmentSelection result finalNet (.inl ()),
      ¬LegacyAuxiliarySeparation (history.closed closed) selection ∧
        AuxiliarySeparation (history.closed closed) selection := by
  refine ⟨init_is_INIT term,closed,history,actual_two_rule_trace,actual_final_matches,?_,?_⟩
  · exact actual_final_matches.occurrence_fragment_selection (current:=result) (history.closed closed)
  · intro selection
    exact ⟨actual_auxiliary_failure selection,corrected_auxiliary_domain_regression selection⟩
#print axioms corrected_auxiliary_domain_regression
#print axioms actual_legacy_failure_and_corrected_domain
end Lamping.Checks.FanUndefinedReachable
