import Lamping.Checks.OldChainBetaFixture
import Lamping.Checks.NodeLabelSuffixOrigins
import Lamping.Checks.AuxiliaryNodeHistoryOrigins
import Lamping.Lamping.BetaCompleteMatching
namespace Lamping.Checks.MarkedAuxiliaryPhysicalFixture
open Graph Lambda Lambda.Labelled AG
abbrev term : Term:=NodeLabelSuffixOriginsChecks.bare
abbrev original : LTerm:=NodeLabelSuffixOriginsChecks.source
abbrev current : LTerm:=NodeLabelSuffixOriginsChecks.target
abbrev net := (encode 0 term).net

theorem initial : INIT original:=NodeLabelSuffixOriginsChecks.initial
theorem closed : Closed original.erase:=NodeLabelSuffixOriginsChecks.closed
abbrev history : History [[.arg]] original current:=NodeLabelSuffixOriginsChecks.actualHistory
abbrev currentClosed : Closed current.erase:=history.closed closed

def outerApp : (encode 0 term).N:=.inl (.inl ())
def app : (encode 0 term).N:=.inr (.inr (.inl (.inl ())))
def lam : (encode 0 term).N:=.inr (.inr (.inr (.inl (.inl ()))))
def principalWire : (encode 0 term).W:=.inl (.inr (.inr (.inr (.inl (.inl ())))))
def outerArgWire : (encode 0 term).W:=.inr (.inr (.inl ()))
def rootEnd : Endpoint net:=.inr (.inl (.inl ()))

theorem wire_equations :
    net.label app=label .app 1 ∧net.label lam=label .lam 1 ∧
    net.wire rootEnd=.inl ⟨outerApp,appCtx⟩ ∧
    net.wire (.inl ⟨outerApp,appArg⟩)=.inr (.inr (outerArgWire,false)) ∧
    net.wire (.inr (.inr (outerArgWire,true)))=.inl ⟨app,appCtx⟩ ∧
    net.wire (.inl ⟨app,.inl ()⟩)=.inr (.inr (principalWire,false)) ∧
    net.wire (.inr (.inr (principalWire,true)))=.inl ⟨lam,.inl ()⟩ :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

def corridor : TransparentCorridor net where
  first:=⟨app,.inl ()⟩
  last:=⟨lam,.inl ()⟩
  edges:=[.inl ⟨app,.inl ()⟩,.inr (.inr (principalWire,true))]
  start:=rfl
  finish:=rfl
  transparent:=by
    intro e f member
    have same:=List.mem_singleton.mp member
    cases same
    exact ⟨principalWire,false,rfl,rfl⟩

def parentEdges : List (Endpoint net):=
  [rootEnd,.inl ⟨outerApp,appArg⟩,.inr (.inr (outerArgWire,true))]
theorem parentLabels (a : Context) : Labelling net parentEdges a a :=
  .cons (LabelledTurn.node (g:=net) outerApp appCtx appArg (.direct (.appArg a)))
    (.cons (LabelledTurn.transparent (g:=net) outerArgWire false a) (.single _ _))
theorem parentForward : Forward net parentEdges :=
  .node outerApp appCtx appArg rfl rfl ⟨rfl,Or.inr rfl⟩
    (.transparent outerArgWire false rfl rfl (.single _))
def parent : RootAccess net (.inl ()):=
  ⟨parentEdges,⟨⟨⟨Context.empty,Context.empty,parentLabels _⟩,parentForward⟩,rfl,⟨.app,rfl⟩⟩⟩
theorem principalLabels (a : Context) : Labelling net corridor.edges a a :=
  .cons (LabelledTurn.transparent (g:=net) principalWire false a) (.single _ _)
theorem principalForward : Forward net corridor.edges :=
  .transparent principalWire false rfl rfl (.single _)
def childEdges : List (Endpoint net):=parentEdges++corridor.edges
theorem childLabels (a : Context) : Labelling net childEdges a a :=
  .cons (LabelledTurn.node (g:=net) outerApp appCtx appArg (.direct (.appArg a)))
    (.cons (LabelledTurn.transparent (g:=net) outerArgWire false a)
      (.cons (LabelledTurn.node (g:=net) app appCtx (.inl ()) (.direct (.appFun a))) (principalLabels a)))
def child : RootAccess net (.inl ()):=
  ⟨childEdges,⟨⟨⟨Context.empty,Context.empty,childLabels _⟩,
    .node outerApp appCtx appArg rfl rfl ⟨rfl,Or.inr rfl⟩
      (.transparent outerArgWire false rfl rfl
        (.node app appCtx (.inl ()) rfl rfl ⟨rfl,Or.inl rfl⟩ principalForward))⟩,
    rfl,⟨.lam,rfl⟩⟩⟩
def redex : RedexOcc term:=⟨[.arg],_,rfl,True.intro⟩
def rich : ActualRedexAccess net (.inl ()) redex where
  connection:={
    app:=app,lam:=lam,appPort:=.inl (),lamPort:=.inl (),appIndex:=1,lamIndex:=1
    appLabel:=rfl,lamLabel:=rfl,appPrincipal:=HEq.rfl,lamPrincipal:=HEq.rfl
    edges:=corridor.edges,proper:=⟨⟨Context.empty,Context.empty,principalLabels _⟩,principalForward⟩
    start:=rfl,finish:=rfl,emptyWord:=rfl }
  parent:=parent
  child:=child
  ctx:=appCtx
  contextPrincipal:=HEq.rfl
  parentWord:=rfl
  childWord:=rfl
  parentFinish:=rfl
  split:=rfl

theorem selected_member : [.arg]∈physicalBetaFiberPaths net (.inl ()) term app lam :=
  (mem_physicalBetaFiberPaths net (.inl ()) term app lam [.arg]).mpr ⟨redex,rich,rfl,rfl,rfl⟩
noncomputable def concrete:=PhysicalCorridorPresentation.of_corridor net (.beta 1) corridor app lam
  (by intro same;cases same) rfl rfl (.inl ()) (.inl ()) HEq.rfl HEq.rfl rfl rfl
theorem actual_beta_step : GraphStep (.beta 1) (ActualNet.initial term)
    (ActualNet.ofNet concrete.site.reduce):=concrete.graph_step

theorem source_matching : Matches concrete.site.net (.inl ()) original.erase :=
  concrete.sourceIso.matches (encode_closed_matches term closed 0)
theorem source_inputs : RootInputs concrete.site.net (.inl ()) :=
  concrete.sourceIso.rootInputs (encode_closed_independence term closed 0).rootInputs
theorem source_flow : Nonempty (FlowBalance concrete.site.net initialBoundaryPolarity) := by
  obtain ⟨flow⟩:=encode_flowBalance term 0
  exact ⟨concrete.sourceIso.flowBalance flow⟩
theorem source_indexed_balance : Nonempty (IndexedLevelBalance concrete.site.net (boundaryDepthAt 0)) := by
  obtain ⟨balance⟩:=encode_indexed_balance term 0
  exact ⟨concrete.sourceIso.indexed_balance balance⟩
theorem source_transparency : Transparency concrete.site.net (.inl ()) :=
  concrete.sourceIso.transparency (encode_closed_transparency term closed 0)
theorem source_positive : (initialBoundaryPolarity (.inl () : Boundary term))=true:=rfl
theorem source_root_depth : (boundaryDepthAt 0 (.inl () : Boundary term))=0:=rfl

theorem source_joint : ∃selection : OccurrenceFragmentSelection original concrete.site.net (.inl ()),
    JointRepresentation closed selection := by
  obtain ⟨originalSelection,initialJoint⟩:=encode_initial_joint_realization original closed initial 0
  obtain ⟨selection⟩:=source_matching.occurrence_fragment_selection closed
  have joint:=(concrete.sourceIso.joint_representation (encode_closed_matches term closed 0)
    closed originalSelection selection).mpr initialJoint
  exact ⟨selection,joint⟩

theorem physical_member : redex.val∈concrete.site.betaSyntaxFiber (.inl ()) original.erase := by
  rw [concrete.betaSyntaxFiber_eq];exact selected_member

theorem exact_fiber : concrete.site.betaSyntaxFiber (.inl ()) original.erase=[[.arg]] := by
  obtain ⟨selection,joint⟩:=source_joint
  let rootRedex : RedexOcc original.erase:=⟨[],_,rfl,True.intro⟩
  let innerRedex : RedexOcc original.erase:=⟨[.arg,.arg],_,rfl,True.intro⟩
  have noRoot : []∉concrete.site.betaSyntaxFiber (.inl ()) original.erase := by
    intro member
    have degrees:=(concrete.site.beta_fiber_iff_degree closed source_matching selection joint.1
      redex physical_member rootRedex).mp member
    change some (Lambda.Labelled.Label.atom 1)=some (Lambda.Labelled.Label.atom 4) at degrees
    cases degrees
  have noInner : [.arg,.arg]∉concrete.site.betaSyntaxFiber (.inl ()) original.erase := by
    intro member
    have degrees:=(concrete.site.beta_fiber_iff_degree closed source_matching selection joint.1
      redex physical_member innerRedex).mp member
    change some (Lambda.Labelled.Label.atom 7)=some (Lambda.Labelled.Label.atom 4) at degrees
    cases degrees
  let test:=physicalBetaTest concrete.site.net (.inl ()) term (.inr (.inl ())) (.inr (.inr ()))
  have yes : test [.arg]=true := by
    have member:=physical_member
    change [.arg]∈([[],[.arg],[.arg,.arg]] : List Path).filter test at member
    exact (List.mem_filter.mp member).2
  have first : test []=false := by
    cases value : test [] with
    | false => rfl
    | true =>
      apply False.elim;apply noRoot
      change []∈([[],[.arg],[.arg,.arg]] : List Path).filter test
      exact List.mem_filter.mpr ⟨by simp,value⟩
  have last : test [.arg,.arg]=false := by
    cases value : test [.arg,.arg] with
    | false => rfl
    | true =>
      apply False.elim;apply noInner
      change [.arg,.arg]∈([[],[.arg],[.arg,.arg]] : List Path).filter test
      exact List.mem_filter.mpr ⟨by simp,value⟩
  change ([[],[.arg],[.arg,.arg]] : List Path).filter test=[[.arg]]
  simp [first,yes,last]

theorem at_degree : original.degreeAt redex.val=some (Lambda.Labelled.Label.atom 4):=rfl

def endpoint : Marked:=.app [[]] (.lam (.var 0))
  (.app [[.arg,.arg]] (.lam (.var 0)) (.lam (.var 0)))
theorem relative : Marked.RelativeHistory [[.arg]]
    (Marked.mark (concrete.site.betaSyntaxFiber (.inl ()) original.erase) original.erase) endpoint := by
  rw [exact_fiber]
  exact .cons (.appR (.root _ _ _)) (.nil _)
theorem normal : Marked.Normal endpoint:=by simp [endpoint,Marked.Normal]

theorem target_matches : Matches concrete.site.reduce (.inl ()) current.erase := by
  obtain ⟨flow⟩:=source_flow
  obtain ⟨balance⟩:=source_indexed_balance
  exact concrete.site.beta_complete_matches initial closed source_matching source_inputs flow source_positive
    balance source_root_depth source_transparency relative normal history

def currentEdge : SyntaxIncidence.Edge current:=⟨[.arg],by
  rw [←LTerm.erase_subterm,NodeLabelSuffixOriginsChecks.actual_lookup];rfl⟩
def sourceVertex : SyntaxIncidence.ProperPosition current:=AuxiliaryNodeHistoryOriginsChecks.currentOuter
def targetVertex : SyntaxIncidence.ProperPosition current:=⟨[.arg],Or.inl ⟨_,_,_,NodeLabelSuffixOriginsChecks.actual_lookup⟩⟩
theorem from_spec : SyntaxIncidence.Source current currentEdge.val (some sourceVertex):=
  AuxiliaryNodeHistoryOriginsChecks.target_source_endpoint
theorem to_spec : SyntaxIncidence.Target current currentEdge.val (some targetVertex):=Or.inl rfl

theorem actual_marked_word : (SyntaxIncidence.label current currentEdge).letters=
    [.atom 3,.over (.atom 4),.atom 5,.under (.atom 4),.atom 6] := by
  rw [SyntaxIncidence.label_of_lookup current currentEdge NodeLabelSuffixOriginsChecks.actual_lookup]
  exact NodeLabelSuffixOriginsChecks.actual_overlap_word

theorem auxiliary : AuxiliaryAt current currentEdge.val:=NodeLabelSuffixOriginsChecks.actual_auxiliary
theorem marked : ¬(SyntaxIncidence.label current currentEdge).OuterBarsSafe (fun x=>x≠Lambda.Labelled.Label.atom 4) := by
  rw [SyntaxIncidence.label_of_lookup current currentEdge NodeLabelSuffixOriginsChecks.actual_lookup]
  exact NodeLabelSuffixOriginsChecks.actual_marked

theorem both_successful :
    SuccessfulEndpointIso current currentClosed (SyntaxIncidence.source current currentEdge) (SyntaxIncidence.source current currentEdge) ∧
    SuccessfulEndpointIso current currentClosed (SyntaxIncidence.target current currentClosed currentEdge)
      (SyntaxIncidence.target current currentClosed currentEdge) := by
  rw [SyntaxIncidence.source_eq_of_spec current currentEdge from_spec,
    SyntaxIncidence.target_eq_of_spec current currentClosed currentEdge to_spec]
  exact ⟨.refl_of_chain NodeLabelSuffixOriginsChecks.actual_source_endpoint_chain,
    .refl_of_chain NodeLabelSuffixOriginsChecks.actual_target_endpoint_chain⟩

/-- The antecedent domain is actually inhabited; no desired physical Eq,
TARGETJoint or marked-Aux transport theorem is supplied. -/
theorem actual_marked_auxiliary_domain :
    GraphStep (.beta 1) (ActualNet.initial term) (ActualNet.ofNet concrete.site.reduce) ∧
    concrete.site.betaSyntaxFiber (.inl ()) original.erase=[[.arg]] ∧
    Marked.RelativeHistory [[.arg]] (Marked.mark (concrete.site.betaSyntaxFiber (.inl ()) original.erase) original.erase) endpoint ∧
    Marked.Normal endpoint ∧Matches concrete.site.reduce (.inl ()) current.erase ∧
    ∃sourceSelection : OccurrenceFragmentSelection original concrete.site.net (.inl ()),
      JointRepresentation closed sourceSelection ∧
      Nonempty (OccurrenceFragmentSelection current concrete.site.reduce (.inl ())) ∧
      AuxiliaryAt current currentEdge.val ∧
      ¬(SyntaxIncidence.label current currentEdge).OuterBarsSafe (fun x=>x≠Lambda.Labelled.Label.atom 4) ∧
      SuccessfulEndpointIso current currentClosed (SyntaxIncidence.source current currentEdge) (SyntaxIncidence.source current currentEdge) ∧
      SuccessfulEndpointIso current currentClosed (SyntaxIncidence.target current currentClosed currentEdge)
        (SyntaxIncidence.target current currentClosed currentEdge) := by
  obtain ⟨sourceSelection,joint⟩:=source_joint
  obtain ⟨targetSelection⟩:=target_matches.occurrence_fragment_selection currentClosed
  exact ⟨actual_beta_step,exact_fiber,relative,normal,target_matches,sourceSelection,joint,⟨targetSelection⟩,
    auxiliary,marked,both_successful.1,both_successful.2⟩

#print axioms wire_equations
#print axioms parentLabels
#print axioms childLabels
#print axioms rich
#print axioms selected_member
#print axioms actual_beta_step
#print axioms source_matching
#print axioms source_inputs
#print axioms source_flow
#print axioms source_indexed_balance
#print axioms source_transparency
#print axioms source_joint
#print axioms exact_fiber
#print axioms at_degree
#print axioms relative
#print axioms normal
#print axioms target_matches
#print axioms actual_marked_word
#print axioms auxiliary
#print axioms marked
#print axioms both_successful
#print axioms actual_marked_auxiliary_domain
end Lamping.Checks.MarkedAuxiliaryPhysicalFixture
