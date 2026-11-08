import Lamping.Lamping.SafeBetaAuxiliaryTransport
import Lamping.Checks.AuxiliaryEndpointReflection
import Lamping.Checks.OldChainBetaFixture
import Lamping.Lamping.BetaCompleteMatching

namespace Lamping.Checks.SafeBetaAuxiliaryTransportChecks
open Graph Lambda Lambda.Labelled AG
namespace Known
open OldChainBetaFixture
open AuxiliaryEndpointReflectionChecks.Physical

theorem direct_safe_body_variable
    (presentation : PhysicalCorridorPresentation net (.beta 0) app lam (.inl ()) (.inl ()))
    (source : OccurrenceFragmentSelection initial presentation.site.net (.inl ()))
    (target : OccurrenceFragmentSelection result presentation.site.reduce (.inl ()))
    (joint : JointRepresentation sourceClosed source) :
    (target edge).fragment.segments=(target edge).fragment.segments := by
  have matching := presentation.sourceIso.matches (encode_closed_matches term closed 0)
  have inputs := presentation.sourceIso.rootInputs (encode_closed_independence term closed 0).rootInputs
  obtain ⟨oldFlow⟩ := encode_flowBalance term 0
  obtain ⟨oldBalance⟩ := encode_indexed_balance term 0
  have member : redex.val∈presentation.site.betaSyntaxFiber (.inl ()) initial.erase := by
    have fiber : presentation.site.betaSyntaxFiber (.inl ()) initial.erase=[[]] := by
      simpa only [initial,erase_initLabels] using actual_fiber presentation
    rw [fiber];exact List.mem_singleton_self _
  exact presentation.site.beta_incoming_safe_auxiliary_pair (init_is_INIT term) (.nil _) (.nil _) (.nil _)
    sourceClosed matching inputs (presentation.sourceIso.flowBalance oldFlow) rfl
    (presentation.sourceIso.indexed_balance oldBalance) rfl
    (presentation.sourceIso.transparency (encode_closed_transparency term closed 0))
    (relative presentation) (by simp [endpoint,Marked.Normal]) history source target joint redex member rfl
    edge edge auxiliary auxiliary rfl (by trivial) both_successful.1 both_successful.2
end Known

namespace MarkedArgument
abbrev I : Term := identity
abbrev term : Term := .app (.lam (.app (.lam (.app (.var 1) (.var 0))) I)) I
abbrev original : LTerm := initLabels term
abbrev body : LTerm := .app (.atom 2)
  (.lam (.atom 3) (.app (.atom 4) (.var (.atom 5) 1) (.var (.atom 6) 0)))
  (.lam (.atom 7) (.var (.atom 8) 0))
abbrev argument : LTerm := .lam (.atom 9) (.var (.atom 10) 0)
abbrev current : LTerm := LTerm.contract (.atom 0) (.atom 1) body argument
abbrev net := (encode 0 term).net

theorem initial : INIT original := init_is_INIT _
theorem closed : Closed original.erase := by
  change ((1<2 ∧0<2) ∧0<2) ∧0<1
  decide

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
  ⟨childEdges,⟨⟨⟨_,_,childLabels⟩,.node app appCtx (.inl ()) rfl rfl ⟨rfl,Or.inl rfl⟩ principalForward⟩,
    rfl,⟨.lam,rfl⟩⟩⟩
def redex : RedexOcc term := ⟨[],_,rfl,True.intro⟩
def rich : ActualRedexAccess net (.inl ()) redex where
  connection := {
    app := app,lam := lam,appPort := .inl (),lamPort := .inl (),appIndex := 0,lamIndex := 0
    appLabel := rfl,lamLabel := rfl,appPrincipal := HEq.rfl,lamPrincipal := HEq.rfl
    edges := corridor.edges,proper := ⟨⟨Context.empty,Context.empty,principalLabels _⟩,principalForward⟩,
    start := rfl,finish := rfl,emptyWord := rfl }
  parent := parent
  child := child
  ctx := appCtx
  contextPrincipal := HEq.rfl
  parentWord := rfl
  childWord := rfl
  parentFinish := rfl
  split := rfl

theorem root_member : []∈physicalBetaFiberPaths net (.inl ()) term app lam :=
  (mem_physicalBetaFiberPaths net (.inl ()) term app lam []).mpr ⟨redex,rich,rfl,rfl,rfl⟩

theorem presentation_exists : Nonempty (PhysicalCorridorPresentation net (.beta 0) app lam (.inl ()) (.inl ())) :=
  physical_corridor_presentation net (.beta 0) corridor app lam (by intro same;cases same)
    rfl rfl (.inl ()) (.inl ()) HEq.rfl HEq.rfl rfl rfl

theorem fiber (presentation : PhysicalCorridorPresentation net (.beta 0) app lam (.inl ()) (.inl ())) :
    presentation.site.betaSyntaxFiber (.inl ()) term=[[]] := by
  have sourceMatches : Matches net (.inl ()) original.erase := encode_closed_matches term closed 0
  have matching := presentation.sourceIso.matches sourceMatches
  obtain ⟨sourceSelection,initialJoint⟩ := encode_initial_joint_realization original closed initial 0
  obtain ⟨localSelection⟩ := matching.occurrence_fragment_selection closed
  have joint := (presentation.sourceIso.joint_representation sourceMatches closed sourceSelection localSelection).mpr initialJoint
  have member : []∈presentation.site.betaSyntaxFiber (.inl ()) original.erase := by
    rw [presentation.betaSyntaxFiber_eq];exact root_member
  let other : RedexOcc original.erase := ⟨[.fn,.body],_,rfl,True.intro⟩
  have absent : [.fn,.body]∉presentation.site.betaSyntaxFiber (.inl ()) original.erase := by
    intro chosen
    have degrees := (presentation.site.beta_fiber_iff_degree closed matching localSelection joint.1 redex member other).mp chosen
    change some (Lambda.Labelled.Label.atom 3)=some (Lambda.Labelled.Label.atom 1) at degrees
    cases degrees
  let test := physicalBetaTest presentation.site.net (.inl ()) term (.inr (.inl ())) (.inr (.inr ()))
  have first : test []=true := by
    change []∈([[],[.fn,.body]] : List Path).filter test at member
    exact (List.mem_filter.mp member).2
  have second : test [.fn,.body]=false := by
    cases result : test [.fn,.body] with
    | false => rfl
    | true =>
      apply False.elim
      apply absent
      change [.fn,.body]∈([[],[.fn,.body]] : List Path).filter test
      exact List.mem_filter.mpr ⟨by simp,result⟩
  change ([[],[.fn,.body]] : List Path).filter test=[[]]
  simp [first,second]

def actualStep : StepAt [] original current := .root _ _ _ _
def history : History [[]] original current := .cons actualStep (.nil _)
abbrev endpoint : Marked := .app [[.fn,.body]]
  (.lam (.app [] (.lam (.var 0)) (.var 0))) (.lam (.var 0))

theorem relative (presentation : PhysicalCorridorPresentation net (.beta 0) app lam (.inl ()) (.inl ())) :
    Marked.RelativeHistory [[]] (Marked.mark (presentation.site.betaSyntaxFiber (.inl ()) original.erase) original.erase) endpoint := by
  have same : presentation.site.betaSyntaxFiber (.inl ()) original.erase=[[]] := by
    simpa only [original,erase_initLabels] using fiber presentation
  rw [same]
  exact .cons (.root _ _ _) (.nil _)

def edge : SyntaxIncidence.Edge current := ⟨[.fn,.body,.arg],rfl⟩
def fromVertex : SyntaxIncidence.ProperPosition current := ⟨[.fn,.body],Or.inl ⟨_,_,_,rfl⟩⟩
def binder : SyntaxIncidence.ProperPosition current := ⟨[.fn],Or.inr ⟨_,_,rfl⟩⟩
abbrev currentClosed : Closed current.erase := history.closed closed

theorem auxiliary : AuxiliaryAt current edge.val := by
  constructor
  · rintro ⟨parent,stamp,fn,arg,split,_lookup⟩
    have last := congrArg List.getLast? split
    simp only [edge,List.getLast?_cons_cons,List.getLast?_singleton,List.getLast?_append,Option.some_or] at last
    cases last
  · rintro ⟨stamp,body,lookup⟩
    cases lookup

theorem from_spec : SyntaxIncidence.Source current edge.val (some fromVertex) :=
  ⟨.arg,.app (.atom 4) (.lam (((Lambda.Labelled.Label.atom 5).concat (Lambda.Labelled.Label.atom 1).under).concat (.atom 9))
    (.var (.atom 10) 0)) (.var (.atom 6) 0),.appArg (.atom 4),rfl,rfl,.arg⟩

theorem target_spec : SyntaxIncidence.Target current edge.val (some binder) :=
  Or.inr ⟨.atom 6,0,.atom 3,_,[.arg],rfl,rfl,rfl,rfl⟩

def from_chain : EndpointChain current (some fromVertex) [[.fn,.body,.fn]] :=
  PrerequisiteChain.redex_app (by rfl)
def binder_chain : EndpointChain current (some binder) [[.fn]] := by
  change PrerequisiteChain current ([]++[.fn]) [[]++[.fn]]
  exact PrerequisiteChain.redex_lam rfl

theorem incoming_safe : (SyntaxIncidence.label current edge).OuterBarsSafe (fun x=>x≠Lambda.Labelled.Label.atom 1) := by trivial

theorem parent_read_marked : ¬degreeReadSafe (.atom 1) (current.labelAt [.fn,.body,.fn]) := by
  intro safe
  have created : BetaCreatedIncoming body [] [.fn,.body,.fn] :=
    betaCreatedIncoming_iff.mpr (Or.inr ⟨[.fn,.body,.fn],rfl,rfl⟩)
  have notSafe := actualStep.created_label_not_safe (by rfl) (current:=.lam
    (((Lambda.Labelled.Label.atom 5).concat (Lambda.Labelled.Label.atom 1).under).concat (.atom 9))
    (.var (.atom 10) 0)) (by rfl) created
  exact notSafe (safe _ rfl)

theorem both_successful :
    SuccessfulEndpointIso current currentClosed (SyntaxIncidence.source current edge) (SyntaxIncidence.source current edge) ∧
    SuccessfulEndpointIso current currentClosed (SyntaxIncidence.target current currentClosed edge)
      (SyntaxIncidence.target current currentClosed edge) := by
  rw [SyntaxIncidence.source_eq_of_spec current edge from_spec,
    SyntaxIncidence.target_eq_of_spec current currentClosed edge target_spec]
  exact ⟨SuccessfulEndpointIso.refl_of_chain from_chain,SuccessfulEndpointIso.refl_of_chain binder_chain⟩

theorem direct_safe_argument_variable
    (presentation : PhysicalCorridorPresentation net (.beta 0) app lam (.inl ()) (.inl ()))
    (source : OccurrenceFragmentSelection original presentation.site.net (.inl ()))
    (target : OccurrenceFragmentSelection current presentation.site.reduce (.inl ()))
    (joint : JointRepresentation closed source) :
    (target edge).fragment.segments=(target edge).fragment.segments := by
  have matching := presentation.sourceIso.matches (encode_closed_matches term closed 0)
  have inputs := presentation.sourceIso.rootInputs (encode_closed_independence term closed 0).rootInputs
  obtain ⟨oldFlow⟩ := encode_flowBalance term 0
  obtain ⟨oldBalance⟩ := encode_indexed_balance term 0
  have member : redex.val∈presentation.site.betaSyntaxFiber (.inl ()) original.erase := by
    have same : presentation.site.betaSyntaxFiber (.inl ()) original.erase=[[]] := by
      simpa only [original,erase_initLabels] using fiber presentation
    rw [same];exact List.mem_singleton_self _
  exact presentation.site.beta_incoming_safe_auxiliary_pair initial (.nil _) (.nil _) (.nil _)
    closed matching inputs (presentation.sourceIso.flowBalance oldFlow) rfl
    (presentation.sourceIso.indexed_balance oldBalance) rfl
    (presentation.sourceIso.transparency (encode_closed_transparency term closed 0))
    (relative presentation) (by simp [Marked.Normal]) history source target joint redex member rfl
    edge edge auxiliary auxiliary rfl incoming_safe both_successful.1 both_successful.2

theorem actual_target_matches
    (presentation : PhysicalCorridorPresentation net (.beta 0) app lam (.inl ()) (.inl ())) :
    Matches presentation.site.reduce (.inl ()) current.erase := by
  obtain ⟨oldFlow⟩ := encode_flowBalance term 0
  obtain ⟨oldBalance⟩ := encode_indexed_balance term 0
  exact presentation.site.beta_complete_matches initial closed
    (presentation.sourceIso.matches (encode_closed_matches term closed 0))
    (presentation.sourceIso.rootInputs (encode_closed_independence term closed 0).rootInputs)
    (presentation.sourceIso.flowBalance oldFlow) rfl
    (presentation.sourceIso.indexed_balance oldBalance) rfl
    (presentation.sourceIso.transparency (encode_closed_transparency term closed 0))
    (relative presentation) (by simp [Marked.Normal]) history

/-- Actual constructed physical step, target Matches and nonempty selectors.
The SOURCEJoint is the genuine original encoding base, transported by sourceIso. -/
theorem actual_nonempty_physical_domain :
    ∃ presentation : PhysicalCorridorPresentation net (.beta 0) app lam (.inl ()) (.inl ()),
      GraphStep (.beta 0) (ActualNet.ofNet net) (ActualNet.ofNet presentation.site.reduce) ∧
      Matches presentation.site.reduce (.inl ()) current.erase ∧
      ∃ source : OccurrenceFragmentSelection original presentation.site.net (.inl ()),
      ∃ target : OccurrenceFragmentSelection current presentation.site.reduce (.inl ()),
        JointRepresentation closed source ∧
        (target edge).fragment.segments=(target edge).fragment.segments := by
  obtain ⟨presentation⟩ := presentation_exists
  have originalMatches := encode_closed_matches term closed 0
  have matching := presentation.sourceIso.matches originalMatches
  obtain ⟨originalSelection,initialJoint⟩ := encode_initial_joint_realization original closed initial 0
  obtain ⟨source⟩ := matching.occurrence_fragment_selection closed
  have joint := (presentation.sourceIso.joint_representation originalMatches closed originalSelection source).mpr initialJoint
  have targetMatches := actual_target_matches presentation
  obtain ⟨target⟩ := targetMatches.occurrence_fragment_selection currentClosed
  exact ⟨presentation,presentation.graph_step,targetMatches,source,target,joint,
    direct_safe_argument_variable presentation source target joint⟩
end MarkedArgument
end Lamping.Checks.SafeBetaAuxiliaryTransportChecks

#print axioms Lamping.Checks.SafeBetaAuxiliaryTransportChecks.Known.direct_safe_body_variable
#print axioms Lamping.Checks.SafeBetaAuxiliaryTransportChecks.MarkedArgument.presentation_exists
#print axioms Lamping.Checks.SafeBetaAuxiliaryTransportChecks.MarkedArgument.fiber
#print axioms Lamping.Checks.SafeBetaAuxiliaryTransportChecks.MarkedArgument.relative
#print axioms Lamping.Checks.SafeBetaAuxiliaryTransportChecks.MarkedArgument.auxiliary
#print axioms Lamping.Checks.SafeBetaAuxiliaryTransportChecks.MarkedArgument.both_successful
#print axioms Lamping.Checks.SafeBetaAuxiliaryTransportChecks.MarkedArgument.parent_read_marked
#print axioms Lamping.Checks.SafeBetaAuxiliaryTransportChecks.MarkedArgument.direct_safe_argument_variable

#print axioms Lamping.Checks.SafeBetaAuxiliaryTransportChecks.MarkedArgument.actual_target_matches
#print axioms Lamping.Checks.SafeBetaAuxiliaryTransportChecks.MarkedArgument.actual_nonempty_physical_domain
