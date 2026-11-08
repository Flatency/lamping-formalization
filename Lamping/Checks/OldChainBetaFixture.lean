import Lamping.Lamping.BetaUncreatedFragmentResiduals
import Lamping.Lamping.Fixtures
import Lamping.Lamping.InitialFullIndependence
import Lamping.Lamping.PhysicalCorridorPresentation
import Lamping.Lamping.NetIsoBetaFiberTransport
import Lamping.Lamping.InitialJointRepresentation
import Lamping.Lamping.JointRepresentationTransport
import Lamping.Lamping.BetaFiberDegrees

namespace Lamping.Checks.OldChainBetaFixture
open AG Graph Lambda Lambda.Labelled
abbrev term : Term := .app identity identityApp
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
theorem closed : Closed term := by change (0<1) ∧ (0<1) ∧ (0<1);decide
theorem actual_root_member : []∈physicalBetaFiberPaths net (.inl ()) term app lam := by
  exact (mem_physicalBetaFiberPaths net (.inl ()) term app lam []).mpr ⟨redex,rich,rfl,rfl,rfl⟩
theorem actual_presentation : Nonempty (PhysicalCorridorPresentation net (.beta 0) app lam (.inl ()) (.inl ())) :=
  physical_corridor_presentation net (.beta 0) corridor app lam (by intro same;cases same)
    rfl rfl (.inl ()) (.inl ()) HEq.rfl HEq.rfl rfl rfl
theorem actual_fiber (presentation : PhysicalCorridorPresentation net (.beta 0) app lam (.inl ()) (.inl ())) :
    presentation.site.betaSyntaxFiber (.inl ()) term=[[]] := by
  let current := initLabels term
  have sourceMatches : Matches net (.inl ()) current.erase := encode_closed_matches term closed 0
  have targetMatches := presentation.sourceIso.matches sourceMatches
  obtain ⟨sourceSelection,initialJoint⟩ := encode_initial_joint_realization current closed (init_is_INIT term) 0
  obtain ⟨targetSelection⟩ := targetMatches.occurrence_fragment_selection closed
  have joint := (presentation.sourceIso.joint_representation sourceMatches closed sourceSelection targetSelection).mpr initialJoint
  have rootMember : []∈presentation.site.betaSyntaxFiber (.inl ()) current.erase := by
    rw [presentation.betaSyntaxFiber_eq]
    exact actual_root_member
  let representative : RedexOcc current.erase := redex
  let other : RedexOcc current.erase := ⟨[.arg],_,rfl,True.intro⟩
  have absent : [.arg]∉presentation.site.betaSyntaxFiber (.inl ()) current.erase := by
    intro member
    have degrees := (presentation.site.beta_fiber_iff_degree (current:=current) closed targetMatches targetSelection joint.1
      representative rootMember other).mp member
    change some (Labelled.Label.atom 4)=some (Labelled.Label.atom 1) at degrees
    cases degrees
  let test := physicalBetaTest presentation.site.net (.inl ()) term (.inr (.inl ())) (.inr (.inr ()))
  have first : test []=true := by
    change []∈([[],[.arg]] : List Path).filter test at rootMember
    exact (List.mem_filter.mp rootMember).2
  have second : test [.arg]=false := by
    cases result : test [.arg] with
    | false => rfl
    | true =>
      apply False.elim
      apply absent
      change [.arg]∈([[],[.arg]] : List Path).filter test
      exact List.mem_filter.mpr ⟨by simp,result⟩
  change ([[],[.arg]] : List Path).filter test=[[]]
  simp [first,second]
abbrev initial := initLabels term
abbrev result : LTerm := LTerm.contract (.atom 0) (.atom 1) (.var (.atom 2) 0)
  (.app (.atom 3) (.lam (.atom 4) (.var (.atom 5) 0)) (.lam (.atom 6) (.var (.atom 7) 0)))
def turn : StepAt [] initial result := .root _ _ _ _
def history : History [[]] initial result := .cons turn (.nil _)
def endpoint : Marked := .app [[.arg]] (.lam (.var 0)) (.lam (.var 0))
theorem relative (presentation : PhysicalCorridorPresentation net (.beta 0) app lam (.inl ()) (.inl ())) :
    Marked.RelativeHistory [[]] (Marked.mark (presentation.site.betaSyntaxFiber (.inl ()) initial.erase) initial.erase)
      endpoint := by
  change Marked.RelativeHistory [[]] (Marked.mark (presentation.site.betaSyntaxFiber (.inl ()) term) term) endpoint
  rw [actual_fiber presentation]
  exact .cons (.root _ _ _) (.nil _)
def complete : ParallelStep [[]] initial.erase result.erase := by
  refine ⟨[[]],endpoint,(Marked.completeOld_iff _ _).mpr ⟨?_,?_⟩,rfl⟩
  · exact .cons (.root _ _ _) (.nil _)
  · simp [endpoint,Marked.Normal]
def targetChain : PrerequisiteChain result [] [[.fn]] := .redex_app rfl
def oldChain : PrerequisiteChain initial [.arg] [[.arg,.fn]] := .redex_app rfl
theorem marker_free : ∀ edge∈([[.fn]] : List Path),∀ node,result.subterm edge=some node →
    node.label.OuterBarsSafe (fun payload=>payload≠Labelled.Label.atom 1) := by
  intro edge member node lookup
  have same := List.mem_singleton.mp member
  subst edge
  have nodeEq : node=.lam (.atom 4) (.var (.atom 5) 0) := Option.some.inj lookup.symm
  rw [nodeEq]
  trivial
theorem actual_old_function_fragment
    (presentation : PhysicalCorridorPresentation net (.beta 0) app lam (.inl ()) (.inl ()))
    (sourceSelection : OccurrenceFragmentSelection initial presentation.site.net (.inl ()))
    (targetSelection : OccurrenceFragmentSelection result presentation.site.reduce (.inl ())) :
    ∃ edge : BetaEdge presentation.site.net,SiteBetaGeometry presentation.site edge ∧
      BetaPathResidual presentation.site edge
        ((targetSelection ⟨[.fn],rfl⟩).fragment.segments.map (plugEnd _ _).invFun)
        (sourceSelection ⟨[.arg,.fn],rfl⟩).fragment.segments := by
  have matching := presentation.sourceIso.matches (encode_closed_matches term closed 0)
  have inputs := presentation.sourceIso.rootInputs (encode_closed_independence term closed 0).rootInputs
  obtain ⟨originalFlow⟩ := encode_flowBalance term 0
  have flow := presentation.sourceIso.flowBalance originalFlow
  obtain ⟨originalBalance⟩ := encode_indexed_balance term 0
  have balance := presentation.sourceIso.indexed_balance originalBalance
  have transparency := presentation.sourceIso.transparency (encode_closed_transparency term closed 0)
  have selected (path : Path) (member : path∈([[]] : List Path)) :
      initial.degreeAt path=some (Labelled.Label.atom 1) := by
    have same := List.mem_singleton.mp member
    subst path;rfl
  obtain ⟨edge,geometry,all⟩ := presentation.site.beta_uncreated_child_residuals (source:=initial) closed matching
    inputs flow rfl balance rfl transparency (relative presentation) (by simp [endpoint,Marked.Normal]) history
      complete.complete.1 (DegreeAligned.initial initial [[]]) selected
  let child := targetSelection ⟨[.fn],rfl⟩
  have occurrence : SourceSubterm [] .external result [.fn] [] (.appFn result.label)
      (.lam (.atom 4) (.var (.atom 5) 0)) := .fn .nil
  obtain ⟨_environment,context,_term⟩ := child.occurrence.same_occurrence occurrence
  have fromEq : (sourceEdge child.environment child.context child.term).fromPort=child.context := by
    cases child.term <;> rfl
  have role : SourceDeparture result .fn (sourceEdge child.environment child.context child.term).fromPort := by
    rw [fromEq,context];exact .fn
  have safe := marker_free [.fn] (by simp) child.term child.occurrence.lookup
  obtain ⟨oldPosition,_oldNode,_oldLookup,trace,relation⟩ := all [] .fn result rfl child role safe
  have origin : BetaNodePreimage (.var (.atom 2) 0)
      (.app (.atom 3) (.lam (.atom 4) (.var (.atom 5) 0)) (.lam (.atom 6) (.var (.atom 7) 0)))
      [] [.fn] [.arg,.fn] := .copied (q:=[]) (relative:=[.fn]) rfl rfl
  have known : BetaNodeHistoryPreimage history [.fn] [.arg,.fn] :=
    .one (step:=turn) rfl origin (.nil result [.fn])
  have same := trace.unique known
  subst oldPosition
  exact ⟨edge,geometry,relation (sourceSelection ⟨[.arg,.fn],rfl⟩)⟩
#print axioms actual_fiber
#print axioms targetChain
#print axioms actual_old_function_fragment
end Lamping.Checks.OldChainBetaFixture
