import Lamping.Lamping.CreatedReadingIncidenceExpansion
import Lamping.Lambda.TargetHistoryPreimages

namespace Lamping.Lambda.Labelled
open SyntaxIncidence
variable {source middle target : LTerm}

private theorem trace_append
    {firstHistory : History ps source middle} {lastHistory : History qs middle target}
    (first : BetaNodeHistoryPreimage firstHistory middleEdge oldEdge)
    (last : BetaNodeHistoryPreimage lastHistory edge middleEdge) :
    BetaNodeHistoryPreimage (firstHistory.append lastHistory) edge oldEdge := by
  induction first with
  | nil => exact last
  | @one _ _ _ _ _ _ _ _ _ _ _ _ step _ redex origin tail ih =>
    exact .one (step:=step) redex origin (ih last)

private theorem trace_chain
    {labels : History ps source target} (trace : BetaNodeHistoryPreimage labels edge oldEdge)
    (chain : PrerequisiteChain target edge es) :
    ∃ oldEdges,PrerequisiteChain source oldEdge oldEdges := by
  induction trace generalizing es with
  | nil => exact ⟨es,chain⟩
  | @one _ _ _ _ _ _ _ _ _ _ _ _ step _ redex origin tail ih =>
    obtain ⟨middleEdges,middleChain⟩ := ih chain
    exact step.chain_reflect_at_preimage redex origin middleChain

def SelectedOldTurn.final_history
    (event : SelectedOldTurn F source degree pre middle target site) :
    History (pre++[site]) source target :=
  event.labels.append (.cons event.turn (.nil _))

/-- A forward RESULTvar0 has its node/FAR ancestry in ARG, while its triple
LAST remains the selected BODY variable. No label identifies this position. -/
private theorem forward_node_origin
    (event : SelectedOldTurn F source degree pre middle target site)
    (origin : BetaIncomingReadingOrigin event.body event.argument site edge reader oldReader first last)
    (reading : PrerequisiteReadsDirected target reader edge true) :
    ∃ middlePosition,
      BetaNodePreimage event.body event.argument site edge middlePosition ∧
      (middlePosition=last ∨∃stamp,event.body=.var stamp 0 ∧middlePosition=site++[.arg]) := by
  cases origin with
  | resultFunction result function =>
    by_cases zero : ∃stamp,event.body=.var stamp 0
    · obtain ⟨stamp,shape⟩ := zero
      refine ⟨site++[.arg],?_,Or.inr ⟨stamp,shape,rfl⟩⟩
      rw [result]
      have occurs : ArgumentOccurrence event.body.erase [] := by rw [shape]; rfl
      have rootLookup : event.argument.subterm []=some event.argument := by cases event.argument <;> rfl
      simpa only [List.append_nil] using
        (BetaNodePreimage.copied occurs rootLookup :
          BetaNodePreimage event.body event.argument site ((site++[])++[]) ((site++[.arg])++[]))
    · refine ⟨site++[.fn,.body],?_,Or.inl rfl⟩
      rw [result]
      have rootLookup : event.body.subterm []=some event.body := by cases event.body <;> rfl
      simpa only [List.append_nil] using
        (BetaNodePreimage.retained rootLookup (by intro stamp shape;exact zero ⟨stamp,shape⟩) :
          BetaNodePreimage event.body event.argument site (site++[]) ((site++[.fn,.body])++[]))
  | @copyFunction parent occurs copy read =>
    refine ⟨site++[.arg],?_,Or.inl rfl⟩
    rw [copy]
    have rootLookup : event.argument.subterm []=some event.argument := by cases event.argument <;> rfl
    simpa only [List.append_nil] using
      (BetaNodePreimage.copied occurs rootLookup :
        BetaNodePreimage event.body event.argument site ((site++(parent++[.fn]))++[]) ((site++[.arg])++[]))
  | resultLambda result read oldLambda =>
    have same : edge=edge++[.fn] := by simpa only [read,←result] using reading.2
    have lengths := congrArg List.length same
    simp at lengths
  | copyLambda occurs copy read oldLambda =>
    have same : edge=edge++[.fn] := by simpa only [read] using reading.2
    have lengths := congrArg List.length same
    simp at lengths

/-- Derived final-event forward data. Literal node starts and their proper
TARGET vertices are separate, including a lexical variable-to-binder jump. -/
structure ForwardExpandedFarOutput
    (event : SelectedOldTurn F source degree pre middle target site)
    (reader edge oldReader first last : Path) (after : List Path) where
  currentTail : PrerequisiteChain target edge after
  middlePosition : Path
  middleNode : LTerm
  middleLookup : middle.subterm middlePosition=some middleNode
  nodeOrigin : BetaNodePreimage event.body event.argument site edge middlePosition
  positionKind : middlePosition=last ∨∃stamp,event.body=.var stamp 0 ∧middlePosition=site++[.arg]
  middleEdges : List Path
  middleChain : PrerequisiteChain middle middlePosition middleEdges
  currentFar : Vertex target
  currentTarget : Target target edge currentFar
  expandedNear : Vertex middle
  expandedFar : Vertex middle
  expandedEdges : List Path
  expandedDirections : List Bool
  expandedChase : IncidenceChase middle expandedNear expandedEdges expandedDirections expandedFar
  expansion : CreatedReadingExpansion event.body site first last true expandedEdges expandedDirections
  expandedTarget : Target middle middlePosition expandedFar
  farOrigin : BetaVertexPreimage event.body event.argument site middle target currentFar expandedFar
  sourcePosition : Path
  sourceNode : LTerm
  sourceLookup : source.subterm sourcePosition=some sourceNode
  prefixTrace : BetaNodeHistoryPreimage event.labels middlePosition sourcePosition
  currentTrace : BetaNodeHistoryPreimage event.final_history edge sourcePosition
  sourceEdges : List Path
  sourceChain : PrerequisiteChain source sourcePosition sourceEdges
  sourceFar : Vertex source
  sourceTarget : Target source sourcePosition sourceFar
  sourceFarHistory : BetaVertexHistoryPreimage event.labels expandedFar sourceFar
  sourceFarChain : Lamping.AG.EndpointChain source sourceFar sourceEdges

/-- Reflect the actual nonempty forward suffix, lock its middle node to the
CP44 EXPANDED endpoint, and retain its OWN original source chain/trace. -/
theorem SelectedOldTurn.forward_expanded_far_output
    (event : SelectedOldTurn F source degree pre middle target site)
    (closed : Closed source.erase)
    (origin : BetaIncomingReadingOrigin event.body event.argument site edge reader oldReader first last)
    (reading : PrerequisiteReadsDirected target reader edge true)
    (lookup : target.subterm edge=some current)
    (remaining : PrerequisiteChain target reader (edge::after)) (more : after≠[]) :
    Nonempty (ForwardExpandedFarOutput event reader edge oldReader first last after) := by
  have readerApp : ∃stamp fn arg,target.subterm reader=some (.app stamp fn arg) := by
    rcases reading.1 with ⟨stamp,fn,arg,lookup,_⟩ | ⟨stamp,body,lookup,split⟩
    · exact ⟨stamp,fn,arg,lookup⟩
    · have lengths:=congrArg List.length (split.symm.trans reading.2)
      simp at lengths
  obtain ⟨stamp,fn,arg,atReader⟩:=readerApp
  have currentTail : PrerequisiteChain target edge after := by
    rcases remaining.app_cases atReader with ⟨l,b,shape,split⟩ | ⟨notLambda,tail,split,actual⟩
    · have parts:=List.cons.inj split
      exact False.elim (more parts.2)
    · have parts:=List.cons.inj split
      rw [reading.2,parts.2];exact actual
  obtain ⟨middlePosition,nodeOrigin,positionKind⟩:=forward_node_origin event origin reading
  obtain ⟨middleNode,middleLookup,_⟩:=event.turn.preimage_node_constructor event.redex nodeOrigin lookup
  obtain ⟨middleEdges,middleChain⟩:=event.turn.chain_reflect_at_preimage event.redex nodeOrigin currentTail
  have targetClosed:=event.final_history.closed closed
  let position : Edge target:=⟨edge,by rw [←LTerm.erase_subterm,lookup];rfl⟩
  obtain ⟨currentFar,currentTarget⟩:=target_total target targetClosed position
  let near : ProperPosition target:=⟨reader,Or.inl ⟨stamp,fn,arg,atReader⟩⟩
  obtain ⟨expandedNear,expandedFar,expandedEdges,expandedDirections,_oldNearTarget,_nearOrigin,
      expandedChase,farOrigin,_lastIncidence,expansion⟩:=
    origin.incidence_expansion (currentFar:=currentFar) event.turn event.redex reading lookup
      (show Target target reader (some near) from Or.inl rfl) currentTarget
  obtain ⟨middleFar,middleTarget,middleOrigin⟩:=
    event.turn.beta_incidence_target_preimage event.redex nodeOrigin currentTarget
  have same:=farOrigin.unique middleOrigin
  have expandedTarget : Target middle middlePosition expandedFar := by rw [same];exact middleTarget
  obtain ⟨sourcePosition,sourceNode,sourceLookup,prefixTrace⟩:=event.labels.node_preimage_from_lookup middleLookup
  have currentTrace : BetaNodeHistoryPreimage event.final_history edge sourcePosition :=
    trace_append prefixTrace (.one (step:=event.turn) event.redex nodeOrigin (.nil target edge))
  obtain ⟨sourceEdges,sourceChain⟩:=trace_chain prefixTrace middleChain
  obtain ⟨sourceFar,sourceTarget,sourceFarHistory⟩:=prefixTrace.target_history expandedTarget
  have sourceFarChain : Lamping.AG.EndpointChain source sourceFar sourceEdges := by
    cases sourceFar with
    | none => exact False.elim sourceTarget
    | some vertex => exact sourceChain.at_actual_target sourceTarget
  exact ⟨{
    currentTail:=currentTail,middlePosition:=middlePosition,middleNode:=middleNode,middleLookup:=middleLookup
    nodeOrigin:=nodeOrigin,positionKind:=positionKind,middleEdges:=middleEdges,middleChain:=middleChain
    currentFar:=currentFar,currentTarget:=currentTarget,expandedNear:=expandedNear,expandedFar:=expandedFar
    expandedEdges:=expandedEdges,expandedDirections:=expandedDirections,expandedChase:=expandedChase,expansion:=expansion
    expandedTarget:=expandedTarget,farOrigin:=farOrigin,sourcePosition:=sourcePosition,sourceNode:=sourceNode
    sourceLookup:=sourceLookup,prefixTrace:=prefixTrace,currentTrace:=currentTrace,sourceEdges:=sourceEdges
    sourceChain:=sourceChain,sourceFar:=sourceFar,sourceTarget:=sourceTarget,sourceFarHistory:=sourceFarHistory
    sourceFarChain:=sourceFarChain }⟩

#print axioms SelectedOldTurn.forward_expanded_far_output
end Lamping.Lambda.Labelled
