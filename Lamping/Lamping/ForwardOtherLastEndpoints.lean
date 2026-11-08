import Lamping.Lamping.BackwardOtherLastFarSources
namespace Lamping.Lambda.Labelled
open Graph Lamping.AG SyntaxIncidence

private theorem forward_app
    (reading : PrerequisiteReadsDirected t reader edge true) :
    ∃stamp fn arg,t.subterm reader=some (.app stamp fn arg) ∧edge=reader++[.fn] := by
  rcases reading.1 with app | ⟨stamp,body,lookup,same⟩
  · exact app
  · have len:=congrArg List.length (same.symm.trans reading.2)
    simp at len

/-- The real forward continuation is the nonempty AFTER, or the selected
terminal lambda's singleton. An empty AFTER never supplies a new reader. -/
theorem PrerequisiteChain.forward_target_available
    (reading : PrerequisiteReadsDirected t reader edge true)
    (remaining : PrerequisiteChain t reader (edge::after)) :
    ∃far : ProperPosition t,Target t edge (some far) ∧
      ((after≠[] ∧EndpointChain t (some far) after) ∨
       (after=[] ∧far.val=edge ∧EndpointChain t (some far) [edge])) := by
  obtain ⟨stamp,fn,arg,lookup,edgeEq⟩:=forward_app reading
  rcases remaining.app_cases lookup with ⟨l,b,shape,split⟩ | ⟨notLambda,tail,split,actual⟩
  · have parts:=List.cons.inj split
    have afterEq : after=[] := parts.2
    have atLambda : t.subterm edge=some (.lam l b) := by
      rw [edgeEq,LTerm.subterm_append,lookup,shape];rfl
    let far : ProperPosition t:=⟨edge,Or.inr ⟨l,b,atLambda⟩⟩
    refine ⟨far,Or.inl rfl,Or.inr ⟨afterEq,rfl,?_⟩⟩
    change PrerequisiteChain t edge [edge]
    rw [edgeEq]
    exact .redex_lam (by simpa only [shape] using lookup)
  · have parts:=List.cons.inj split
    have chain : PrerequisiteChain t edge after := by rw [edgeEq,parts.2];exact actual
    obtain ⟨far,vertices,toFar,walk,nodup,cover⟩:=chain.incidence_path
    refine ⟨far,toFar,Or.inl ⟨?_,chain.at_actual_target toFar⟩⟩
    intro empty
    have noempty:=chain.nonempty
    exact noempty empty

/-- The forward NEAR endpoint is THIS selected lambda (BODY incoming) or
THIS selected application (ARG incoming), with its actual Source incidence. -/
theorem SelectedOldTurn.forward_other_last_near_source
    {F pre : List Path} {source middle target : LTerm} {degree : Label} {site : Path}
    {edge reader oldReader first last : Path}
    (event : SelectedOldTurn F source degree pre middle target site)
    (origin : BetaIncomingReadingOrigin event.body event.argument site edge reader oldReader first last)
    (reading : PrerequisiteReadsDirected target reader edge true) :
    ∃near : ProperPosition middle,Source middle last (some near) ∧
      (near.val=site++[.fn] ∨near.val=site) ∧
      EndpointChain middle (some near) [site++[.fn]] := by
  have forward : edge=reader++[.fn] := reading.2
  cases origin with
  | resultFunction result function =>
    have lookup : middle.subterm (site++[.fn])=some (.lam degree event.body) := by
      rw [LTerm.subterm_append,event.redex];rfl
    let near : ProperPosition middle:=⟨site++[.fn],Or.inr ⟨degree,event.body,lookup⟩⟩
    refine ⟨near,?_,Or.inl rfl,?_⟩
    · exact ⟨.body,.lam degree event.body,.lamBody degree,by simp only [near,List.append_assoc,List.cons_append,List.nil_append],lookup,.body⟩
    · exact .redex_lam event.redex
  | resultLambda result read oldLambda =>
    have same : edge=edge++[.fn] := by simpa only [read,←result] using forward
    have len:=congrArg List.length same;simp at len
  | copyFunction occurs copy read =>
    let near : ProperPosition middle:=⟨site,Or.inl ⟨event.beta,.lam degree event.body,event.argument,event.redex⟩⟩
    exact ⟨near,⟨.arg,_,.appArg event.beta,rfl,event.redex,.arg⟩,Or.inr rfl,.redex_app event.redex⟩
  | copyLambda occurs copy read oldLambda =>
    have same : edge=edge++[.fn] := by simpa only [read] using forward
    have len:=congrArg List.length same;simp at len

private theorem body_zero_target
    (redex : middle.subterm site=some (.app beta (.lam degree (.var stamp 0)) argument)) :
    ∃far : ProperPosition middle,Target middle (site++[.fn,.body]) (some far) ∧
      EndpointChain middle (some far) [site++[.fn]] ∧far.val=site++[.fn] := by
  have lookup : middle.subterm (site++[.fn])=some (.lam degree (.var stamp 0)) := by
    rw [LTerm.subterm_append,redex];rfl
  let far : ProperPosition middle:=⟨site++[.fn],Or.inr ⟨degree,_,lookup⟩⟩
  refine ⟨far,Or.inr ⟨stamp,0,degree,.var stamp 0,[],?_,lookup,?_,rfl⟩,.redex_lam redex,rfl⟩
  · rw [LTerm.subterm_append,redex];rfl
  · simp only [far,List.append_assoc,List.cons_append,List.nil_append]

/-- Actual forward FAR Target availability. Retained BODY and copied ARG
use THIS target preimage; BODY variable zero uses its actual selected binder.
The continuation output distinguishes genuine AFTER from terminal singleton. -/
theorem SelectedOldTurn.forward_other_last_far_target
    {F pre : List Path} {source middle target : LTerm} {degree : Label} {site : Path}
    {edge reader oldReader first last : Path} {after : List Path}
    (event : SelectedOldTurn F source degree pre middle target site)
    (origin : BetaIncomingReadingOrigin event.body event.argument site edge reader oldReader first last)
    (reading : PrerequisiteReadsDirected target reader edge true)
    (remaining : PrerequisiteChain target reader (edge::after)) :
    ∃currentFar : ProperPosition target,∃far : ProperPosition middle,∃farEdges,
      Target target edge (some currentFar) ∧
      ((after≠[] ∧EndpointChain target (some currentFar) after) ∨
       (after=[] ∧currentFar.val=edge ∧EndpointChain target (some currentFar) [edge])) ∧
      Target middle last (some far) ∧EndpointChain middle (some far) farEdges ∧
      (BetaVertexPreimage event.body event.argument site middle target (some currentFar) (some far) ∨far.val=site++[.fn]) := by
  obtain ⟨currentFar,currentTarget,continuation⟩:=remaining.forward_target_available reading
  have currentAvailable : ∃es,EndpointChain target (some currentFar) es := by
    rcases continuation with ⟨_,chain⟩ | ⟨_,_,chain⟩
    · exact ⟨after,chain⟩
    · exact ⟨[edge],chain⟩
  obtain ⟨es,currentChain⟩:=currentAvailable
  have reflect (nodeOrigin : BetaNodePreimage event.body event.argument site edge last) :
      ∃far : ProperPosition middle,∃farEdges,Target middle last (some far) ∧
        EndpointChain middle (some far) farEdges ∧
        BetaVertexPreimage event.body event.argument site middle target (some currentFar) (some far) := by
    obtain ⟨oldVertex,oldTarget,vertexOrigin⟩:=event.turn.beta_incidence_target_preimage event.redex nodeOrigin currentTarget
    obtain ⟨oldEdges,oldChain⟩:=endpoint_available_at_beta_preimage event.turn event.redex vertexOrigin currentChain
    cases oldVertex with
    | none => exact False.elim oldTarget
    | some far => exact ⟨far,oldEdges,oldTarget,oldChain,vertexOrigin⟩
  cases origin with
  | resultFunction result function =>
    by_cases zero : ∃stamp,event.body=.var stamp 0
    · obtain ⟨stamp,bodyEq⟩:=zero
      obtain ⟨far,toFar,chain,farEq⟩:=body_zero_target (bodyEq ▸ event.redex)
      exact ⟨currentFar,far,_,currentTarget,continuation,toFar,chain,Or.inr farEq⟩
    · have bodyLookup : event.body.subterm []=some event.body := by cases event.body <;>rfl
      have nodeOrigin : BetaNodePreimage event.body event.argument site edge (site++[.fn,.body]) := by
        rw [result]
        simpa only [List.append_nil] using
          (BetaNodePreimage.retained bodyLookup (by intro stamp eq;exact zero ⟨stamp,eq⟩) :
            BetaNodePreimage event.body event.argument site (site++[]) ((site++[.fn,.body])++[]))
      obtain ⟨far,farEdges,toFar,chain,vertexOrigin⟩:=reflect nodeOrigin
      exact ⟨currentFar,far,farEdges,currentTarget,continuation,toFar,chain,Or.inl vertexOrigin⟩
  | resultLambda result read oldLambda =>
    have same : edge=edge++[.fn] := by simpa only [read,←result] using (reading.2 : edge=reader++[.fn])
    have len:=congrArg List.length same;simp at len
  | @copyFunction parent occurs copy read =>
    have lookup : event.argument.subterm []=some event.argument := by cases event.argument <;>rfl
    have nodeOrigin : BetaNodePreimage event.body event.argument site edge (site++[.arg]) := by
      rw [copy]
      simpa only [List.append_nil] using
        (BetaNodePreimage.copied occurs lookup :
          BetaNodePreimage event.body event.argument site ((site++(parent++[.fn]))++[]) ((site++[.arg])++[]))
    obtain ⟨far,farEdges,toFar,chain,vertexOrigin⟩:=reflect nodeOrigin
    exact ⟨currentFar,far,farEdges,currentTarget,continuation,toFar,chain,Or.inl vertexOrigin⟩
  | copyLambda occurs copy read oldLambda =>
    have same : edge=edge++[.fn] := by simpa only [read] using reading.2
    have len:=congrArg List.length same;simp at len
/-- Both endpoints reflected through THIS old-last node history. This is
availability only, not a created Source hom or paired endpoint isomorphism. -/
theorem SelectedOldTurn.forward_original_other_last_available
    {F pre : List Path} {source middle target : LTerm} {degree : Label} {site : Path}
    {edge reader oldReader first last oldEdge : Path} {after : List Path}
    (event : SelectedOldTurn F source degree pre middle target site)
    (origin : BetaIncomingReadingOrigin event.body event.argument site edge reader oldReader first last)
    (reading : PrerequisiteReadsDirected target reader edge true)
    (remaining : PrerequisiteChain target reader (edge::after))
    (ownTrace : BetaNodeHistoryPreimage event.labels last oldEdge) :
    ∃original oldNear oldFar nearEdges farEdges,
      source.subterm oldEdge=some original ∧Source source oldEdge oldNear ∧
      Target source oldEdge oldFar ∧EndpointChain source oldNear nearEdges ∧
      EndpointChain source oldFar farEdges := by
  obtain ⟨near,fromNear,selected,nearChain⟩:=event.forward_other_last_near_source origin reading
  obtain ⟨currentFar,far,farEdges,currentTarget,continuation,toFar,farChain,ancestry⟩:=
    event.forward_other_last_far_target origin reading remaining
  obtain ⟨lastNode,atLast⟩:= (origin.old_prerequisite event.redex).2
  exact history_edge_endpoint_availability ownTrace atLast fromNear toFar nearChain farChain
end Lamping.Lambda.Labelled
