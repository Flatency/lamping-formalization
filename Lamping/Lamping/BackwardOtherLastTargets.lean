import Lamping.Lambda.SelectedOldOtherLastOrigins
import Lamping.Lambda.TargetHistoryPreimages
import Lamping.Lamping.SuccessfulEndpointIso
import Lamping.Lamping.RedexChainDegrees
namespace Lamping.Lambda.Labelled
open Graph Lamping.AG SyntaxIncidence

/-- Backward reading internally leaves exactly the two lambda origin cases.
The BODY variable's actual Target is the selected binder, not ARG ancestry. -/
theorem SelectedOldTurn.backward_other_last_target
    {F pre : List Path} {source middle target : LTerm} {degree : Label} {site : Path}
    {edge reader oldReader first last : Path}
    (event : SelectedOldTurn F source degree pre middle target site)
    (origin : BetaIncomingReadingOrigin event.body event.argument site edge reader oldReader first last)
    (reading : PrerequisiteReadsDirected target reader edge false) :
    ∃vertex : ProperPosition middle,Target middle last (some vertex) ∧
      (vertex.val=site ∨vertex.val=site++[.fn]) ∧
      PrerequisitePrefix middle last [] vertex.val ∧EndpointChain middle (some vertex) [site++[.fn]] := by
  have backward : edge=reader := reading.2
  have redex:=event.redex
  cases origin with
  | resultFunction result function =>
    have same:=backward.symm.trans (result.trans function)
    have length:=congrArg List.length same;simp at length
  | resultLambda result read oldLambda =>
    let app : ProperPosition middle:=⟨site,Or.inl ⟨event.beta,_,event.argument,redex⟩⟩
    exact ⟨app,Or.inl rfl,Or.inl rfl,.refl,.redex_app redex⟩
  | @copyFunction parent occurs copy read =>
    have same : reader=reader++[.fn] := by
      calc
        reader=edge := backward.symm
        _=site++(parent++[.fn]) := copy
        _=(site++parent)++[.fn] := (List.append_assoc _ _ _).symm
        _=reader++[.fn] := by rw [read]
    have length:=congrArg List.length same;simp at length
  | @copyLambda q stamp inner occurs copy read oldLambda =>
    have atLambda : middle.subterm (site++[.fn])=some (.lam degree event.body) := by rw [LTerm.subterm_append,redex];rfl
    let lam : ProperPosition middle:=⟨site++[.fn],Or.inr ⟨degree,event.body,atLambda⟩⟩
    have raw : subtermAt event.body.erase q=some (.var (binderDepth q)) := occurs
    rw [←LTerm.erase_subterm] at raw
    obtain ⟨varStamp,atVar⟩ : ∃varStamp,event.body.subterm q=some (.var varStamp (binderDepth q)) := by
      cases lookup : event.body.subterm q with
      | none => rw [lookup] at raw;cases raw
      | some node =>
        rw [lookup,Option.map_some] at raw
        cases node with
        | var a index => cases Option.some.inj raw;exact ⟨a,rfl⟩
        | app => cases raw
        | lam => cases raw
    have atLast : middle.subterm ((site++[.fn,.body])++q)=some (.var varStamp (binderDepth q)) := by
      rw [List.append_assoc,LTerm.subterm_append,redex];exact atVar
    have split : (site++[.fn,.body])++q=(site++[.fn])++(.body::q) := by simp only [List.append_assoc,List.cons_append,List.nil_append]
    exact ⟨lam,Or.inr ⟨varStamp,binderDepth q,degree,event.body,q,atLast,atLambda,split,rfl⟩,
      Or.inr rfl,.var atLast atLambda split rfl .refl,.redex_lam redex⟩

/-- The OWN otherLast node trace transports its actual proper Target.
A second vertex trace from selected APP/FN ancestry locks THIS old Target. -/
theorem SelectedOldTurn.backward_original_other_last_target
    {F pre : List Path} {source middle target : LTerm} {degree : Label} {site : Path}
    {edge reader oldReader first last oldPosition : Path}
    (event : SelectedOldTurn F source degree pre middle target site)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (origin : BetaIncomingReadingOrigin event.body event.argument site edge reader oldReader first last)
    (reading : PrerequisiteReadsDirected target reader edge false)
    (ownTrace : BetaNodeHistoryPreimage event.labels last oldPosition) :
    ∃name∈F,∃beta body argument originalNode vertex,
      source.subterm name=some (.app beta (.lam degree body) argument) ∧
      source.subterm oldPosition=some originalNode ∧Target source oldPosition (some vertex) ∧
      (vertex.val=name ∨vertex.val=name++[.fn]) ∧EndpointChain source (some vertex) [name++[.fn]] := by
  obtain ⟨midVertex,midTarget,position,zero,midChain⟩:=event.backward_other_last_target origin reading
  obtain ⟨oldVertex,oldTarget,vertexTrace⟩:=ownTrace.target_history midTarget
  obtain ⟨name,chosen,originalRedex,appTrace,fnTrace⟩:=event.beforeOld.selected_app_function_preimages event.labels event.member
  obtain ⟨beta,alpha,body,argument,atRedex⟩:=originalRedex
  have degreeEq:=selected name chosen
  simp only [LTerm.degreeAt,atRedex,Option.bind_some,LTerm.degree,Option.some.injEq] at degreeEq
  subst alpha
  obtain ⟨_,midNode,atLast⟩:=origin.old_prerequisite event.redex
  obtain ⟨originalPosition,originalNode,originalLookup,actualTrace⟩:=event.labels.node_preimage_from_lookup atLast
  have eq:=actualTrace.unique ownTrace
  subst originalPosition
  rcases position with appPosition | fnPosition
  · let vertex : ProperPosition source:=⟨name,Or.inl ⟨beta,_,argument,atRedex⟩⟩
    have ancestry : BetaNodeHistoryPreimage event.labels midVertex.val vertex.val := by rw [appPosition];exact appTrace
    have other : BetaVertexHistoryPreimage event.labels (some midVertex) (some vertex) := .proper ancestry
    have same:=vertexTrace.unique other
    rw [same] at oldTarget
    exact ⟨name,chosen,beta,body,argument,originalNode,vertex,atRedex,originalLookup,oldTarget,Or.inl rfl,.redex_app atRedex⟩
  · have fnLookup : source.subterm (name++[.fn])=some (.lam degree body) := by rw [LTerm.subterm_append,atRedex];rfl
    let vertex : ProperPosition source:=⟨name++[.fn],Or.inr ⟨degree,body,fnLookup⟩⟩
    have ancestry : BetaNodeHistoryPreimage event.labels midVertex.val vertex.val := by rw [fnPosition];exact fnTrace
    have other : BetaVertexHistoryPreimage event.labels (some midVertex) (some vertex) := .proper ancestry
    have same:=vertexTrace.unique other
    rw [same] at oldTarget
    exact ⟨name,chosen,beta,body,argument,originalNode,vertex,atRedex,originalLookup,oldTarget,Or.inr rfl,.redex_lam atRedex⟩

/-- Prefix times may differ: each OWN Target is locked independently in
the SAME relative source, then genuine selected singleton chains are compared. -/
theorem SelectedOldTurn.backward_other_last_pair_iso
    {F leftPre rightPre : List Path} {source leftMiddle leftTarget rightMiddle rightTarget : LTerm}
    {degree : Label} {leftSite rightSite : Path}
    {leftEdge leftReader leftOldReader leftFirst leftLast leftOld : Path}
    {rightEdge rightReader rightOldReader rightFirst rightLast rightOld : Path}
    (left : SelectedOldTurn F source degree leftPre leftMiddle leftTarget leftSite)
    (right : SelectedOldTurn F source degree rightPre rightMiddle rightTarget rightSite)
    (selected : ∀name∈F,source.degreeAt name=some degree) (closed : Closed source.erase)
    (leftOrigin : BetaIncomingReadingOrigin left.body left.argument leftSite leftEdge leftReader leftOldReader leftFirst leftLast)
    (rightOrigin : BetaIncomingReadingOrigin right.body right.argument rightSite rightEdge rightReader rightOldReader rightFirst rightLast)
    (leftRead : PrerequisiteReadsDirected leftTarget leftReader leftEdge false)
    (rightRead : PrerequisiteReadsDirected rightTarget rightReader rightEdge false)
    (leftTrace : BetaNodeHistoryPreimage left.labels leftLast leftOld)
    (rightTrace : BetaNodeHistoryPreimage right.labels rightLast rightOld) :
    ∃leftNode rightNode leftVertex rightVertex,
      source.subterm leftOld=some leftNode ∧source.subterm rightOld=some rightNode ∧
      Target source leftOld (some leftVertex) ∧Target source rightOld (some rightVertex) ∧
      SuccessfulEndpointIso source closed (some leftVertex) (some rightVertex) := by
  obtain ⟨ln,lm,lb,lbody,larg,lNode,lv,lRedex,lLookup,lTarget,lPosition,lChain⟩:=
    left.backward_original_other_last_target selected leftOrigin leftRead leftTrace
  obtain ⟨rn,rm,rb,rbody,rarg,rNode,rv,rRedex,rLookup,rTarget,rPosition,rChain⟩:=
    right.backward_original_other_last_target selected rightOrigin rightRead rightTrace
  have sameDegree : source.degreeAt ln=source.degreeAt rn := by
    rw [LTerm.degreeAt,lRedex,LTerm.degreeAt,rRedex];rfl
  have comparison:=(redex_chain_iso_iff_degree closed lRedex rRedex).mpr sameDegree
  exact ⟨lNode,rNode,lv,rv,lLookup,rLookup,lTarget,rTarget,[ln++[.fn]],[rn++[.fn]],lChain,rChain,comparison⟩
end Lamping.Lambda.Labelled
