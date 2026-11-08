import Lamping.Lamping.BackwardOtherLastTargets
import Lamping.Lamping.ActualCurrentAfterChains
import Lamping.Lamping.HistoryEndpointAvailability
namespace Lamping.Lambda.Labelled
open Graph Lamping.AG SyntaxIncidence

private theorem append_last_inj {p q : Path} {s u : Step} (eq : p++[s]=q++[u]) : p=q ∧s=u := by
  have h:=congrArg List.reverse eq
  simp only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append] at h
  have parts:=List.cons.inj h
  exact ⟨by simpa only [List.reverse_reverse] using congrArg List.reverse parts.2,parts.1⟩

private theorem unsnoc (q : Path) (nonempty : q≠[]) : ∃p s,q=p++[s] := by
  induction q with
  | nil => exact False.elim (nonempty rfl)
  | cons s tail ih =>
    cases tail with
    | nil => exact ⟨[],s,rfl⟩
    | cons u rest =>
      obtain ⟨p,v,eq⟩:=ih (by simp)
      exact ⟨s::p,v,by rw [eq];rfl⟩

private theorem actual_source_parent (lookup : t.subterm edge=some node) (split : edge=parent++[child]) :
    ∃vertex : ProperPosition t,Source t edge (some vertex) ∧vertex.val=parent := by
  have valid : (subtermAt t.erase edge).isSome := by rw [←LTerm.erase_subterm,lookup];rfl
  obtain ⟨vertex,spec⟩:=source_total t ⟨edge,valid⟩
  cases vertex with
  | none => have length:=congrArg List.length (spec.symm.trans split);simp at length
  | some vertex =>
    obtain ⟨step,sub,port,eq,atParent,departure⟩:=spec
    have parentEq := (append_last_inj (eq.symm.trans split)).1
    exact ⟨vertex,⟨step,sub,port,eq,atParent,departure⟩,parentEq⟩

private theorem backward_after_parent
    (reading : PrerequisiteReadsDirected t reader edge false)
    (remaining : PrerequisiteChain t reader (edge::after)) (nonempty : after≠[]) :
    ∃parent child stamp body,reader=parent++[child] ∧child≠.fn ∧edge=reader ∧
      t.subterm reader=some (.lam stamp body) ∧PrerequisiteChain t parent after := by
  have backward : edge=reader := reading.2
  rcases reading.1 with ⟨stamp,fn,arg,lookup,eq⟩ | ⟨stamp,body,lookup,eq⟩
  · have same:=backward.symm.trans eq
    have length:=congrArg List.length same;simp at length
  · rcases remaining.lambda_cases lookup with ⟨parent,a,arg,fn,atApp,split⟩ |
      ⟨parent,child,tail,split,notFn,listEq,actual⟩
    · have len:=congrArg List.length split
      simp only [List.length_cons,List.length_nil] at len
      exact False.elim (nonempty (List.length_eq_zero_iff.mp (by omega)))
    · have tails:after=tail := (List.cons.inj listEq).2
      exact ⟨parent,child,stamp,body,split,notFn,backward,lookup,tails ▸ actual⟩

/-- Nonterminal backward FAR Source availability. The q=[] copy case is
an actual selected lambda Source, not the current AFTER parent or a hom. -/
theorem SelectedOldTurn.backward_far_source_available
    {F pre : List Path} {source middle target : LTerm} {degree : Label} {site : Path}
    {edge reader oldReader first last : Path} {after : List Path}
    (event : SelectedOldTurn F source degree pre middle target site)
    (origin : BetaIncomingReadingOrigin event.body event.argument site edge reader oldReader first last)
    (reading : PrerequisiteReadsDirected target reader edge false)
    (remaining : PrerequisiteChain target reader (edge::after)) (nonempty : after≠[]) :
    ∃currentFar : ProperPosition target,∃far : ProperPosition middle,∃farEdges,
      Source target edge (some currentFar) ∧EndpointChain target (some currentFar) after ∧
      Source middle last (some far) ∧EndpointChain middle (some far) farEdges ∧
      (BetaVertexPreimage event.body event.argument site middle target (some currentFar) (some far) ∨far.val=site++[.fn]) := by
  obtain ⟨parent,child,stamp,inner,readerEq,notFn,backward,atReader,afterChain⟩:=backward_after_parent reading remaining nonempty
  have atEdge : target.subterm edge=some (.lam stamp inner) := backward ▸ atReader
  obtain ⟨currentFar,currentSource,currentEq⟩:=actual_source_parent atEdge (backward.trans readerEq)
  have currentChain : EndpointChain target (some currentFar) after := by change PrerequisiteChain target currentFar.val after;rw [currentEq];exact afterChain
  have redex:=event.redex
  cases origin with
  | resultFunction result function =>
    have same:=backward.symm.trans (result.trans function)
    have length:=congrArg List.length same;simp at length
  | resultLambda result read oldLambda =>
    have siteEq : site=parent++[child] := result.symm.trans (backward.trans readerEq)
    obtain ⟨far,farSource,farEq⟩:=actual_source_parent redex siteEq
    have outside : ¬∃relative,currentFar.val=site++relative := by
      rintro ⟨relative,eq⟩
      have len:=congrArg List.length eq
      rw [currentEq,siteEq] at len
      simp only [List.length_append,List.length_singleton] at len
      omega
    have nodeOrigin : BetaNodePreimage event.body event.argument site currentFar.val far.val := by
      rw [currentEq,farEq];exact .context (by simpa only [currentEq] using outside)
    obtain ⟨es,chain⟩:=event.turn.chain_reflect_at_preimage redex nodeOrigin currentChain
    exact ⟨currentFar,far,es,currentSource,currentChain,farSource,chain,Or.inl (.proper nodeOrigin)⟩
  | @copyFunction p occurs copy read =>
    have same : reader=reader++[.fn] := by
      calc reader=edge := backward.symm
           _=site++(p++[.fn]) := copy
           _=(site++p)++[.fn] := (List.append_assoc _ _ _).symm
           _=reader++[.fn] := by rw [read]
    have length:=congrArg List.length same;simp at length
  | @copyLambda q a b occurs copy read oldLambda =>
    by_cases empty : q=[]
    · have atLambda : middle.subterm (site++[.fn])=some (.lam degree event.body) := by rw [LTerm.subterm_append,redex];rfl
      let far : ProperPosition middle:=⟨site++[.fn],Or.inr ⟨degree,event.body,atLambda⟩⟩
      have farSource : Source middle ((site++[.fn,.body])++q) (some far) := by
        rw [empty,List.append_nil]
        exact ⟨.body,.lam degree event.body,_,by simp only [far,List.append_assoc,List.cons_append,List.nil_append],atLambda,.body⟩
      have farChain : EndpointChain middle (some far) [site++[Step.fn]] := by
        change PrerequisiteChain middle (site++[.fn]) [site++[.fn]]
        exact .redex_lam redex
      exact ⟨currentFar,far,[site++[Step.fn]],currentSource,currentChain,farSource,farChain,Or.inr rfl⟩
    · obtain ⟨p,s,qEq⟩:=unsnoc q empty
      have curParent : currentFar.val=site++p := by
        have eq : currentFar.val++[child]=(site++p)++[s] := by
          calc currentFar.val++[child]=parent++[child] := by rw [currentEq]
               _=reader := readerEq.symm
               _=edge := backward.symm
               _=site++q := copy
               _=(site++p)++[s] := by rw [qEq,List.append_assoc]
        exact (append_last_inj eq).1
      obtain ⟨_,lastNode,atLast⟩:=BetaIncomingReadingOrigin.old_prerequisite redex (BetaIncomingReadingOrigin.copyLambda occurs copy read oldLambda)
      have lastSplit : (site++[.fn,.body])++q=((site++[.fn,.body])++p)++[s] := by simp only [qEq,List.append_assoc]
      obtain ⟨far,farSource,farEq⟩:=actual_source_parent atLast lastSplit
      obtain ⟨step,sub,port,split,atFar,departure⟩:=farSource
      have atBody : event.body.subterm p=some sub := by
        rw [farEq,List.append_assoc,LTerm.subterm_append,redex] at atFar
        exact atFar
      have nonselected : ∀stamp,sub≠.var stamp (binderDepth p) := by
        intro stamp eq;cases departure <;> cases eq
      have nodeOrigin : BetaNodePreimage event.body event.argument site currentFar.val far.val := by
        rw [curParent,farEq];exact .retained atBody nonselected
      obtain ⟨es,chain⟩:=event.turn.chain_reflect_at_preimage redex nodeOrigin currentChain
      exact ⟨currentFar,far,es,currentSource,currentChain,⟨step,sub,port,split,atFar,departure⟩,chain,Or.inl (.proper nodeOrigin)⟩

/-- Original FAR Source availability is reflected along the OWN actual edge
trace. A Source vertex history is claimed only for an uncreated lineage. -/
theorem SelectedOldTurn.backward_original_far_available
    {F pre : List Path} {source middle target : LTerm} {degree : Label} {site : Path}
    {edge reader oldReader first last oldPosition : Path} {after : List Path}
    (event : SelectedOldTurn F source degree pre middle target site)
    (origin : BetaIncomingReadingOrigin event.body event.argument site edge reader oldReader first last)
    (reading : PrerequisiteReadsDirected target reader edge false)
    (remaining : PrerequisiteChain target reader (edge::after)) (nonempty : after≠[])
    (ownTrace : BetaNodeHistoryPreimage event.labels last oldPosition) :
    ∃currentFar : ProperPosition target,∃far : ProperPosition middle,
      ∃original oldFar oldEdges,
      Source target edge (some currentFar) ∧EndpointChain target (some currentFar) after ∧
      Source middle last (some far) ∧source.subterm oldPosition=some original ∧
      Source source oldPosition (some oldFar) ∧EndpointChain source (some oldFar) oldEdges ∧
      (UncreatedNodeHistoryPreimage event.labels last oldPosition →
        BetaVertexHistoryPreimage event.labels (some far) (some oldFar)) := by
  obtain ⟨currentFar,far,farEdges,currentSource,currentChain,farSource,farChain,relation⟩:=
    event.backward_far_source_available origin reading remaining nonempty
  obtain ⟨near,nearTarget,position,zero,nearChain⟩:=event.backward_other_last_target origin reading
  obtain ⟨_,lastNode,atLast⟩:=origin.old_prerequisite event.redex
  obtain ⟨original,oldFar,oldNear,oldEdges,oldNearEdges,originalLookup,oldSource,oldTarget,oldFarChain,oldNearChain⟩:=
    history_edge_endpoint_availability ownTrace atLast farSource nearTarget farChain nearChain
  cases oldFar with
  | none => exact False.elim oldFarChain
  | some oldFar =>
    refine ⟨currentFar,far,original,oldFar,oldEdges,currentSource,currentChain,farSource,originalLookup,oldSource,oldFarChain,?_⟩
    intro uncreated
    obtain ⟨original',vertex,lookup',sameLabel,source',trace⟩:=uncreated.source_history atLast farSource
    have eq:=Source.unique source' oldSource
    rw [eq] at trace
    exact trace
end Lamping.Lambda.Labelled
