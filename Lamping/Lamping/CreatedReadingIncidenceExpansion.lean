import Lamping.Lamping.ChainIncidenceWalk
import Lamping.Lamping.ForwardOtherLastEndpoints
namespace Lamping.Lambda.Labelled
open SyntaxIncidence
variable {source target : LTerm}

/-- Literal expansion of the actual created reading. Repeated selected edges
and variable loops are retained; this is not a prerequisite whole chain. -/
inductive CreatedReadingExpansion (body : LTerm) (site : Path) :
    Path →Path →Bool →List Path →List Bool →Prop where
  | resultFunction (other : ∀stamp,body≠.var stamp 0) :
      CreatedReadingExpansion body site site (site++[.fn,.body]) true
        [site,site++[.fn],site++[.fn,.body]] [true,true,true]
  | resultOverlap (shape : body=.var stamp 0) :
      CreatedReadingExpansion body site site (site++[.fn,.body]) true
        [site,site++[.fn],site++[.fn,.body],site++[.fn],site++[.arg]] [true,true,true,false,true]
  | copyFunction : CreatedReadingExpansion body site first (site++[.arg]) true
      [first,site++[.fn],site++[.arg]] [true,false,true]
  | resultLambda : CreatedReadingExpansion body site (site++[.fn,.body]) site false
      [site++[.fn,.body],site++[.fn],site] [false,false,false]
  | copyLambda (nonroot : q≠[]) :
      CreatedReadingExpansion body site (site++[.arg]) ((site++[.fn,.body])++q) false
        [site++[.arg],site++[.fn],(site++[.fn,.body])++q] [false,true,false]
  | copyOverlap : CreatedReadingExpansion body site (site++[.arg]) (site++[.fn,.body]) false
      [site++[.arg],site++[.fn],site++[.fn,.body],site++[.fn],site] [false,true,false,false,false]

private theorem zero_target_forward (segment : PrerequisitePrefix t p es q)
    (empty : es=[]) (atStart : Target t p v) : Target t q v := by
  induction segment generalizing v with
  | refl => exact atStart
  | app _ _ _ _ => cases empty
  | lam _ _ _ _ => cases empty
  | @var leaf stamp index parent origin body rest edges finish lookup binder split depth tail ih =>
    let actual : ProperPosition t:=⟨parent,Or.inr ⟨origin,body,binder⟩⟩
    have same:=Target.unique atStart (show Target t leaf (some actual) from
      Or.inr ⟨stamp,index,origin,body,rest,lookup,binder,split,depth⟩)
    subst v
    exact ih empty (Or.inl rfl)

private theorem reading_near (reading : PrerequisiteReadsDirected t p e d)
    (atStart : Target t p v) : if d then Source t e v else Target t e v := by
  cases d with
  | false =>
    have equal : e=p:=reading.2
    simpa only [equal,if_false,Bool.false_eq_true] using atStart
  | true =>
    rcases reading.1 with ⟨stamp,fn,arg,lookup,split⟩ | ⟨stamp,body,lookup,split⟩
    · let actual : ProperPosition t:=⟨p,Or.inl ⟨stamp,fn,arg,lookup⟩⟩
      have same:=Target.unique atStart (show Target t p (some actual) from Or.inl rfl)
      subst v
      exact ⟨.fn,_,_,reading.2,lookup,.fn⟩
    · have lengths:=congrArg List.length (split.symm.trans reading.2)
      simp at lengths

private theorem last_parent {p q : Path} {s u : Step} (same : p++[s]=q++[u]) : p=q := by
  have sizes:=congrArg List.length same
  have lengths : p.length=q.length := by simpa using sizes
  exact List.append_inj_left same lengths

/-- A context incoming source is reflected by its literal parent, including
external none. This does not assert a created-source map to otherLast. -/
private theorem context_source (_step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (currentSource : Source target site v) :
    ∃old,Source source site old ∧BetaVertexPreimage body argument site source target v old := by
  obtain ⟨old,oldSource⟩:=source_total source ⟨site,by rw [←LTerm.erase_subterm,redex];rfl⟩
  cases v with
  | none =>
    cases old with
    | none => exact ⟨none,oldSource,.boundary⟩
    | some parent =>
      obtain ⟨s,child,port,split,_,_⟩:=oldSource
      have length:=congrArg List.length (currentSource.symm.trans split)
      simp at length
  | some parent =>
    obtain ⟨s,child,port,split,atParent,departure⟩:=currentSource
    cases old with
    | none => have length:=congrArg List.length (oldSource.symm.trans split);simp at length
    | some oldParent =>
      obtain ⟨u,oldChild,oldPort,oldSplit,oldAt,oldDeparture⟩:=oldSource
      have parents:=last_parent (split.symm.trans oldSplit)
      have outside : ¬∃relative,parent.val=site++relative := by
        rintro ⟨relative,equal⟩
        have length:=congrArg List.length equal
        have siteLength:=congrArg List.length split
        simp only [List.length_append,List.length_singleton] at length siteLength
        omega
      refine ⟨some oldParent,⟨u,oldChild,oldPort,oldSplit,oldAt,oldDeparture⟩,.proper ?_⟩
      rw [←parents]
      exact .context outside

private theorem unsnoc (q : Path) (positive : q≠[]) : ∃p s,q=p++[s] := by
  induction q with
  | nil => exact False.elim (positive rfl)
  | cons s tail ih =>
    cases tail with
    | nil => exact ⟨[],s,rfl⟩
    | cons u rest => obtain ⟨p,v,split⟩:=ih (by simp);exact ⟨s::p,v,by rw [split];rfl⟩

private theorem copied_source (_step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (_occurs : ArgumentOccurrence body.erase q) (positive : q≠[])
    (oldLookup : source.subterm ((site++[.fn,.body])++q)=some oldNode)
    (currentSource : Source target (site++q) v) :
    ∃old,Source source ((site++[.fn,.body])++q) old ∧
      BetaVertexPreimage body argument site source target v old := by
  obtain ⟨p,s,qEq⟩:=unsnoc q positive
  obtain ⟨old,oldSource⟩:=source_total source ⟨_,by rw [←LTerm.erase_subterm,oldLookup];rfl⟩
  cases v with
  | none =>
    have length:=congrArg List.length currentSource
    simp only [List.length_append,List.length_nil] at length
    exact False.elim (positive (List.length_eq_zero_iff.mp (by omega)))
  | some parent =>
    obtain ⟨u,child,port,split,atParent,departure⟩:=currentSource
    have currentParent : parent.val=site++p := last_parent (by simpa only [qEq,List.append_assoc] using split.symm)
    cases old with
    | none => have length:=congrArg List.length oldSource;simp only [List.length_append,List.length_cons,List.length_nil] at length;omega
    | some oldParent =>
      obtain ⟨u,oldChild,oldPort,oldSplit,oldAt,oldDeparture⟩:=oldSource
      have oldParentEq : oldParent.val=(site++[.fn,.body])++p := last_parent (by simpa only [qEq,List.append_assoc] using oldSplit.symm)
      have bodyAt : body.subterm p=some oldChild := by
        rw [oldParentEq,List.append_assoc,LTerm.subterm_append,redex] at oldAt
        exact oldAt
      have proper : ∀stamp,oldChild≠.var stamp (binderDepth p) := by
        intro stamp impossible;cases oldDeparture <;> cases impossible
      refine ⟨some oldParent,⟨u,oldChild,oldPort,oldSplit,oldAt,oldDeparture⟩,.proper ?_⟩
      rw [currentParent,oldParentEq]
      exact .retained bodyAt proper

/-- The GIVEN actual created reading expands into a literal three/five-edge
incidence chase with genuine endpoint preimages. Far means the endpoint of
the full expansion, which differs from triple otherLast at root overlaps. -/
theorem BetaIncomingReadingOrigin.incidence_expansion
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (origin : BetaIncomingReadingOrigin body argument site edge reader oldReader first last)
    (reading : PrerequisiteReadsDirected target reader edge forward)
    (_lookup : target.subterm edge=some current)
    (near : Target target reader currentNear)
    (far : if forward then Target target edge currentFar else Source target edge currentFar) :
    ∃oldNear oldFar es ds,
      Target source oldReader oldNear ∧
      BetaVertexPreimage body argument site source target currentNear oldNear ∧
      IncidenceChase source oldNear es ds oldFar ∧
      BetaVertexPreimage body argument site source target currentFar oldFar ∧
      (if forward then Target source (es.getLastD []) oldFar else Source source (es.getLastD []) oldFar) ∧
      CreatedReadingExpansion body site first last forward es ds := by
  obtain ⟨oldNear,oldNearTarget,nearOrigin⟩:=step.beta_incidence_target_preimage redex origin.middle_preimage near
  obtain ⟨readAt,zero,oldRead⟩:=origin.old_directed_reading redex reading
  have firstNear:=reading_near oldRead (zero_target_forward zero rfl oldNearTarget)
  have atLambda : source.subterm (site++[.fn])=some (.lam alpha body) := by rw [LTerm.subterm_append,redex];rfl
  let app : ProperPosition source:=⟨site,Or.inl ⟨beta,.lam alpha body,argument,redex⟩⟩
  let lam : ProperPosition source:=⟨site++[.fn],Or.inr ⟨alpha,body,atLambda⟩⟩
  have fnSource : Source source (site++[.fn]) (some app):=⟨.fn,_,_,rfl,redex,.fn⟩
  have fnTarget : Target source (site++[.fn]) (some lam):=Or.inl rfl
  have bodySource : Source source (site++[.fn,.body]) (some lam):=⟨.body,_,_,by simp only [lam,List.append_assoc,List.cons_append,List.nil_append],atLambda,.body⟩
  have argSource : Source source (site++[.arg]) (some app):=⟨.arg,_,_,rfl,redex,.arg⟩
  have firstTarget : Target source site (some app):=Or.inl rfl
  cases origin with
  | resultFunction result function =>
    have direction : forward=true := by
      cases forward with
      | true => rfl
      | false => have length:=congrArg List.length (reading.2.symm.trans (result.trans function));simp at length
    subst forward
    have firstSource : Source source site oldNear:=firstNear
    by_cases selected : ∃stamp,body=.var stamp 0
    · obtain ⟨stamp,shape⟩:=selected
      have occurs : ArgumentOccurrence body.erase [] := by rw [shape];rfl
      have nodeOrigin : BetaNodePreimage body argument site edge (site++[.arg]) := by
        rw [result];simpa only [List.append_nil] using (BetaNodePreimage.copied (site:=site) (q:=[]) (relative:=[]) (old:=argument) occurs (by cases argument <;> rfl))
      obtain ⟨oldFar,lastTarget,farOrigin⟩:=step.beta_incidence_target_preimage redex nodeOrigin far
      have bodyLoop : Target source (site++[.fn,.body]) (some lam) := by
        refine Or.inr ⟨stamp,0,alpha,body,[],?_,atLambda,?_,rfl⟩
        · rw [LTerm.subterm_append,redex,shape];rfl
        · simp only [lam,List.append_assoc,List.cons_append,List.nil_append]
      exact ⟨oldNear,oldFar,_,_,oldNearTarget,nearOrigin,
        .forward firstSource firstTarget (.forward fnSource fnTarget (.forward bodySource bodyLoop
          (.backward fnTarget fnSource (.forward argSource lastTarget .nil)))),farOrigin,lastTarget,.resultOverlap shape⟩
    · have nonselected : ∀stamp,body≠.var stamp 0 := by simpa only [not_exists] using selected
      have nodeOrigin : BetaNodePreimage body argument site edge (site++[.fn,.body]) := by
        rw [result];simpa only [List.append_nil] using (BetaNodePreimage.retained (site:=site) (relative:=[]) (old:=body) (by cases body <;> rfl) nonselected)
      obtain ⟨oldFar,lastTarget,farOrigin⟩:=step.beta_incidence_target_preimage redex nodeOrigin far
      exact ⟨oldNear,oldFar,_,_,oldNearTarget,nearOrigin,
        .forward firstSource firstTarget (.forward fnSource fnTarget (.forward bodySource lastTarget .nil)),farOrigin,lastTarget,.resultFunction nonselected⟩
  | resultLambda result read shape =>
    have direction : forward=false := by
      cases forward with
      | false => rfl
      | true =>
        have length:=congrArg List.length reading.2
        simp only [result,read,List.length_append,List.length_singleton] at length
        omega
    subst forward
    obtain ⟨oldFar,lastSource,farOrigin⟩:=context_source step redex (by simpa only [result] using far)
    exact ⟨oldNear,oldFar,_,_,oldNearTarget,nearOrigin,
      .backward firstNear bodySource (.backward fnTarget fnSource (.backward firstTarget lastSource .nil)),farOrigin,lastSource,.resultLambda⟩
  | @copyFunction parent occurs copy read =>
    have direction : forward=true := by
      cases forward with
      | true => rfl
      | false =>
        have length:=congrArg List.length reading.2
        simp only [copy,read,List.length_append,List.length_singleton] at length
        omega
    subst forward
    have variableAt : ∃stamp,body.subterm (parent++[.fn])=some (.var stamp (binderDepth (parent++[.fn]))) := by
      change subtermAt body.erase _=some (.var _) at occurs
      rw [←LTerm.erase_subterm] at occurs
      obtain ⟨node,atNode,same⟩:=Option.map_eq_some_iff.mp occurs
      cases node with
      | var stamp index => cases same;exact ⟨stamp,atNode⟩
      | app => cases same
      | lam => cases same
    obtain ⟨stamp,variableAt⟩:=variableAt
    have variableTarget : Target source ((site++[.fn,.body])++(parent++[.fn])) (some lam) := by
      refine Or.inr ⟨stamp,_,alpha,body,parent++[.fn],?_,atLambda,?_,rfl⟩
      · rw [List.append_assoc,LTerm.subterm_append,redex];exact variableAt
      · simp only [lam,List.append_assoc,List.cons_append,List.nil_append]
    have nodeOrigin : BetaNodePreimage body argument site edge (site++[.arg]) := by
      rw [copy];simpa only [List.append_nil] using (BetaNodePreimage.copied (site:=site) (relative:=[]) (old:=argument) occurs (by cases argument <;> rfl))
    obtain ⟨oldFar,lastTarget,farOrigin⟩:=step.beta_incidence_target_preimage redex nodeOrigin far
    exact ⟨oldNear,oldFar,_,_,oldNearTarget,nearOrigin,
      .forward firstNear variableTarget (.backward fnTarget fnSource (.forward argSource lastTarget .nil)),farOrigin,lastTarget,.copyFunction⟩
  | @copyLambda q stamp inner occurs copy read shape =>
    have direction : forward=false := by
      cases forward with
      | false => rfl
      | true => have length:=congrArg List.length (read.trans reading.2);simp at length
    subst forward
    obtain ⟨lastNode,lastAt⟩:=(BetaIncomingReadingOrigin.copyLambda occurs copy read shape).old_prerequisite redex |>.2
    have variableTarget : Target source ((site++[.fn,.body])++q) (some lam) := by
      change subtermAt body.erase _=some (.var _) at occurs
      rw [←LTerm.erase_subterm] at occurs
      obtain ⟨node,atNode,same⟩:=Option.map_eq_some_iff.mp occurs
      cases node with
      | var variableStamp index =>
        cases same
        refine Or.inr ⟨variableStamp,_,alpha,body,q,?_,atLambda,?_,rfl⟩
        · rw [List.append_assoc,LTerm.subterm_append,redex];exact atNode
        · simp only [lam,List.append_assoc,List.cons_append,List.nil_append]
      | app => cases same
      | lam => cases same
    by_cases empty : q=[]
    · have currentSource : Source target site currentFar := by simpa only [copy,empty,List.append_nil] using far
      obtain ⟨oldFar,lastSource,farOrigin⟩:=context_source step redex currentSource
      have loop : Target source (site++[.fn,.body]) (some lam) := by simpa only [empty,List.append_nil] using variableTarget
      refine ⟨oldNear,oldFar,[site++[.arg],site++[.fn],site++[.fn,.body],site++[.fn],site],[false,true,false,false,false],oldNearTarget,nearOrigin,?_,farOrigin,lastSource,?_⟩
      · exact .backward firstNear argSource (.forward fnSource fnTarget
            (.backward loop bodySource (.backward fnTarget fnSource (.backward firstTarget lastSource .nil))))
      · simpa only [empty,List.append_nil] using (CreatedReadingExpansion.copyOverlap (body:=body) (site:=site))
    · obtain ⟨oldFar,lastSource,farOrigin⟩:=copied_source step redex occurs empty lastAt (by simpa only [copy] using far)
      exact ⟨oldNear,oldFar,_,_,oldNearTarget,nearOrigin,
        .backward firstNear argSource (.forward fnSource fnTarget (.backward variableTarget lastSource .nil)),farOrigin,lastSource,.copyLambda empty⟩

#print axioms BetaIncomingReadingOrigin.incidence_expansion
end Lamping.Lambda.Labelled
