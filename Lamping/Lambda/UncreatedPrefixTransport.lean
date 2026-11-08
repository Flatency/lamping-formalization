import Lamping.Lambda.UncreatedChainTransport
namespace Lamping.Lambda.Labelled
/-- Finite prefix reflection needs no old chain at its endpoint. -/
theorem PrerequisitePrefix.beta_uncreated_reflect
    {source target body argument : LTerm} {site start oldStart finish : Path} {beta alpha : Label}
    (segment : PrerequisitePrefix target start edges finish)
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (origin : BetaNodePreimage body argument site start oldStart)
    (uncreated : ∀ edge∈edges,¬BetaCreatedIncoming body site edge) :
    ∃ oldFinish oldEdges,PrerequisitePrefix source oldStart oldEdges oldFinish ∧
      BetaEdgePreimages body argument site edges oldEdges ∧
      BetaNodePreimage body argument site finish oldFinish := by
  induction segment generalizing oldStart with
  | refl => exact ⟨_,[],.refl,.nil,origin⟩
  | @app p a fn arg es finish lookup notLambda tail ih =>
    obtain ⟨oldStamp,oldFn,oldArg,oldLookup,childOrigin,same⟩ :=
      step.beta_app_preimages redex origin lookup (uncreated _ (by simp))
    have oldNotLambda : ∀ l b,oldFn≠.lam l b := by
      intro l b equal
      rw [equal] at same
      cases fn with
      | var => cases same
      | app => cases same
      | lam stamp body => exact notLambda stamp body rfl
    obtain ⟨oldFinish,oldEdges,oldTail,edgeOrigins,endOrigin⟩ := ih childOrigin (by
      intro edge member; exact uncreated edge (List.mem_cons_of_mem _ member))
    exact ⟨_,_,.app oldLookup oldNotLambda oldTail,.cons childOrigin edgeOrigins,endOrigin⟩
  | @lam parent child stamp currentBody es finish lookup notFunction tail ih =>
    obtain ⟨oldParent,oldStamp,oldBody,oldPositionEq,oldLookup,parentOrigin⟩ :=
      step.beta_lambda_parent_preimage redex origin lookup rfl (uncreated _ (by simp))
    obtain ⟨oldFinish,oldEdges,oldTail,edgeOrigins,endOrigin⟩ := ih parentOrigin (by
      intro edge member; exact uncreated edge (List.mem_cons_of_mem _ member))
    refine ⟨oldFinish,oldStart::oldEdges,?_,.cons origin edgeOrigins,endOrigin⟩
    rw [oldPositionEq] at oldLookup ⊢
    exact .lam oldLookup notFunction oldTail
  | @var leaf stamp index parent binderStamp binderBody rest es finish lookup binder split depth tail ih =>
    obtain ⟨oldParent,oldStamp,oldBody,oldBinder,oldJump,parentOrigin⟩ :=
      step.beta_variable_preimage_prefix redex origin binder
        (by simpa only [depth] using lookup) split
    obtain ⟨oldFinish,oldEdges,oldTail,edgeOrigins,endOrigin⟩ := ih parentOrigin uncreated
    exact ⟨_,oldEdges,by simpa using oldJump.append oldTail,edgeOrigins,endOrigin⟩
/-- The actual next reading role survives when THIS read edge is uncreated. -/
theorem StepAt.beta_uncreated_reading
    {source target body argument : LTerm} {site middle oldMiddle edge : Path} {beta alpha : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (origin : BetaNodePreimage body argument site middle oldMiddle)
    (reads : PrerequisiteReads target middle edge)
    (uncreated : ¬BetaCreatedIncoming body site edge) :
    ∃ oldEdge,PrerequisiteReads source oldMiddle oldEdge ∧
      BetaNodePreimage body argument site edge oldEdge := by
  rcases reads with ⟨stamp,fn,arg,lookup,equal⟩ | ⟨stamp,inner,lookup,equal⟩
  · subst edge
    obtain ⟨oldStamp,oldFn,oldArg,atOld,childOrigin,_⟩ :=
      step.beta_app_preimages redex origin lookup uncreated
    exact ⟨_,Or.inl ⟨oldStamp,oldFn,oldArg,atOld,rfl⟩,childOrigin⟩
  · obtain ⟨old,atOld,same⟩ := step.preimage_node_constructor redex origin lookup
    cases old with
    | var => cases same
    | app => cases same
    | lam oldStamp oldBody =>
      exact ⟨oldMiddle,Or.inr ⟨oldStamp,oldBody,atOld,rfl⟩,equal ▸ origin⟩
private theorem prefix_start_lookup (segment : PrerequisitePrefix t start edges finish)
    (atFinish : ∃ node,t.subterm finish=some node) : ∃ node,t.subterm start=some node := by
  cases segment with
  | refl => exact atFinish
  | app lookup _ _ => exact ⟨_,lookup⟩
  | lam lookup _ _ => exact ⟨_,lookup⟩
  | var lookup _ _ _ _ => exact ⟨_,lookup⟩
private theorem prefix_edge_lookup (segment : PrerequisitePrefix t start edges finish)
    (member : edge∈edges) : ∃ node,t.subterm edge=some node := by
  induction segment with
  | refl => cases member
  | @app p a fn arg es finish lookup _ tail ih =>
    rcases List.mem_cons.mp member with equal | inside
    · subst edge
      refine ⟨fn,?_⟩
      rw [LTerm.subterm_append,lookup]; cases fn <;> rfl
    · exact ih inside
  | lam lookup _ tail ih =>
    rcases List.mem_cons.mp member with equal | inside
    · exact ⟨_,equal ▸ lookup⟩
    · exact ih inside
  | var _ _ _ _ tail ih => exact ih member
/-- Actual finite prefix and next reading reflect without any chain hypothesis
at the endpoint or on the unread suffix. -/
theorem StepAt.uncreated_prefix_reading
    {source target body argument : LTerm} {site start finish edge : Path} {beta alpha : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (segment : PrerequisitePrefix target start edges finish)
    (reads : PrerequisiteReads target finish edge)
    (uncreated : ∀ e∈edges,¬BetaCreatedIncoming body site e)
    (edgeOld : ¬BetaCreatedIncoming body site edge) :
    ∃ oldStart oldFinish oldEdges oldEdge,
      BetaNodePreimage body argument site start oldStart ∧
      PrerequisitePrefix source oldStart oldEdges oldFinish ∧
      BetaNodePreimage body argument site finish oldFinish ∧
      BetaEdgePreimages body argument site edges oldEdges ∧
      PrerequisiteReads source oldFinish oldEdge ∧
      BetaNodePreimage body argument site edge oldEdge ∧
      edges.map target.labelAt=oldEdges.map source.labelAt ∧
      target.labelAt edge=source.labelAt oldEdge := by
  have atFinish : ∃ node,target.subterm finish=some node := by
    rcases reads with ⟨a,f,b,h,_⟩ | ⟨a,b,h,_⟩ <;> exact ⟨_,h⟩
  obtain ⟨current,atStart⟩ := prefix_start_lookup segment atFinish
  obtain ⟨oldStart,startOrigin⟩ := step.beta_node_preimage redex atStart
  obtain ⟨oldFinish,oldEdges,oldPrefix,origins,finishOrigin⟩ :=
    segment.beta_uncreated_reflect step redex startOrigin uncreated
  obtain ⟨oldEdge,oldReads,edgeOrigin⟩ :=
    step.beta_uncreated_reading redex finishOrigin reads edgeOld
  have labels := step.beta_preimage_ordered_labels redex origins
    (fun e member=>prefix_edge_lookup segment member) uncreated
  have atEdge : ∃ node,target.subterm edge=some node := by
    rcases reads with ⟨a,f,b,h,equal⟩ | ⟨a,b,h,equal⟩
    · subst edge; refine ⟨f,?_⟩; rw [LTerm.subterm_append,h]; cases f <;> rfl
    · exact ⟨_,equal ▸ h⟩
  obtain ⟨node,lookup⟩ := atEdge
  exact ⟨oldStart,oldFinish,oldEdges,oldEdge,startOrigin,oldPrefix,finishOrigin,origins,
    oldReads,edgeOrigin,labels,step.beta_preimage_labelAt redex edgeOrigin lookup edgeOld⟩
end Lamping.Lambda.Labelled

namespace Lamping.Lambda.Labelled
/-- Each direction-sensitive old reading origin is also the actual node
preimage of the current app/lambda at which this incoming edge is read. -/
theorem BetaIncomingReadingOrigin.middle_preimage
    (origin : BetaIncomingReadingOrigin body argument site edge middle oldMiddle first last) :
    BetaNodePreimage body argument site middle oldMiddle := by
  cases origin with
  | resultFunction result function =>
    apply BetaNodePreimage.context
    rintro ⟨r,equal⟩
    have size := congrArg List.length (equal.trans (congrArg (·++r) function))
    simp only [List.length_append,List.length_singleton] at size
    omega
  | resultLambda result reading oldLambda =>
    subst middle;subst body
    simpa only [List.append_nil] using
      (BetaNodePreimage.retained (site:=site) (relative:=[]) (old:=LTerm.lam _ _) rfl
        (by intro stamp impossible;cases impossible))
  | @copyFunction parent occurs copy reading =>
    subst middle
    change subtermAt body.erase (parent++[.fn])=some (.var (binderDepth (parent++[.fn]))) at occurs
    rw [subtermAt_append,←LTerm.erase_subterm] at occurs
    cases atParent : body.subterm parent with
    | none => rw [atParent] at occurs;cases occurs
    | some old =>
      rw [atParent,Option.map_some,Option.bind_some] at occurs
      cases old with
      | var => cases occurs
      | lam => cases occurs
      | app stamp fn arg =>
        exact BetaNodePreimage.retained atParent (by intro stamp impossible;cases impossible)
  | copyLambda occurs copy reading oldLambda =>
    rw [reading,copy]
    simpa only [List.append_nil] using
      (BetaNodePreimage.copied (body:=body) (argument:=argument) (site:=site)
        (q:=_) (relative:=[]) (old:=argument) occurs (by cases argument <;> rfl))
private theorem start_lookup (segment : PrerequisitePrefix t start edges finish)
    (reads : PrerequisiteReads t finish edge) : ∃ node,t.subterm start=some node := by
  cases segment with
  | refl => rcases reads with ⟨a,f,b,h,_⟩ | ⟨a,b,h,_⟩ <;> exact ⟨_,h⟩
  | app lookup _ _ => exact ⟨_,lookup⟩
  | lam lookup _ _ => exact ⟨_,lookup⟩
  | var lookup _ _ _ _ => exact ⟨_,lookup⟩
/-- Created-edge prefix surgery needs only the actual finite prefix/reading.
There is no old or current chain hypothesis at the unread endpoint. -/
theorem StepAt.created_prefix_old_chain
    {source target body argument : LTerm} {site start middle edge : Path} {beta alpha : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (segment : PrerequisitePrefix target start before middle)
    (reads : PrerequisiteReads target middle edge)
    (created : BetaCreatedIncoming body site edge)
    (uncreated : ∀ e∈before,¬BetaCreatedIncoming body site e) :
    ∃ oldStart oldBefore oldMiddle first last,
      BetaNodePreimage body argument site start oldStart ∧
      BetaIncomingReadingOrigin body argument site edge middle oldMiddle first last ∧
      PrerequisitePrefix source oldStart oldBefore oldMiddle ∧
      BetaEdgePreimages body argument site before oldBefore ∧
      PrerequisiteChain source oldStart (oldBefore++[first,site++[.fn]]) ∧
      before.map target.labelAt=oldBefore.map source.labelAt ∧
      ∃ oldLast,source.subterm last=some oldLast := by
  obtain ⟨oldMiddle,first,last,readingOrigin⟩ :=
    step.created_reading_origin redex reads (betaCreatedIncoming_iff.mp created)
  obtain ⟨current,atStart⟩ := start_lookup segment reads
  obtain ⟨oldStart,startOrigin⟩ := step.beta_node_preimage redex atStart
  obtain ⟨actualEnd,oldBefore,oldPrefix,edgeOrigins,endOrigin⟩ :=
    segment.beta_uncreated_reflect step redex startOrigin uncreated
  have equal := endOrigin.unique readingOrigin.middle_preimage
  subst actualEnd
  obtain ⟨oldTwo,lastLookup⟩ := readingOrigin.old_prerequisite redex
  have labels := step.beta_preimage_ordered_labels redex edgeOrigins
    (fun e member=>prefix_edge_lookup segment member) uncreated
  exact ⟨oldStart,oldBefore,oldMiddle,first,last,startOrigin,readingOrigin,oldPrefix,
    edgeOrigins,oldPrefix.close oldTwo,labels,lastLookup⟩
end Lamping.Lambda.Labelled
