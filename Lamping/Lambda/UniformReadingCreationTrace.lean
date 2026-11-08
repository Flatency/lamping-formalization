import Lamping.Lambda.UncreatedPrefixTransport
import Lamping.Lambda.LabelUniformDevelopment
namespace Lamping.Lambda.Labelled
/-- Operational event/schedule witness, not an input certificate. -/
def CreatedReadingEvent (F ps : List Path) (m n : Marked) (source target : LTerm)
    (degree : Label) (beforeLabels : List (Option Label)) (chosen : Option Label) : Prop :=
  ∃ pre post site m1 m2 t1 t2 beta body argument start before middle edge,
    ps=pre++(site::post) ∧
    Marked.RelativeOldHistory F pre m m1 ∧Marked.RelativeOldHistory F post m2 n ∧
    Marked.ReductionAt site m1 m2 ∧site∈Marked.setResidualPositions F m1 ∧
    History pre source t1 ∧History post t2 target ∧StepAt site t1 t2 ∧
    t1.subterm site=some (.app beta (.lam degree body) argument) ∧
    PrerequisitePrefix t2 start before middle ∧PrerequisiteReads t2 middle edge ∧
    BetaCreatedIncoming body site edge ∧
    (∀ e∈before,¬BetaCreatedIncoming body site e) ∧
    beforeLabels=before.map t2.labelAt ∧chosen=t2.labelAt edge ∧
    ∃ oldMiddle first last,
      BetaIncomingReadingOrigin body argument site edge middle oldMiddle first last ∧
      PrerequisiteChain t1 oldMiddle [first,site++[.fn]] ∧
      (∃ oldLast,t1.subterm last=some oldLast) ∧
      ∃ oldStart oldBefore,
        BetaNodePreimage body argument site start oldStart ∧
        PrerequisitePrefix t1 oldStart oldBefore oldMiddle ∧
        BetaEdgePreimages body argument site before oldBefore ∧
        PrerequisiteChain t1 oldStart (oldBefore++[first,site++[.fn]]) ∧
        before.map t2.labelAt=oldBefore.map t1.labelAt
private theorem prefix_edge_lookup (segment : PrerequisitePrefix t start edges finish)
    (member : edge∈edges) : ∃ node,t.subterm edge=some node := by
  induction segment with
  | refl => cases member
  | @app p a fn arg es finish lookup _ tail ih =>
    rcases List.mem_cons.mp member with equal | inside
    · subst edge; refine ⟨fn,?_⟩; rw [LTerm.subterm_append,lookup]; cases fn <;> rfl
    · exact ih inside
  | lam lookup _ tail ih =>
    rcases List.mem_cons.mp member with equal | inside
    · exact ⟨_,equal ▸ lookup⟩
    · exact ih inside
  | var _ _ _ _ tail ih => exact ih member
private theorem safe_of_maps {left right : LTerm} {degree : Label} {edges other : List Path} {e : Path} {node : LTerm}
    (same : edges.map left.labelAt=other.map right.labelAt)
    (safe : ∀ e∈edges,∀ node,left.subterm e=some node →node.label.OuterBarsSafe (fun x=>x≠degree))
    (member : e∈other) (lookup : right.subterm e=some node) :
    node.label.OuterBarsSafe (fun x=>x≠degree) := by
  have present : some node.label∈other.map right.labelAt :=
    List.mem_map.mpr ⟨e,member,by simp [LTerm.labelAt,lookup]⟩
  rw [←same] at present
  obtain ⟨p,inside,equal⟩ := List.mem_map.mp present
  change (left.subterm p).map LTerm.label=some node.label at equal
  obtain ⟨old,atOld,labelEq⟩ := Option.map_eq_some_iff.mp equal
  rw [←labelEq];exact safe p inside old atOld
end Lamping.Lambda.Labelled
namespace Lamping.Lambda.Marked
open Labelled
/-- Tracks the specified reading unchanged backwards, stopping at an actual
creation of THAT literal label. This does not identify its first nested marker. -/
theorem RelativeOldHistory.inherited_reading_or_created_event
    {F ps : List Path} {m n : Marked} (old : RelativeOldHistory F ps m n)
    {d : Path →Option Label} {source target : LTerm} {degree : Label}
    {start middle edge : Path} {before : List Path}
    (aligned : DegreeAligned d m source) (labels : Labelled.History ps source target)
    (selected : ∀ p∈F,d p=some degree)
    (segment : PrerequisitePrefix target start before middle)
    (reads : PrerequisiteReads target middle edge)
    (safe : ∀ e∈before,∀ node,target.subterm e=some node →node.label.OuterBarsSafe (fun x=>x≠degree)) :
    (∃ oldStart oldBefore oldMiddle oldEdge,
      PrerequisitePrefix source oldStart oldBefore oldMiddle ∧
      PrerequisiteReads source oldMiddle oldEdge ∧
      before.map target.labelAt=oldBefore.map source.labelAt ∧
      target.labelAt edge=source.labelAt oldEdge) ∨
    CreatedReadingEvent F ps m n source target degree (before.map target.labelAt) (target.labelAt edge) := by
  induction old generalizing source target start middle edge before with
  | nil => cases labels;exact Or.inl ⟨_,_,_,_,segment,reads,rfl,rfl⟩
  | @cons site mark next rest last reduction member tail ih =>
    cases labels with
    | @cons _ _ current _ _ turn remaining =>
      rcases ih (aligned.step reduction turn) remaining segment reads safe with inherited | event
      · obtain ⟨s,es,f,e,oldPrefix,oldReads,mapEq,chosenEq⟩ := inherited
        obtain ⟨name,chosen,residual⟩ := (mem_setResidualPositions _ _ _).mp member
        have atDegree := (aligned.trace_degree residual).trans (selected name chosen)
        obtain ⟨beta,body,argument,redex⟩ := LTerm.degreeAt_redex atDegree
        have beforeOld (p : Path) (inside : p∈es) : ¬BetaCreatedIncoming body site p := by
          obtain ⟨node,lookup⟩ := prefix_edge_lookup oldPrefix inside
          intro created
          exact turn.created_label_not_safe redex lookup created (safe_of_maps mapEq safe inside lookup)
        by_cases created : BetaCreatedIncoming body site e
        · obtain ⟨oldStart,oldBefore,oldMiddle,first,last,startOrigin,readingOrigin,
              reflectedPrefix,edgeOrigins,wholeChain,wholeLabels,oldLast⟩ :=
            turn.created_prefix_old_chain redex oldPrefix oldReads created beforeOld
          obtain ⟨oldChain,_⟩ := readingOrigin.old_prerequisite redex
          exact Or.inr ⟨[],rest,site,mark,next,source,current,beta,body,argument,s,es,f,e,
            rfl,.nil _,tail,reduction,member,.nil _,remaining,turn,redex,oldPrefix,oldReads,
            created,beforeOld,mapEq,chosenEq,oldMiddle,first,last,readingOrigin,oldChain,oldLast,
            oldStart,oldBefore,startOrigin,reflectedPrefix,edgeOrigins,wholeChain,wholeLabels⟩
        · obtain ⟨ss,ff,ees,ee,_,reflected,_,_,reflectedReads,_,reflectedMap,reflectedChosen⟩ :=
            turn.uncreated_prefix_reading redex oldPrefix oldReads beforeOld created
          exact Or.inl ⟨ss,ees,ff,ee,reflected,reflectedReads,mapEq.trans reflectedMap,chosenEq.trans reflectedChosen⟩
      · obtain ⟨pre,post,eventSite,m1,m2,t1,t2,beta,body,argument,s,es,f,e,
          split,beforeOld,afterOld,eventReduction,eventMember,beforeLabels,afterLabels,
          eventStep,redex,eventPrefix,eventReads,created,uncreated,mapEq,chosenEq,neighbors⟩ := event
        refine Or.inr ⟨site::pre,post,eventSite,m1,m2,t1,t2,beta,body,argument,s,es,f,e,
          ?_,.cons reduction member beforeOld,afterOld,eventReduction,eventMember,
          .cons turn beforeLabels,afterLabels,eventStep,redex,eventPrefix,eventReads,
          created,uncreated,mapEq,chosenEq,neighbors⟩
        simpa only [List.cons_append] using congrArg (site::·) split
/-- Initial old-label exclusion forces an actual creation of this final
literal label along the SAME OLD schedule. No sourceSafe is used midway. -/
theorem RelativeOldHistory.created_reading_event_of_fresh
    {F ps : List Path} {m n : Marked} (old : RelativeOldHistory F ps m n)
    {d : Path →Option Label} {source target current : LTerm} {degree : Label}
    {start middle edge : Path} {before : List Path}
    (aligned : DegreeAligned d m source) (labels : Labelled.History ps source target)
    (selected : ∀ p∈F,d p=some degree)
    (segment : PrerequisitePrefix target start before middle)
    (reads : PrerequisiteReads target middle edge)
    (safe : ∀ e∈before,∀ node,target.subterm e=some node →node.label.OuterBarsSafe (fun x=>x≠degree))
    (lookup : target.subterm edge=some current) (fresh : current.label∉source.labels) :
    CreatedReadingEvent F ps m n source target degree (before.map target.labelAt) (target.labelAt edge) := by
  rcases old.inherited_reading_or_created_event aligned labels selected segment reads safe with inherited | event
  · obtain ⟨s,es,f,e,oldPrefix,oldReads,_,labelEq⟩ := inherited
    have atOld : ∃ node,source.subterm e=some node := by
      rcases oldReads with ⟨a,fn,arg,atFn,equal⟩ | ⟨a,body,atLambda,equal⟩
      · subst e;refine ⟨fn,?_⟩;rw [LTerm.subterm_append,atFn];cases fn <;> rfl
      · exact ⟨_,equal ▸ atLambda⟩
    obtain ⟨node,atNode⟩ := atOld
    have equal : current.label=node.label := by
      simpa only [LTerm.labelAt,lookup,atNode,Option.map_some,Option.some.injEq] using labelEq
    exact False.elim (fresh (equal ▸ LTerm.label_mem_of_subterm atNode))
  · exact event
end Lamping.Lambda.Marked
