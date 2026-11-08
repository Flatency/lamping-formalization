import Lamping.Lambda.UniformReadingCreationTrace
import Lamping.Lambda.NodeIncomingFirstCreation
import Lamping.Lambda.UncreatedChainTransport
import Lamping.Lambda.DirectedReadingCreation

namespace Lamping.Lambda.Labelled

private theorem false_lookup
    {t : LTerm} {reader : Path}
    (reading : PrerequisiteReadsDirected t reader reader false) :
    ∃stamp body,t.subterm reader=some (.lam stamp body) := by
  rcases reading.1 with ⟨stamp,fn,arg,lookup,eq⟩ | ⟨stamp,body,lookup,_⟩
  · have length:=congrArg List.length eq;simp at length
  · exact ⟨stamp,body,lookup⟩

theorem UncreatedNodeHistoryPreimage.false_terminal_reflect
    {ps : List Path} {source target : LTerm}
    {labels : History ps source target} {reader oldReader : Path}
    (trace : UncreatedNodeHistoryPreimage labels reader oldReader)
    (reading : PrerequisiteReadsDirected target reader reader false)
    (terminal : PrerequisiteChain target reader [reader]) :
    PrerequisiteReadsDirected source oldReader oldReader false ∧
      PrerequisiteChain source oldReader [oldReader] := by
  induction trace with
  | nil => exact ⟨reading,terminal⟩
  | @one site ps source middle target body argument beta alpha reader mid oldReader step remaining redex origin uncreated tail ih =>
    obtain ⟨midRead,midChain⟩:=ih reading terminal
    obtain ⟨oldEdges,oldChain,edgeOrigins⟩:=midChain.beta_uncreated_reflect step redex origin (by
      intro edge inside
      have equal : edge=mid:=List.mem_singleton.mp inside
      exact equal ▸ uncreated)
    obtain ⟨stamp,inner,lookup⟩:=false_lookup midRead
    obtain ⟨old,atOld,tag⟩:=step.preimage_node_constructor redex origin lookup
    have oldRead : PrerequisiteReadsDirected source oldReader oldReader false := by
      cases old with
      | var => cases tag
      | app => cases tag
      | lam a b => exact ⟨Or.inr ⟨a,b,atOld,rfl⟩,rfl⟩
    cases edgeOrigins with
    | cons edgeOrigin rest =>
      cases rest
      have equal:=edgeOrigin.unique origin
      exact ⟨oldRead,equal ▸ oldChain⟩
end Lamping.Lambda.Labelled

namespace Lamping.Lambda.Marked
open Labelled

private def TerminalCreatedEvent
    (F ps : List Path) (m n : Marked) (source target : LTerm) (degree : Label) (reader : Path) : Prop :=
  ∃ pre post site m1 m2 t1 t2 beta body argument eventReader,
    ps=pre++(site::post) ∧
    RelativeOldHistory F pre m m1 ∧RelativeOldHistory F post m2 n ∧
    ReductionAt site m1 m2 ∧site∈setResidualPositions F m1 ∧
    ∃ _prefix : Labelled.History pre source t1,
    ∃ suffix : Labelled.History post t2 target,
      Labelled.StepAt site t1 t2 ∧
      t1.subterm site=some (.app beta (.lam degree body) argument) ∧
      BetaCreatedIncoming body site eventReader ∧
      UncreatedNodeHistoryPreimage suffix reader eventReader ∧
      PrerequisiteReadsDirected t2 eventReader eventReader false ∧
      PrerequisiteChain t2 eventReader [eventReader] ∧
      target.labelAt reader=t2.labelAt eventReader ∧
      ∃ oldReader first last,
        BetaIncomingReadingOrigin body argument site eventReader eventReader oldReader first last ∧
        PrerequisiteChain t1 oldReader [first,site++[.fn]] ∧
        ∃ oldLast,t1.subterm last=some oldLast

private theorem inherited_terminal_or_event
    {F ps : List Path} {m n : Marked} (old : RelativeOldHistory F ps m n)
    {d : Path→Option Label} {source target : LTerm} {degree : Label} {reader : Path}
    (aligned : DegreeAligned d m source) (labels : Labelled.History ps source target)
    (selected : ∀p∈F,d p=some degree)
    (reading : PrerequisiteReadsDirected target reader reader false)
    (terminal : PrerequisiteChain target reader [reader]) :
    (∃oldReader,UncreatedNodeHistoryPreimage labels reader oldReader ∧
      PrerequisiteReadsDirected source oldReader oldReader false ∧
      PrerequisiteChain source oldReader [oldReader]) ∨
    TerminalCreatedEvent F ps m n source target degree reader := by
  induction old generalizing source target reader with
  | nil => cases labels;exact Or.inl ⟨reader,.nil _ _,reading,terminal⟩
  | @cons site mark next rest last reduction member tail ih =>
    cases labels with
    | @cons _ _ current _ _ turn remaining =>
      rcases ih (aligned.step reduction turn) remaining reading terminal with inherited | event
      · obtain ⟨mid,trace,midRead,midChain⟩:=inherited
        obtain ⟨name,chosen,residual⟩:=(mem_setResidualPositions _ _ _).mp member
        have atDegree:=(aligned.trace_degree residual).trans (selected name chosen)
        obtain ⟨beta,body,argument,redex⟩:=LTerm.degreeAt_redex atDegree
        by_cases created : BetaCreatedIncoming body site mid
        · obtain ⟨oldReader,first,last,origin⟩:=turn.created_reading_origin redex midRead.1 (betaCreatedIncoming_iff.mp created)
          obtain ⟨oldTwo,lastLookup⟩:=origin.old_prerequisite redex
          obtain ⟨finalStamp,finalBody,finalLookup⟩:=Labelled.false_lookup reading
          obtain ⟨midNode,midLookup,same⟩:=trace.source_label finalLookup
          have labelEq : target.labelAt reader=current.labelAt mid := by
            simpa only [LTerm.labelAt,finalLookup,midLookup,Option.map_some] using congrArg (@some Label) same.symm
          exact Or.inr ⟨[],rest,site,mark,next,source,current,beta,body,argument,mid,
            rfl,.nil _,tail,reduction,member,.nil _,remaining,turn,redex,created,trace,
            midRead,midChain,labelEq,oldReader,first,last,origin,oldTwo,lastLookup⟩
        · obtain ⟨stamp,inner,lookup⟩:=Labelled.false_lookup midRead
          obtain ⟨oldReader,origin⟩:=turn.beta_node_preimage redex lookup
          have wholeTrace : UncreatedNodeHistoryPreimage (.cons turn remaining) reader oldReader :=
            .one (step:=turn) redex origin created trace
          obtain ⟨oldRead,oldChain⟩:=wholeTrace.false_terminal_reflect reading terminal
          exact Or.inl ⟨oldReader,wholeTrace,oldRead,oldChain⟩
      · obtain ⟨pre,post,eventSite,m1,m2,t1,t2,beta,body,argument,eventReader,
          split,beforeOld,afterOld,eventReduction,eventMember,segmentPrefix,suffix,eventStep,
          redex,created,trace,eventRead,eventChain,labelEq,oldReader,first,last,
          origin,oldTwo,lastLookup⟩:=event
        exact Or.inr ⟨site::pre,post,eventSite,m1,m2,t1,t2,beta,body,argument,eventReader,
          by simpa only [List.cons_append] using congrArg (site::·) split,
          .cons reduction member beforeOld,afterOld,eventReduction,eventMember,
          .cons turn segmentPrefix,suffix,eventStep,redex,created,trace,eventRead,eventChain,
          labelEq,oldReader,first,last,origin,oldTwo,lastLookup⟩

theorem RelativeOldHistory.created_false_terminal_event_of_fresh
    {F ps : List Path} {m n : Marked}
    (old : RelativeOldHistory F ps m n)
    {d : Path → Option Label} {source target current : LTerm}
    {degree : Label} {reader : Path}
    (aligned : DegreeAligned d m source)
    (labels : Labelled.History ps source target)
    (selected : ∀ p∈F, d p=some degree)
    (reading : PrerequisiteReadsDirected target reader reader false)
    (terminal : PrerequisiteChain target reader [reader])
    (lookup : target.subterm reader=some current)
    (fresh : current.label∉source.labels) :
    ∃ pre post site m1 m2 t1 t2 beta body argument eventReader,
      ps=pre++(site::post) ∧
      RelativeOldHistory F pre m m1 ∧ RelativeOldHistory F post m2 n ∧
      ReductionAt site m1 m2 ∧ site∈setResidualPositions F m1 ∧
      ∃ _prefix : Labelled.History pre source t1,
      ∃ suffix : Labelled.History post t2 target,
        Labelled.StepAt site t1 t2 ∧
        t1.subterm site=some (.app beta (.lam degree body) argument) ∧
        BetaCreatedIncoming body site eventReader ∧
        UncreatedNodeHistoryPreimage suffix reader eventReader ∧
        PrerequisiteReadsDirected t2 eventReader eventReader false ∧
        PrerequisiteChain t2 eventReader [eventReader] ∧
        target.labelAt reader=t2.labelAt eventReader ∧
        ∃ oldReader first last,
          BetaIncomingReadingOrigin body argument site eventReader eventReader oldReader first last ∧
          PrerequisiteChain t1 oldReader [first,site++[.fn]] ∧
          ∃ oldLast,t1.subterm last=some oldLast := by
  rcases inherited_terminal_or_event old aligned labels selected reading terminal with inherited | event
  · obtain ⟨oldReader,trace,_read,_chain⟩:=inherited
    obtain ⟨node,atOld,same⟩:=trace.source_label lookup
    exact False.elim (fresh (same ▸ LTerm.label_mem_of_subterm atOld))
  · exact event

#print axioms Labelled.UncreatedNodeHistoryPreimage.false_terminal_reflect
#print axioms RelativeOldHistory.created_false_terminal_event_of_fresh
end Lamping.Lambda.Marked
