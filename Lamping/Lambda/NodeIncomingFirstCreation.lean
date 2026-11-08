import Lamping.Lambda.BetaChainExistenceReflection
import Lamping.Lambda.BetaPreimageLabels
namespace Lamping.Lambda.Labelled
/-- Actual node ancestry with every encountered incoming occurrence uncreated.
There are no label, chain, representation or source-map fields. -/
inductive UncreatedNodeHistoryPreimage : {ps : List Path} →{source target : LTerm} →
    History ps source target →Path →Path →Prop where
  | nil (t : LTerm) (p : Path) : UncreatedNodeHistoryPreimage (.nil t) p p
  | one {site : Path} {ps : List Path} {source middle target body argument : LTerm}
      {beta alpha : Label} {currentPosition middlePosition oldPosition : Path}
      {step : StepAt site source middle} {remaining : History ps middle target}
      (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
      (origin : BetaNodePreimage body argument site middlePosition oldPosition)
      (uncreated : ¬BetaCreatedIncoming body site middlePosition)
      (tail : UncreatedNodeHistoryPreimage remaining currentPosition middlePosition) :
      UncreatedNodeHistoryPreimage (.cons step remaining) currentPosition oldPosition

namespace UncreatedNodeHistoryPreimage
theorem to_node (trace : UncreatedNodeHistoryPreimage labels p oldPosition) :
    BetaNodeHistoryPreimage labels p oldPosition := by
  induction trace with
  | nil => exact .nil _ _
  | @one site ps source middle target body argument beta alpha p mid oldPosition step remaining redex origin uncreated tail ih => exact .one (step:=step) redex origin ih

theorem source_label
    {ps : List Path} {source target current : LTerm} {labels : History ps source target}
    {p oldPosition : Path}
    (trace : UncreatedNodeHistoryPreimage labels p oldPosition)
    (lookup : target.subterm p=some current) :
    ∃old,source.subterm oldPosition=some old ∧old.label=current.label := by
  induction trace with
  | nil => exact ⟨current,lookup,rfl⟩
  | @one site ps source middle target body argument beta alpha p mid oldPosition step remaining redex origin uncreated tail ih =>
    obtain ⟨midNode,midLookup,tailLabel⟩ := ih lookup
    obtain ⟨old,atOld,labelEq⟩ := step.beta_preimage_label redex origin midLookup uncreated
    exact ⟨old,atOld,labelEq.trans tailLabel⟩
end UncreatedNodeHistoryPreimage

/-- The FIRST created incoming occurrence on THIS lineage. pre/site/post
index the actual schedule split. The prefix stores only actual uncreated steps;
the suffix is arbitrary actual node ancestry, not necessarily uncreated. -/
inductive NodeIncomingFirstCreation : {ps : List Path} →{source target : LTerm} →
    History ps source target →Path →Path →List Path →Path →List Path →Prop where
  | here {site : Path} {ps : List Path} {source middle target body argument : LTerm}
      {beta alpha : Label} {p mid oldPosition : Path}
      {step : StepAt site source middle} {remaining : History ps middle target}
      (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
      (origin : BetaNodePreimage body argument site mid oldPosition)
      (created : BetaCreatedIncoming body site mid)
      (tail : BetaNodeHistoryPreimage remaining p mid) :
      NodeIncomingFirstCreation (.cons step remaining) p oldPosition [] site ps
  | later {head : Path} {ps pre : List Path} {site : Path} {post : List Path}
      {source middle target body argument : LTerm} {beta alpha : Label}
      {p mid oldPosition : Path} {step : StepAt head source middle}
      {remaining : History ps middle target}
      (redex : source.subterm head=some (.app beta (.lam alpha body) argument))
      (origin : BetaNodePreimage body argument head mid oldPosition)
      (uncreated : ¬BetaCreatedIncoming body head mid)
      (tail : NodeIncomingFirstCreation remaining p mid pre site post) :
      NodeIncomingFirstCreation (.cons step remaining) p oldPosition (head::pre) site post

/-- A structural partition of the actual node trace, independent of labels. -/
theorem BetaNodeHistoryPreimage.incoming_partition
    (trace : BetaNodeHistoryPreimage labels p oldPosition) :
    UncreatedNodeHistoryPreimage labels p oldPosition ∨
      ∃pre site post,NodeIncomingFirstCreation labels p oldPosition pre site post := by
  classical
  induction trace with
  | nil => exact Or.inl (.nil _ _)
  | @one site ps source middle target body argument beta alpha p mid oldPosition step remaining redex origin tail ih =>
    by_cases created : BetaCreatedIncoming body site mid
    · exact Or.inr ⟨[],site,ps,.here (step:=step) redex origin created tail⟩
    · rcases ih with uncreated |⟨pre,event,post,first⟩
      · exact Or.inl (.one (step:=step) redex origin created uncreated)
      · exact Or.inr ⟨site::pre,event,post,.later (step:=step) redex origin created first⟩

/-- Extract the actual finite split; the chosen event has a truly all-uncreated
prefix, and its arbitrary suffix stays tied to the same final node. -/
theorem NodeIncomingFirstCreation.split
    {ps : List Path} {source target : LTerm} {labels : History ps source target}
    {p oldPosition : Path} {pre : List Path} {site : Path} {post : List Path}
    (first : NodeIncomingFirstCreation labels p oldPosition pre site post) :
    ps=pre++site::post ∧
    ∃before after beforePosition afterPosition body argument beta alpha,
      ∃earlierLabels : History pre source before,∃_step : StepAt site before after,
      ∃suffix : History post after target,
        before.subterm site=some (.app beta (.lam alpha body) argument) ∧
        UncreatedNodeHistoryPreimage earlierLabels beforePosition oldPosition ∧
        BetaNodePreimage body argument site afterPosition beforePosition ∧
        BetaCreatedIncoming body site afterPosition ∧
        BetaNodeHistoryPreimage suffix p afterPosition := by
  induction first with
  | @here site ps source middle target body argument beta alpha p mid oldPosition step remaining redex origin created tail =>
    exact ⟨rfl,source,middle,oldPosition,mid,body,argument,beta,alpha,.nil _,step,remaining,
      redex,.nil _ _,origin,created,tail⟩
  | @later head ps pre site post source middle target body argument beta alpha p mid oldPosition step remaining redex origin uncreated tail ih =>
    obtain ⟨schedule,before,after,bp,ap,b,a,bs,ls,earlierLabels,event,suffix,atEvent,up,atOrigin,created,afterTrace⟩ := ih
    exact ⟨congrArg (head::·) schedule,before,after,bp,ap,b,a,bs,ls,.cons step earlierLabels,event,suffix,
      atEvent,.one (step:=step) redex origin uncreated up,atOrigin,created,afterTrace⟩

/-- Lookup wrapper preserves THIS original coordinate, not a same-label choice. -/
theorem BetaNodeHistoryPreimage.incoming_partition_at_lookup
    {ps : List Path} {source target current : LTerm} {labels : History ps source target}
    {p oldPosition : Path} (trace : BetaNodeHistoryPreimage labels p oldPosition)
    (lookup : target.subterm p=some current) :
    ∃old,source.subterm oldPosition=some old ∧
      (UncreatedNodeHistoryPreimage labels p oldPosition ∨
        ∃pre site post,NodeIncomingFirstCreation labels p oldPosition pre site post) := by
  obtain ⟨oldPosition',old,atOld,other⟩ := labels.node_preimage_from_lookup lookup
  have same:=other.unique trace
  exact ⟨old,same ▸ atOld,trace.incoming_partition⟩
#print axioms UncreatedNodeHistoryPreimage.source_label
#print axioms BetaNodeHistoryPreimage.incoming_partition
#print axioms NodeIncomingFirstCreation.split
#print axioms BetaNodeHistoryPreimage.incoming_partition_at_lookup
end Lamping.Lambda.Labelled
