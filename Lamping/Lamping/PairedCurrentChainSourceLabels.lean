import Lamping.Lamping.ActualCurrentAfterChains
import Lamping.Lambda.MarkerSourceChainLabels
import Lamping.Lambda.UniformOldChainPreimages
namespace Lamping.AG
open Graph Lambda Lambda.Labelled

private theorem source_chain_at_actual_cut
    {source current : LTerm} {F ps : List Path} {degree : Label} {n : Marked}
    (old : Marked.RelativeOldHistory F ps (Marked.mark F source.erase) n)
    (labels : History ps source current)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (cut : ActualUnsafeMarkerCut F ps source current degree start edges)
    (reading : PrerequisiteReadsDirected current cut.reader cut.edge forward) :
    ∃output : MarkerSourceChain F source degree forward (cut.before.map current.labelAt)
        (cut.node.label.readLetters forward),
      BetaNodeHistoryPreimage labels start output.start := by
  have beforeSafe (e : Path) (member : e∈cut.before) (node : LTerm)
      (lookup : current.subterm e=some node) : node.label.OuterBarsSafe (fun x=>x≠degree) :=
    cut.safeBefore e member node.label (by simp only [LTerm.labelAt,lookup,Option.map_some])
  obtain ⟨spine,s,bs,r,f,name,node,marker,rest,chosen,lookup,safe,segment,sourceReading,chain,
      beforeEq,marks,equation,startTrace⟩:=
    old.earliest_marker_prefix_at_start labels selected sourceSafe cut.segment reading cut.lookup cut.marked beforeSafe
  exact ⟨⟨s,bs,r,f,name,node,marker,rest,chosen,lookup,safe,segment,sourceReading,chain,beforeEq,marks,equation⟩,startTrace⟩

/-- Actual current-chain ancestry reflects to matching complete source-chain
labels, except for the genuine opposite-sign terminal firstunsafe case.
The cut/sign/source chains are outputs; no old iso or completion is an input. -/
theorem paired_current_chain_source_labels
    {initialSource source current : LTerm} {prior ps F : List Path} {degree : Label} {n : Marked}
    {leftStart rightStart oldLeft oldRight : Path} {es fs : List Path}
    (initial : INIT initialSource) (prefixHistory : History prior initialSource source)
    (old : Marked.RelativeOldHistory F ps (Marked.mark F source.erase) n)
    (labels : History ps source current)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (sourceClosed : Closed source.erase) (currentClosed : Closed current.erase)
    (leftChain : PrerequisiteChain current leftStart es) (rightChain : PrerequisiteChain current rightStart fs)
    (iso : ChainIncidenceIso (chainSyntaxIncidence current currentClosed es) (chainSyntaxIncidence current currentClosed fs))
    (leftTrace : BetaNodeHistoryPreimage labels leftStart oldLeft)
    (rightTrace : BetaNodeHistoryPreimage labels rightStart oldRight) :
    (((∀e∈es,degreeReadSafe degree (current.labelAt e)) ∧(∀e∈fs,degreeReadSafe degree (current.labelAt e))) ∧
      ∃oldEs oldFs,PrerequisiteChain source oldLeft oldEs ∧PrerequisiteChain source oldRight oldFs ∧
        oldEs.map source.labelAt=oldFs.map source.labelAt ∧
        ChainIncidenceIsomorphic (chainSyntaxIncidence source sourceClosed oldEs) (chainSyntaxIncidence source sourceClosed oldFs)) ∨
    (∃left : ActualUnsafeMarkerCut F ps source current degree leftStart es,
      ∃right : ActualUnsafeMarkerCut F ps source current degree rightStart fs,
        left.forward=right.forward ∧
        left.before.map current.labelAt=right.before.map current.labelAt ∧
        current.labelAt left.edge=current.labelAt right.edge ∧
        ∃oldEs oldFs,PrerequisiteChain source oldLeft oldEs ∧PrerequisiteChain source oldRight oldFs ∧
          oldEs.map source.labelAt=oldFs.map source.labelAt ∧
          ChainIncidenceIsomorphic (chainSyntaxIncidence source sourceClosed oldEs) (chainSyntaxIncidence source sourceClosed oldFs)) ∨
    (∃left : ActualUnsafeMarkerCut F ps source current degree leftStart es,
      ∃right : ActualUnsafeMarkerCut F ps source current degree rightStart fs,
        left.after=[] ∧right.after=[] ∧left.forward≠right.forward ∧
        left.before.map current.labelAt=right.before.map current.labelAt ∧current.labelAt left.edge=current.labelAt right.edge) := by
  have currentLabels:=actual_chain_labels_forward (prefixHistory.append labels) initial currentClosed leftChain rightChain iso
  rcases actual_first_unsafe_marker_leaves initial prefixHistory old labels selected sourceSafe currentClosed leftChain rightChain iso with allSafe | cuts
  · obtain ⟨ls,les,lc,lt,le,lm,ll⟩:=old.marker_free_chain_preimages (DegreeAligned.initial source F) labels selected leftChain (by
      intro e member node lookup;exact allSafe.1 e member node.label (by simp only [LTerm.labelAt,lookup,Option.map_some]))
    obtain ⟨rs,res,rc,rt,re,rm,rl⟩:=old.marker_free_chain_preimages (DegreeAligned.initial source F) labels selected rightChain (by
      intro e member node lookup;exact allSafe.2 e member node.label (by simp only [LTerm.labelAt,lookup,Option.map_some]))
    have lStart:=lt.unique leftTrace
    have rStart:=rt.unique rightTrace
    subst ls;subst rs
    have same:=lm.symm.trans (currentLabels.trans rm)
    exact Or.inl ⟨allSafe,les,res,lc,rc,same,actual_chain_iso_of_labels prefixHistory initial sourceClosed lc rc same⟩
  · obtain ⟨left,right,len,lt,rt,ld,rd,front,head,back,tails,signs⟩:=cuts
    by_cases direction : left.forward=right.forward
    · obtain ⟨lout,ltrace⟩:=source_chain_at_actual_cut old labels selected sourceSafe left left.reading
      have rightReading : PrerequisiteReadsDirected current right.reader right.edge left.forward := by
        rw [direction];exact right.reading
      obtain ⟨rout,rtrace⟩:=source_chain_at_actual_cut old labels selected sourceSafe right rightReading
      have sameNode : left.node.label=right.node.label := by
        simpa only [LTerm.labelAt,left.lookup,right.lookup,Option.map_some,Option.some.injEq] using head
      have sameWord : left.node.label.readLetters left.forward=right.node.label.readLetters left.forward := congrArg (fun x:Label=>x.readLetters left.forward) sameNode
      have fullLabels:=lout.compare_chain_labels rout selected front sameWord
      have lStart:=ltrace.unique leftTrace
      have rStart:=rtrace.unique rightTrace
      have lc : PrerequisiteChain source oldLeft lout.edges := by rw [←lStart];exact lout.chain
      have rc : PrerequisiteChain source oldRight rout.edges := by rw [←rStart];exact rout.chain
      exact Or.inr (Or.inl ⟨left,right,direction,front,head,lout.edges,rout.edges,lc,rc,fullLabels,
        actual_chain_iso_of_labels prefixHistory initial sourceClosed lc rc fullLabels⟩)
    · have empty : left.after=[] := signs.resolve_right direction
      exact Or.inr (Or.inr ⟨left,right,empty,tails.mp empty,direction,front,head⟩)
end Lamping.AG
