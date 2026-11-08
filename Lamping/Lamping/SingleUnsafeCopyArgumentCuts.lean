import Lamping.Lamping.ActualCurrentAfterChains
import Lamping.Lamping.SafeLastCopyArgumentAuxInputs
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
variable {source middle target t : LTerm}

private theorem append_last_inj {p q : Path} {s t : Step} (same : p++[s]=q++[t]) : p=q ∧s=t := by
  have reverse:=congrArg List.reverse same
  simp only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append] at reverse
  have parts:=List.cons.inj reverse
  exact ⟨by simpa only [List.reverse_reverse] using congrArg List.reverse parts.2,parts.1⟩

private theorem arg_lambda_tail
    (lookup : t.subterm (p++[.arg])=some (.lam stamp inner))
    (chain : PrerequisiteChain t (p++[.arg]) (edge::after)) :
    edge=p++[.arg] ∧PrerequisiteChain t p after ∧after≠[] := by
  rcases chain.lambda_cases lookup with ⟨parent,a,arg,fn,atApp,split⟩ |
    ⟨parent,child,tail,readerEq,notFn,listEq,actual⟩
  · have wrong:Step.arg=Step.fn:=(append_last_inj fn).2
    cases wrong
  · have parentEq:parent=p := (append_last_inj readerEq).1.symm
    subst parent
    have parts:=List.cons.inj listEq
    rw [parts.2]
    exact ⟨parts.1,actual,actual.nonempty⟩

/-- All fields are derived output for the SAME internally chosen cuts. There
is no desired cut, direction, old iso, evaluator or physical equality input. -/
structure SingleUnsafeCopyArgumentCuts
    (event : SelectedOldTurn F source degree pre middle target site)
    (closed : Closed source.erase) (leftStart rightStart leftParent rightParent : Path)
    (es fs : List Path) where
  left : ActualUnsafeMarkerCut F (pre++[site]) source target degree leftStart es
  right : ActualUnsafeMarkerCut F (pre++[site]) source target degree rightStart fs
  leftEdge : left.edge=site++(leftParent++[.arg])
  rightEdge : right.edge=site++(rightParent++[.arg])
  leftReader : left.reader=site++(leftParent++[.arg])
  rightReader : right.reader=site++(rightParent++[.arg])
  leftFalse : left.forward=false
  rightFalse : right.forward=false
  sameBeforeLength : left.before.length=right.before.length
  leftTake : es.take left.before.length=left.before
  rightTake : fs.take left.before.length=right.before
  leftDrop : es.drop (left.before.length+1)=left.after
  rightDrop : fs.drop (left.before.length+1)=right.after
  fullLabels : es.map target.labelAt=fs.map target.labelAt
  sameBefore : left.before.map target.labelAt=right.before.map target.labelAt
  sameHead : target.labelAt left.edge=target.labelAt right.edge
  sameAfter : left.after.map target.labelAt=right.after.map target.labelAt
  leftHeadChain : PrerequisiteChain target (site++(leftParent++[.arg])) (left.edge::left.after)
  rightHeadChain : PrerequisiteChain target (site++(rightParent++[.arg])) (right.edge::right.after)
  headIso : ChainIncidenceIsomorphic
    (chainSyntaxIncidence target (event.final_history.closed closed) (left.edge::left.after))
    (chainSyntaxIncidence target (event.final_history.closed closed) (right.edge::right.after))
  leftAfterChain : PrerequisiteChain target (site++leftParent) left.after
  rightAfterChain : PrerequisiteChain target (site++rightParent) right.after
  afterIso : ChainIncidenceIsomorphic
    (chainSyntaxIncidence target (event.final_history.closed closed) left.after)
    (chainSyntaxIncidence target (event.final_history.closed closed) right.after)
  leftAfterSafe : ∀e∈left.after,∀node,target.subterm e=some node →node.label.OuterBarsSafe (fun x=>x≠degree)
  rightAfterSafe : ∀e∈right.after,∀node,target.subterm e=some node →node.label.OuterBarsSafe (fun x=>x≠degree)
  leftAfterNonempty : left.after≠[]
  rightAfterNonempty : right.after≠[]
  leftNoHeadBefore : left.edge∉left.before
  rightNoHeadBefore : right.edge∉right.before
  leftNoHeadAfter : left.edge∉left.after
  rightNoHeadAfter : right.edge∉right.after
  leftAfterShorter : left.after.length<es.length
  rightAfterShorter : right.after.length<fs.length

private theorem locate_arg_cut
    (chain : PrerequisiteChain t start edges)
    (cut : ActualUnsafeMarkerCut F ps source t degree start edges)
    (lookup : t.subterm (p++[.arg])=some (.lam stamp inner))
    (otherSafe : ∀e∈edges,e≠p++[.arg] →degreeReadSafe degree (t.labelAt e)) :
    cut.edge=p++[.arg] ∧cut.reader=p++[.arg] ∧cut.forward=false ∧
    PrerequisiteChain t (p++[.arg]) (cut.edge::cut.after) ∧
    PrerequisiteChain t p cut.after ∧cut.after≠[] ∧
    cut.edge∉cut.before ∧cut.edge∉cut.after ∧
    (∀e∈cut.after,∀node,t.subterm e=some node →node.label.OuterBarsSafe (fun x=>x≠degree)) := by
  have edgeMember : cut.edge∈edges :=
    Eq.mpr (congrArg (fun xs : List Path=>cut.edge∈xs) cut.split) (List.mem_append_right _ List.mem_cons_self)
  have edgeEq : cut.edge=p++[.arg] := by
    classical
    by_cases same : cut.edge=p++[.arg]
    · exact same
    · have safe:=otherSafe cut.edge edgeMember same cut.node.label (by simp only [LTerm.labelAt,cut.lookup,Option.map_some])
      exact False.elim (cut.marked safe)
  have direction : cut.forward=false := by
    cases sign : cut.forward with
    | false => rfl
    | true =>
      have same:=cut.reading.2
      rw [sign] at same
      change cut.edge=cut.reader++[.fn] at same
      have wrong:Step.arg=Step.fn:=(append_last_inj (edgeEq.symm.trans same)).2
      cases wrong
  have readerEq : cut.reader=p++[.arg] := by
    have same:=cut.reading.2
    rw [direction] at same
    change cut.edge=cut.reader at same
    exact same.symm.trans edgeEq
  have headChain : PrerequisiteChain t (p++[.arg]) (cut.edge::cut.after) := readerEq ▸ cut.remaining
  obtain ⟨_,afterChain,nonempty⟩:=arg_lambda_tail lookup headChain
  have nodup:=chain.nodup
  rw [cut.split,List.nodup_append] at nodup
  have noAfter : cut.edge∉cut.after:= (List.nodup_cons.mp nodup.2.1).1
  have noBefore : cut.edge∉cut.before := by
    intro inside
    exact nodup.2.2 cut.edge inside cut.edge List.mem_cons_self rfl
  refine ⟨edgeEq,readerEq,direction,headChain,afterChain,nonempty,noBefore,noAfter,?_⟩
  intro e inside node atNode
  have member : e∈edges := by rw [cut.split];exact List.mem_append_right _ (List.mem_cons_of_mem _ inside)
  have ne : e≠p++[.arg] := by intro same;apply noAfter;rw [edgeEq,←same];exact inside
  exact otherSafe e member ne node.label (by simp only [LTerm.labelAt,atNode,Option.map_some])

/-- Actual normal COPY ARG/member and safety of every other READ select the
first unsafe cuts internally. LAST safety is separate and is not an unused
premise of this finite localization theorem. -/
theorem single_unsafe_copy_argument_cuts
    {original : LTerm} {prior : List Path}
    (initial : INIT original) (prefixHistory : History prior original source)
    (sourceClosed : Closed source.erase)
    (event : SelectedOldTurn F source degree pre middle target site)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (leftOccurs : ArgumentOccurrence event.body.erase (leftParent++[.arg]))
    (rightOccurs : ArgumentOccurrence event.body.erase (rightParent++[.arg]))
    (leftLookup : target.subterm (site++(leftParent++[.arg]))=some (.lam leftStamp leftInner))
    (rightLookup : target.subterm (site++(rightParent++[.arg]))=some (.lam rightStamp rightInner))
    (leftChain : PrerequisiteChain target leftStart es)
    (rightChain : PrerequisiteChain target rightStart fs)
    (iso : ChainIncidenceIso (chainSyntaxIncidence target (event.final_history.closed sourceClosed) es)
      (chainSyntaxIncidence target (event.final_history.closed sourceClosed) fs))
    (leftMember : (site++(leftParent++[.arg]))∈es)
    (rightMember : (site++(rightParent++[.arg]))∈fs)
    (leftOtherSafe : ∀e∈es,e≠site++(leftParent++[.arg]) →degreeReadSafe degree (target.labelAt e))
    (rightOtherSafe : ∀e∈fs,e≠site++(rightParent++[.arg]) →degreeReadSafe degree (target.labelAt e)) :
    Nonempty (SingleUnsafeCopyArgumentCuts event sourceClosed leftStart rightStart leftParent rightParent es fs) := by
  have leftMarked := event.turn.created_label_not_safe event.redex leftLookup
    (betaCreatedIncoming_iff.mpr (Or.inr ⟨leftParent++[.arg],leftOccurs,rfl⟩))
  have rightMarked := event.turn.created_label_not_safe event.redex rightLookup
    (betaCreatedIncoming_iff.mpr (Or.inr ⟨rightParent++[.arg],rightOccurs,rfl⟩))
  rcases actual_first_unsafe_marker_leaves initial prefixHistory event.final_old event.final_history selected sourceSafe
      (event.final_history.closed sourceClosed) leftChain rightChain iso with all | cuts
  · have leftSafe:=all.1 _ leftMember leftStamp (by simp only [LTerm.labelAt,leftLookup,Option.map_some,LTerm.label])
    have rightSafe:=all.2 _ rightMember rightStamp (by simp only [LTerm.labelAt,rightLookup,Option.map_some,LTerm.label])
    have impossible : False ∧False:=⟨leftMarked leftSafe,rightMarked rightSafe⟩
    exact False.elim impossible.1
  · obtain ⟨left,right,len,lt,rt,ld,rd,front,head,back,tails,signs⟩:=cuts
    have ll : target.subterm ((site++leftParent)++[.arg])=some (.lam leftStamp leftInner) := by
      simpa only [List.append_assoc] using leftLookup
    have rl : target.subterm ((site++rightParent)++[.arg])=some (.lam rightStamp rightInner) := by
      simpa only [List.append_assoc] using rightLookup
    have ls : ∀e∈es,e≠(site++leftParent)++[.arg] →degreeReadSafe degree (target.labelAt e) := by
      simpa only [List.append_assoc] using leftOtherSafe
    have rs : ∀e∈fs,e≠(site++rightParent)++[.arg] →degreeReadSafe degree (target.labelAt e) := by
      simpa only [List.append_assoc] using rightOtherSafe
    obtain ⟨le,lr,lf,lh,la,ln,lb,ldup,lsafe⟩:=locate_arg_cut leftChain left ll ls
    obtain ⟨re,rr,rf,rh,ra,rn,rb,rdup,rsafe⟩:=locate_arg_cut rightChain right rl rs
    have headLabels : (left.edge::left.after).map target.labelAt=(right.edge::right.after).map target.labelAt := by
      simp only [List.map_cons,head,back]
    have hi:=actual_chain_iso_of_labels (prefixHistory.append event.final_history) initial (event.final_history.closed sourceClosed) lh rh headLabels
    have ai:=actual_chain_iso_of_labels (prefixHistory.append event.final_history) initial (event.final_history.closed sourceClosed) la ra back
    refine ⟨⟨left,right,?_,?_,?_,?_,lf,rf,len,lt,rt,ld,rd,?_,front,head,back,?_,?_,hi,la,ra,ai,lsafe,rsafe,ln,rn,lb,rb,ldup,rdup,left.after_length_lt,right.after_length_lt⟩⟩
    · simpa only [List.append_assoc] using le
    · simpa only [List.append_assoc] using re
    · simpa only [List.append_assoc] using lr
    · simpa only [List.append_assoc] using rr
    · exact actual_chain_labels_forward (prefixHistory.append event.final_history) initial (event.final_history.closed sourceClosed) leftChain rightChain iso
    · simpa only [List.append_assoc] using lh
    · simpa only [List.append_assoc] using rh
end Lamping.AG
