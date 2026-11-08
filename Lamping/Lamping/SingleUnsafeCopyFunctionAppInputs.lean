import Lamping.Lamping.ActualCurrentAfterChains
import Lamping.Lamping.ForwardFarChainComparison
import Lamping.Lamping.SameEventBetaPieces
import Lamping.Lamping.DirectedMarkerSpineIncidence
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
variable {source middle target t : LTerm}

private theorem append_last_inj {p q : Path} {s t : Step} (same : p++[s]=q++[t]) : p=q ∧s=t := by
  have reverse:=congrArg List.reverse same
  simp only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append] at reverse
  have parts:=List.cons.inj reverse
  exact ⟨by simpa only [List.reverse_reverse] using congrArg List.reverse parts.2,parts.1⟩

private theorem function_parent (lookup : t.subterm (p++[.fn])=some node) :
    ∃stamp fn arg,t.subterm p=some (.app stamp fn arg) := by
  rw [LTerm.subterm_append] at lookup
  cases atParent : t.subterm p with
  | none => rw [atParent] at lookup;cases lookup
  | some parent =>
    rw [atParent,Option.bind_some] at lookup
    cases parent with
    | var => cases lookup
    | lam => cases lookup
    | app stamp fn arg => exact ⟨stamp,fn,arg,rfl⟩

private theorem app_function_tail
    (lookup : t.subterm (p++[.fn])=some (.app stamp fn arg))
    (chain : PrerequisiteChain t p (edge::after)) :
    edge=p++[.fn] ∧PrerequisiteChain t (p++[.fn]) after ∧after≠[] := by
  obtain ⟨parentStamp,parentFn,parentArg,atParent⟩:=function_parent lookup
  have fnEq : parentFn=.app stamp fn arg := by
    rw [LTerm.subterm_append,atParent,Option.bind_some] at lookup
    exact Option.some.inj (by simpa only [LTerm.subterm] using lookup)
  subst parentFn
  rcases chain.app_cases atParent with ⟨l,b,shape,split⟩ |⟨notLambda,tail,listEq,actual⟩
  · cases shape
  · have parts:=List.cons.inj listEq
    exact ⟨parts.1,parts.2 ▸ actual,by intro empty;exact actual.nonempty (parts.2.symm.trans empty)⟩

/-- All fields are derived output for the SAME internally chosen cuts. There
is no desired cut, direction, old iso, evaluator or physical equality input. -/
structure CopyFunctionAppCuts
    (event : SelectedOldTurn F source degree pre middle target site)
    (closed : Closed source.erase) (leftStart rightStart leftParent rightParent : Path)
    (es fs : List Path) where
  left : ActualUnsafeMarkerCut F (pre++[site]) source target degree leftStart es
  right : ActualUnsafeMarkerCut F (pre++[site]) source target degree rightStart fs
  leftEdge : left.edge=site++(leftParent++[.fn])
  rightEdge : right.edge=site++(rightParent++[.fn])
  leftReader : left.reader=site++leftParent
  rightReader : right.reader=site++rightParent
  leftTrue : left.forward=true
  rightTrue : right.forward=true
  sameBeforeLength : left.before.length=right.before.length
  leftTake : es.take left.before.length=left.before
  rightTake : fs.take left.before.length=right.before
  leftDrop : es.drop (left.before.length+1)=left.after
  rightDrop : fs.drop (left.before.length+1)=right.after
  fullLabels : es.map target.labelAt=fs.map target.labelAt
  sameBefore : left.before.map target.labelAt=right.before.map target.labelAt
  sameHead : target.labelAt left.edge=target.labelAt right.edge
  sameAfter : left.after.map target.labelAt=right.after.map target.labelAt
  leftRemaining : PrerequisiteChain target (site++leftParent) (left.edge::left.after)
  rightRemaining : PrerequisiteChain target (site++rightParent) (right.edge::right.after)
  headIso : ChainIncidenceIsomorphic
    (chainSyntaxIncidence target (event.final_history.closed closed) (left.edge::left.after))
    (chainSyntaxIncidence target (event.final_history.closed closed) (right.edge::right.after))
  leftAfterChain : PrerequisiteChain target (site++(leftParent++[.fn])) left.after
  rightAfterChain : PrerequisiteChain target (site++(rightParent++[.fn])) right.after
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

private theorem locate_function_cut
    (chain : PrerequisiteChain t start edges)
    (cut : ActualUnsafeMarkerCut F ps source t degree start edges)
    (lookup : t.subterm (p++[.fn])=some (.app stamp fn arg))
    (otherSafe : ∀e∈edges,e≠p++[.fn] →degreeReadSafe degree (t.labelAt e)) :
    cut.edge=p++[.fn] ∧cut.reader=p ∧cut.forward=true ∧
    PrerequisiteChain t p (cut.edge::cut.after) ∧
    PrerequisiteChain t (p++[.fn]) cut.after ∧cut.after≠[] ∧
    cut.edge∉cut.before ∧cut.edge∉cut.after ∧
    (∀e∈cut.after,∀node,t.subterm e=some node →node.label.OuterBarsSafe (fun x=>x≠degree)) := by
  have edgeMember : cut.edge∈edges :=
    Eq.mpr (congrArg (fun xs : List Path=>cut.edge∈xs) cut.split) (List.mem_append_right _ List.mem_cons_self)
  have edgeEq : cut.edge=p++[.fn] := by
    classical
    by_cases same : cut.edge=p++[.fn]
    · exact same
    · have safe:=otherSafe cut.edge edgeMember same cut.node.label (by simp only [LTerm.labelAt,cut.lookup,Option.map_some])
      exact False.elim (cut.marked safe)
  have direction : cut.forward=true := by
    cases sign : cut.forward with
    | true => rfl
    | false =>
      have readerEq:=cut.reading.2
      rw [sign] at readerEq
      change cut.edge=cut.reader at readerEq
      rcases cut.reading.1 with ⟨a,f,b,atApp,function⟩ |⟨a,b,atLambda,same⟩
      · have size:=congrArg List.length (readerEq.symm.trans function)
        simp only [List.length_append,List.length_singleton] at size
        omega
      · rw [←readerEq,edgeEq,lookup] at atLambda
        cases atLambda
  have readerEq : cut.reader=p := by
    have same:=cut.reading.2
    rw [direction] at same
    change cut.edge=cut.reader++[.fn] at same
    exact (append_last_inj (edgeEq.symm.trans same)).1.symm
  have headChain : PrerequisiteChain t p (cut.edge::cut.after) := readerEq ▸ cut.remaining
  obtain ⟨_,afterChain,nonempty⟩:=app_function_tail lookup headChain
  have nodup:=chain.nodup
  rw [cut.split,List.nodup_append] at nodup
  have noAfter : cut.edge∉cut.after:= (List.nodup_cons.mp nodup.2.1).1
  have noBefore : cut.edge∉cut.before := by
    intro inside
    exact nodup.2.2 cut.edge inside cut.edge List.mem_cons_self rfl
  refine ⟨edgeEq,readerEq,direction,headChain,afterChain,nonempty,noBefore,noAfter,?_⟩
  intro e inside node atNode
  have member : e∈edges := by rw [cut.split];exact List.mem_append_right _ (List.mem_cons_of_mem _ inside)
  have ne : e≠p++[.fn] := by intro same;apply noAfter;rw [edgeEq,←same];exact inside
  exact otherSafe e member ne node.label (by simp only [LTerm.labelAt,atNode,Option.map_some])

/-- Actual normal COPY FUNCTION APP/member and safety of every other READ select the
first unsafe cuts internally. FIRST-safe final-leaf provenance is added
separately below without rerunning the OLD producer. -/
private theorem copy_function_app_cuts
    {original : LTerm} {prior : List Path}
    (initial : INIT original) (prefixHistory : History prior original source)
    (sourceClosed : Closed source.erase)
    (event : SelectedOldTurn F source degree pre middle target site)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (leftOccurs : ArgumentOccurrence event.body.erase (leftParent++[.fn]))
    (rightOccurs : ArgumentOccurrence event.body.erase (rightParent++[.fn]))
    (leftLookup : target.subterm (site++(leftParent++[.fn]))=some (.app leftStamp leftFn leftArg))
    (rightLookup : target.subterm (site++(rightParent++[.fn]))=some (.app rightStamp rightFn rightArg))
    (leftChain : PrerequisiteChain target leftStart es)
    (rightChain : PrerequisiteChain target rightStart fs)
    (iso : ChainIncidenceIso (chainSyntaxIncidence target (event.final_history.closed sourceClosed) es)
      (chainSyntaxIncidence target (event.final_history.closed sourceClosed) fs))
    (leftMember : (site++(leftParent++[.fn]))∈es)
    (rightMember : (site++(rightParent++[.fn]))∈fs)
    (leftOtherSafe : ∀e∈es,e≠site++(leftParent++[.fn]) →degreeReadSafe degree (target.labelAt e))
    (rightOtherSafe : ∀e∈fs,e≠site++(rightParent++[.fn]) →degreeReadSafe degree (target.labelAt e)) :
    Nonempty (CopyFunctionAppCuts event sourceClosed leftStart rightStart leftParent rightParent es fs) := by
  have leftMarked := event.turn.created_label_not_safe event.redex leftLookup
    (betaCreatedIncoming_iff.mpr (Or.inr ⟨leftParent++[.fn],leftOccurs,rfl⟩))
  have rightMarked := event.turn.created_label_not_safe event.redex rightLookup
    (betaCreatedIncoming_iff.mpr (Or.inr ⟨rightParent++[.fn],rightOccurs,rfl⟩))
  rcases actual_first_unsafe_marker_leaves initial prefixHistory event.final_old event.final_history selected sourceSafe
      (event.final_history.closed sourceClosed) leftChain rightChain iso with all | cuts
  · have leftSafe:=all.1 _ leftMember leftStamp (by simp only [LTerm.labelAt,leftLookup,Option.map_some,LTerm.label])
    have rightSafe:=all.2 _ rightMember rightStamp (by simp only [LTerm.labelAt,rightLookup,Option.map_some,LTerm.label])
    have impossible : False ∧False:=⟨leftMarked leftSafe,rightMarked rightSafe⟩
    exact False.elim impossible.1
  · obtain ⟨left,right,len,lt,rt,ld,rd,front,head,back,tails,signs⟩:=cuts
    have ll : target.subterm ((site++leftParent)++[.fn])=some (.app leftStamp leftFn leftArg) := by
      simpa only [List.append_assoc] using leftLookup
    have rl : target.subterm ((site++rightParent)++[.fn])=some (.app rightStamp rightFn rightArg) := by
      simpa only [List.append_assoc] using rightLookup
    have ls : ∀e∈es,e≠(site++leftParent)++[.fn] →degreeReadSafe degree (target.labelAt e) := by
      simpa only [List.append_assoc] using leftOtherSafe
    have rs : ∀e∈fs,e≠(site++rightParent)++[.fn] →degreeReadSafe degree (target.labelAt e) := by
      simpa only [List.append_assoc] using rightOtherSafe
    obtain ⟨le,lr,lf,lh,la,ln,lb,ldup,lsafe⟩:=locate_function_cut leftChain left ll ls
    obtain ⟨re,rr,rf,rh,ra,rn,rb,rdup,rsafe⟩:=locate_function_cut rightChain right rl rs
    have headLabels : (left.edge::left.after).map target.labelAt=(right.edge::right.after).map target.labelAt := by
      simp only [List.map_cons,head,back]
    have hi:=actual_chain_iso_of_labels (prefixHistory.append event.final_history) initial (event.final_history.closed sourceClosed) lh rh headLabels
    have ai:=actual_chain_iso_of_labels (prefixHistory.append event.final_history) initial (event.final_history.closed sourceClosed) la ra back
    refine ⟨⟨left,right,?_,?_,?_,?_,lf,rf,len,lt,rt,ld,rd,?_,front,head,back,?_,?_,hi,?_,?_,ai,lsafe,rsafe,ln,rn,lb,rb,ldup,rdup,left.after_length_lt,right.after_length_lt⟩⟩
    · simpa only [List.append_assoc] using le
    · simpa only [List.append_assoc] using re
    · simpa only [List.append_assoc] using lr
    · simpa only [List.append_assoc] using rr
    · exact actual_chain_labels_forward (prefixHistory.append event.final_history) initial (event.final_history.closed sourceClosed) leftChain rightChain iso
    · simpa only [List.append_assoc] using lh
    · simpa only [List.append_assoc] using rh

    · simpa only [List.append_assoc] using la
    · simpa only [List.append_assoc] using ra

private theorem snoc_inj {A : Type} {ps qs : List A} {p q : A} (same : ps++[p]=qs++[q]) : ps=qs ∧p=q := by
  have reverse:=congrArg List.reverse same
  simp only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append] at reverse
  have parts:=List.cons.inj reverse
  exact ⟨by simpa only [List.reverse_reverse] using congrArg List.reverse parts.2,parts.1⟩

private theorem same_final_event
    (event : SelectedOldTurn F source degree pre middle target site)
    (other : SelectedOldTurn F source degree otherPre otherMiddle target otherSite)
    (schedule : otherPre++[otherSite]=pre++[site]) :
    otherPre=pre ∧otherSite=site ∧otherMiddle=middle ∧other.beta=event.beta ∧
      other.body=event.body ∧other.argument=event.argument := by
  obtain ⟨preEq,siteEq⟩:=snoc_inj schedule
  have labels : History pre source otherMiddle:=preEq ▸ other.labels
  have middleEq:=labels.deterministic event.labels
  have atSame : middle.subterm site=some (.app other.beta (.lam degree other.body) other.argument) :=
    Eq.mp (congrArg (fun pair : LTerm×Path=>pair.1.subterm pair.2=some (.app other.beta (.lam degree other.body) other.argument))
      (show (otherMiddle,otherSite)=(middle,site) from Prod.ext middleEq siteEq)) other.redex
  have parts:=LTerm.app.inj (Option.some.inj (atSame.symm.trans event.redex))
  exact ⟨preEq,siteEq,middleEq,parts.1,(LTerm.lam.inj parts.2.1).2,parts.2.2⟩

private theorem copy_function_first
    (origin : BetaIncomingReadingOrigin body argument site edge reader oldReader first last)
    (reading : PrerequisiteReadsDirected target reader edge true)
    (head : edge=site++(parent++[.fn])) :
    first=(site++[.fn,.body])++(parent++[.fn]) := by
  cases origin with
  | resultFunction result function =>
    have lengths:=congrArg List.length (head.symm.trans result)
    simp only [List.length_append,List.length_cons,List.length_nil] at lengths
    omega
  | @copyFunction other occurs copy read =>
    have same:=List.append_cancel_left (head.symm.trans copy)
    have parentEq:parent=other:=(append_last_inj same).1
    rw [parentEq]
  | resultLambda result read oldLambda =>
    have same : edge=edge++[.fn] := by simpa only [read,←result] using reading.2
    have sizes:=congrArg List.length same
    simp at sizes
  | copyLambda occurs copy read oldLambda =>
    have same : edge=edge++[.fn] := by simpa only [read] using reading.2
    have sizes:=congrArg List.length same
    simp at sizes

/-- Finite elimination on the actual public provenance data, not on the
proof shape of its Prop-valued spine index. -/
private theorem geometry_final_safe
    (event : SelectedOldTurn F source degree pre middle target site)
    {ps : List Path} {before : List (Option Label)} {edge : Path} {current : LTerm}
    {spine : DirectedMarkerSpine F source degree true ps target before edge}
    {lookup : target.subterm edge=some current}
    {leaf : DirectedMarkerLeafOutput F source degree true ps (current.label.readLetters true)}
    {snapshot : IncomingIncidenceSnapshot target edge}
    (geometry : SpineIncidenceProvenance F source degree true spine lookup leaf snapshot)
    (schedule : ps=pre++[site])
    (head : edge=site++(parent++[.fn]))
    (occurs : ArgumentOccurrence event.body.erase (parent++[.fn]))
    (firstSafe : ∀node,middle.subterm ((site++[.fn,.body])++(parent++[.fn]))=some node →
      node.label.OuterBarsSafe (fun x=>x≠degree)) :
    leaf.pre=pre ∧leaf.site=site ∧leaf.after=[] ∧leaf.continuation=[] ∧
      leaf.edge=edge ∧leaf.reader=site++parent ∧leaf.current=current ∧
      leaf.target=target ∧leaf.middle=middle ∧geometry.creationFrames.length=1 := by
  cases geometry with
  | inherited other lookup oldLookup origin uncreated same earlier earlierGeometry snap transport =>
    obtain ⟨preEq,siteEq,middleEq,betaEq,bodyEq,argEq⟩:=same_final_event event other schedule
    apply False.elim
    apply uncreated
    rw [bodyEq,siteEq,head]
    exact betaCreatedIncoming_iff.mpr (Or.inr ⟨parent++[.fn],occurs,rfl⟩)
  | safe other reading lookup origin segment beforeEq beforeSafe firstLookup firstSafeOther lastLookup lastSourceLookup lastTrace marks formula snap firstSnap frame =>
    obtain ⟨preEq,siteEq,middleEq,betaEq,bodyEq,argEq⟩:=same_final_event event other schedule
    have headRight : edge=(site++parent)++[.fn] := by simpa only [List.append_assoc] using head
    have readerEq := (append_last_inj (headRight.symm.trans reading.2)).1.symm
    exact ⟨preEq,siteEq,rfl,rfl,rfl,readerEq,rfl,rfl,middleEq,rfl⟩
  | marked other reading lookup origin segment beforeEq beforeSafe firstLookup firstMarked lastLookup lastSourceLookup lastTrace earlier earlierGeometry marks formula equation snap frame =>
    obtain ⟨preEq,siteEq,middleEq,betaEq,bodyEq,argEq⟩:=same_final_event event other schedule
    have localHead:=head
    rw [←siteEq] at localHead
    have firstEq:=copy_function_first origin reading localHead
    rw [siteEq] at firstEq
    have localLookup:=firstLookup
    rw [firstEq] at localLookup
    have fixedLookup := (congrArg (fun t : LTerm=>t.subterm ((site++[.fn,.body])++(parent++[.fn]))) middleEq).symm.trans localLookup
    exact False.elim (firstMarked (firstSafe _ fixedLookup))


/-- Only an equality transport of THIS actual cut's spine. It does not
run earliest-marker descent again or replace its operational witness. -/
abbrev ActualUnsafeMarkerCut.asTrueSpine
    (cut : ActualUnsafeMarkerCut F ps source target degree start edges) (direction : cut.forward=true) :
    DirectedMarkerSpine F source degree true ps target (cut.before.map target.labelAt) cut.edge :=
  direction ▸ cut.spine

/-- Pure natural inputs for existing TRUE-head and complete-chain consumers.
All leaf/frame data are derived from the SAME returned actual cut geometry. -/
structure SingleUnsafeCopyFunctionAppInputs
    (event : SelectedOldTurn F source degree pre middle target site)
    (closed : Closed source.erase) (leftStart rightStart leftParent rightParent : Path)
    (es fs : List Path) extends CopyFunctionAppCuts event closed leftStart rightStart leftParent rightParent es fs where
  leftLeaf : DirectedMarkerLeafOutput F source degree true (pre++[site]) (left.node.label.readLetters true)
  rightLeaf : DirectedMarkerLeafOutput F source degree true (pre++[site]) (right.node.label.readLetters true)
  leftSnapshot : IncomingIncidenceSnapshot target left.edge
  rightSnapshot : IncomingIncidenceSnapshot target right.edge
  leftGeometry : SpineIncidenceProvenance F source degree true (left.asTrueSpine leftTrue) left.lookup leftLeaf leftSnapshot
  rightGeometry : SpineIncidenceProvenance F source degree true (right.asTrueSpine rightTrue) right.lookup rightLeaf rightSnapshot
  leftLeafPre : leftLeaf.pre=pre
  rightLeafPre : rightLeaf.pre=pre
  leftLeafSite : leftLeaf.site=site
  rightLeafSite : rightLeaf.site=site
  leftLeafAfter : leftLeaf.after=[]
  rightLeafAfter : rightLeaf.after=[]
  leftLeafContinuation : leftLeaf.continuation=[]
  rightLeafContinuation : rightLeaf.continuation=[]
  leftLeafReader : leftLeaf.reader=site++leftParent
  rightLeafReader : rightLeaf.reader=site++rightParent
  leftLeafEdge : leftLeaf.edge=left.edge
  rightLeafEdge : rightLeaf.edge=right.edge
  leftLeafCurrent : leftLeaf.current=left.node
  rightLeafCurrent : rightLeaf.current=right.node
  leftLeafTarget : leftLeaf.target=target
  rightLeafTarget : rightLeaf.target=target
  leftLeafMiddle : leftLeaf.middle=middle
  rightLeafMiddle : rightLeaf.middle=middle
  leftSingle : leftGeometry.creationFrames.length=1
  rightSingle : rightGeometry.creationFrames.length=1

/-- A single unsafe normal COPY FUNCTION APP chooses actual cuts internally
and forces their GIVEN public provenance to the actual final safe event.
FIRST safety is observed in the actual middle; no global-middle safety,
caller leaf/frame, desired old iso or physical equality is supplied. -/
theorem single_unsafe_copy_function_app_inputs
    {original : LTerm} {prior : List Path}
    (initial : INIT original) (prefixHistory : History prior original source)
    (sourceClosed : Closed source.erase)
    (event : SelectedOldTurn F source degree pre middle target site)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (leftOccurs : ArgumentOccurrence event.body.erase (leftParent++[.fn]))
    (rightOccurs : ArgumentOccurrence event.body.erase (rightParent++[.fn]))
    (leftLookup : target.subterm (site++(leftParent++[.fn]))=some (.app leftStamp leftFn leftArg))
    (rightLookup : target.subterm (site++(rightParent++[.fn]))=some (.app rightStamp rightFn rightArg))
    (leftChain : PrerequisiteChain target leftStart es)
    (rightChain : PrerequisiteChain target rightStart fs)
    (iso : ChainIncidenceIso (chainSyntaxIncidence target (event.final_history.closed sourceClosed) es)
      (chainSyntaxIncidence target (event.final_history.closed sourceClosed) fs))
    (leftMember : (site++(leftParent++[.fn]))∈es)
    (rightMember : (site++(rightParent++[.fn]))∈fs)
    (leftOtherSafe : ∀e∈es,e≠site++(leftParent++[.fn]) →degreeReadSafe degree (target.labelAt e))
    (rightOtherSafe : ∀e∈fs,e≠site++(rightParent++[.fn]) →degreeReadSafe degree (target.labelAt e))
    (leftFirstSafe : ∀node,middle.subterm ((site++[.fn,.body])++(leftParent++[.fn]))=some node →node.label.OuterBarsSafe (fun x=>x≠degree))
    (rightFirstSafe : ∀node,middle.subterm ((site++[.fn,.body])++(rightParent++[.fn]))=some node →node.label.OuterBarsSafe (fun x=>x≠degree)) :
    Nonempty (SingleUnsafeCopyFunctionAppInputs event sourceClosed leftStart rightStart leftParent rightParent es fs) := by
  obtain ⟨cuts⟩:=copy_function_app_cuts initial prefixHistory sourceClosed event selected sourceSafe leftOccurs rightOccurs
    leftLookup rightLookup leftChain rightChain iso leftMember rightMember leftOtherSafe rightOtherSafe
  obtain ⟨ll,ls,⟨lg⟩⟩:=(cuts.left.asTrueSpine cuts.leftTrue).incidence_leaf_output sourceClosed cuts.left.lookup
  obtain ⟨rl,rs,⟨rg⟩⟩:=(cuts.right.asTrueSpine cuts.rightTrue).incidence_leaf_output sourceClosed cuts.right.lookup
  obtain ⟨lp,lsite,la,lc,le,lr,lcur,lt,lmid,lframes⟩:=
    geometry_final_safe event lg rfl cuts.leftEdge leftOccurs leftFirstSafe
  obtain ⟨rp,rsite,ra,rc,re,rr,rcur,rt,rmid,rframes⟩:=
    geometry_final_safe event rg rfl cuts.rightEdge rightOccurs rightFirstSafe
  exact ⟨{ toCopyFunctionAppCuts:=cuts
           leftLeaf:=ll, rightLeaf:=rl, leftSnapshot:=ls, rightSnapshot:=rs
           leftGeometry:=lg, rightGeometry:=rg
           leftLeafPre:=lp, rightLeafPre:=rp, leftLeafSite:=lsite, rightLeafSite:=rsite
           leftLeafAfter:=la, rightLeafAfter:=ra, leftLeafContinuation:=lc, rightLeafContinuation:=rc
           leftLeafReader:=lr, rightLeafReader:=rr, leftLeafEdge:=le, rightLeafEdge:=re
           leftLeafCurrent:=lcur, rightLeafCurrent:=rcur, leftLeafTarget:=lt, rightLeafTarget:=rt
           leftLeafMiddle:=lmid, rightLeafMiddle:=rmid, leftSingle:=lframes, rightSingle:=rframes }⟩
end Lamping.AG
