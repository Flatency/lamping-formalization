import Lamping.Lamping.ActualPrerequisiteSignedSlots
import Lamping.Lamping.CanonicalAfterFarComparison
namespace Lamping.AG
open Graph Lambda Lambda.Labelled SyntaxIncidence

private theorem reading_near_proper
    (reading : PrerequisiteReadsDirected t reader edge forward) :
    ∃v : ProperPosition t,
      if forward then Source t edge (some v) else Target t edge (some v) := by
  cases forward with
  | false =>
    rcases reading.1 with ⟨a,fn,arg,lookup,eq⟩ | ⟨a,body,lookup,eq⟩
    · have lengths:=congrArg List.length (eq.symm.trans reading.2);simp at lengths
    · exact ⟨⟨reader,Or.inr ⟨a,body,lookup⟩⟩,Or.inl reading.2⟩
  | true =>
    rcases reading.1 with ⟨a,fn,arg,lookup,eq⟩ | ⟨a,body,lookup,eq⟩
    · exact ⟨⟨reader,Or.inl ⟨a,fn,arg,lookup⟩⟩,⟨.fn,_,_,eq,lookup,.fn⟩⟩
    · have lengths:=congrArg List.length (eq.symm.trans reading.2);simp at lengths

/-- Proper near endpoints are consequences of the two actual readings;
proper far endpoints are the canonical AFTER outputs. -/
private theorem same_far_kind
    (history : History historySites initialSource current) (initial : INIT initialSource)
    (leftLookup : current.subterm le=some ln) (rightLookup : current.subterm re=some rn)
    (head : ln.label=rn.label)
    (leftRead : PrerequisiteReadsDirected current lr le forward)
    (rightRead : PrerequisiteReadsDirected current rr re forward)
    (ls : IncomingIncidenceSnapshot current le) (rs : IncomingIncidenceSnapshot current re)
    (lf : ls.far forward=some lv) (rf : rs.far forward=some rv) :
    ∃kind,ProperKind current lv kind ∧ProperKind current rv kind := by
  obtain ⟨nearL,leftNear⟩:=reading_near_proper leftRead
  obtain ⟨nearR,rightNear⟩:=reading_near_proper rightRead
  cases forward with
  | false =>
    change ls.fromVertex=some lv at lf
    change rs.fromVertex=some rv at rf
    have leftSource : Source current le (some lv) := lf ▸ ls.fromSpec
    have rightSource : Source current re (some rv) := rf ▸ rs.fromSpec
    obtain ⟨sk,tk,lk,rk,_⟩:=history.equal_label_endpoint_kinds initial leftLookup rightLookup head
      leftSource rightSource leftNear rightNear
    exact ⟨sk,lk,rk⟩
  | true =>
    change ls.toVertex=some lv at lf
    change rs.toVertex=some rv at rf
    have leftTarget : Target current le (some lv) := lf ▸ ls.toSpec
    have rightTarget : Target current re (some rv) := rf ▸ rs.toSpec
    obtain ⟨sk,tk,_,_,lk,rk⟩:=history.equal_label_endpoint_kinds initial leftLookup rightLookup head
      leftNear rightNear leftTarget rightTarget
    exact ⟨tk,lk,rk⟩

private theorem snapshot_of_lookup (closed : Closed current.erase)
    (lookup : current.subterm edge=some node) : Nonempty (IncomingIncidenceSnapshot current edge) := by
  let e : Edge current:=⟨edge,by rw [←LTerm.erase_subterm,lookup];rfl⟩
  obtain ⟨s,ss⟩:=source_total current e
  obtain ⟨t,ts⟩:=target_total current closed e
  exact ⟨⟨s,t,ss,ts⟩⟩

/-- Natural parent geometry removes the AFTER-only comparator's opposite
case. No orientation, endpoint kind or source isomorphism is a premise. -/
theorem actual_parent_cuts_canonical_far_comparison
    {initialSource source current : LTerm} {prior ps F : List Path} {degree : Label} {n : Marked}
    (initial : INIT initialSource) (prefixHistory : History prior initialSource source)
    (sourceClosed : Closed source.erase)
    (old : Marked.RelativeOldHistory F ps (Marked.mark F source.erase) n)
    (labels : History ps source current)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (leftChain : PrerequisiteChain current leftStart leftEdges)
    (rightChain : PrerequisiteChain current rightStart rightEdges)
    (wholeIso : ChainIncidenceIso
      (chainSyntaxIncidence current (labels.closed sourceClosed) leftEdges)
      (chainSyntaxIncidence current (labels.closed sourceClosed) rightEdges)) :
    ((∀e∈leftEdges,degreeReadSafe degree (current.labelAt e)) ∧
     (∀e∈rightEdges,degreeReadSafe degree (current.labelAt e))) ∨
    ∃leftCut : ActualUnsafeMarkerCut F ps source current degree leftStart leftEdges,
      ∃rightCut : ActualUnsafeMarkerCut F ps source current degree rightStart rightEdges,
        leftCut.before.length=rightCut.before.length ∧
        leftCut.before.map current.labelAt=rightCut.before.map current.labelAt ∧
        current.labelAt leftCut.edge=current.labelAt rightCut.edge ∧
        leftCut.after.map current.labelAt=rightCut.after.map current.labelAt ∧
        ((leftCut.after=[] ∧rightCut.after=[]) ∨
         (leftCut.after≠[] ∧rightCut.after≠[] ∧
          ∃leftSnapshot rightSnapshot,
            ∃left : CanonicalAfterFarOutput labels leftCut leftSnapshot,
              ∃right : CanonicalAfterFarOutput labels rightCut rightSnapshot,
                CanonicalFarFullComparison sourceClosed left right)) := by
  classical
  have full:=prefixHistory.append labels
  rcases actual_first_unsafe_current_after initial prefixHistory old labels selected sourceSafe
      (labels.closed sourceClosed) leftChain rightChain wholeIso with safe | cuts
  · exact Or.inl safe
  · obtain ⟨lc,rc,len,front,head,back,_ll,_rl,emptyOr⟩:=cuts
    refine Or.inr ⟨lc,rc,len,front,head,back,?_⟩
    rcases emptyOr with empty | more
    · exact Or.inl empty
    · obtain ⟨lm,rm,direction,_ln,_rn,_lg,_rg,_lchain,_rchain,afterIso⟩:=more
      obtain ⟨ls⟩:=snapshot_of_lookup (labels.closed sourceClosed) lc.lookup
      obtain ⟨rs⟩:=snapshot_of_lookup (labels.closed sourceClosed) rc.lookup
      obtain ⟨left,right,result⟩:=canonical_after_far_comparison initial prefixHistory sourceClosed old labels selected sourceSafe
        lc rc lm rm ls rs (Classical.choice afterIso)
      refine Or.inr ⟨lm,rm,ls,rs,left,right,?_⟩
      rcases result with safe | same | opposite
      · exact safe.2
      · obtain ⟨_,_,_,_,_,good⟩:=same;exact good
      · obtain ⟨a,b,_ae,_be,opposed,beforeEq,_headEq⟩:=opposite
        have rightRead : PrerequisiteReadsDirected current rc.reader rc.edge lc.forward := direction ▸ rc.reading
        have nodeEq : lc.node.label=rc.node.label := by
          simpa only [LTerm.labelAt,lc.lookup,rc.lookup,Option.map_some,Option.some.injEq] using head
        have rightFar : rs.far lc.forward=some right.currentProper := by rw [direction];exact right.farEq
        have kind:=same_far_kind full initial lc.lookup rc.lookup nodeEq lc.reading rightRead ls rs left.farEq rightFar
        obtain ⟨lf,ss,vs,lt,lwalk⟩:=left.currentChain.signed_path
        obtain ⟨rf,ts,ws,rt,rwalk⟩:=right.currentChain.signed_path
        have lfEq : lf=left.currentProper:=Option.some.inj (Target.unique lt (Or.inl rfl))
        have rfEq : rf=right.currentProper:=Option.some.inj (Target.unique rt (Or.inl rfl))
        subst lf;subst rf
        have signEq:=lwalk.signs_eq full initial rwalk back kind
        obtain ⟨_av,_ap,_ai,asign⟩:=a.signed_slot lwalk (Or.inl rfl)
        obtain ⟨_bv,_bp,_bi,bsign⟩:=b.signed_slot rwalk (Or.inl rfl)
        have ordinal : a.before.length=b.before.length := by
          have size:=congrArg List.length beforeEq
          simpa only [List.length_map] using size
        have equal : a.forward=b.forward := by
          rw [signEq,ordinal] at asign
          exact Option.some.inj (asign.symm.trans bsign)
        exact False.elim (opposed equal)
end Lamping.AG
