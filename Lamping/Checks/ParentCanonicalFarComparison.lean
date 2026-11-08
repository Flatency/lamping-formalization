import Lamping.Lamping.ParentCanonicalFarComparison
import Lamping.Checks.CanonicalAfterFarComparison
import Lamping.Checks.SingleUnsafeCopyFunctionAppInputs
import Lamping.Checks.ActualPrerequisiteSignedSlots
namespace Lamping.Checks.ParentCanonicalFarComparisonChecks
open Graph Lambda Lambda.Labelled AG SyntaxIncidence

section Helpers
variable {source t original : LTerm}

private theorem locate
    (chain : PrerequisiteChain t start edges)
    (cut : ActualUnsafeMarkerCut F ps source t degree start edges)
    (expected : edges=before++head::after)
    (otherSafe : ∀e∈edges,e≠head →degreeReadSafe degree (t.labelAt e)) :
    cut.edge=head ∧cut.before=before ∧cut.after=after := by
  have inside : cut.edge∈edges := Eq.mpr (congrArg (fun xs : List Path=>cut.edge∈xs) cut.split) (List.mem_append_right _ List.mem_cons_self)
  have chosen : cut.edge=head := by
    classical
    by_cases same : cut.edge=head
    · exact same
    · exact False.elim (cut.marked (otherSafe _ inside same _ (by simp only [LTerm.labelAt,cut.lookup,Option.map_some])))
  have split:=cut.split
  rw [chosen] at split
  obtain ⟨front,back⟩:=chain.first_created_split_unique split expected
  exact ⟨chosen,front,back⟩

/-- Test assembly calls the natural high and then only locates its returned
cuts at the fixture's uniquely unsafe heads. No old chains/iso are supplied. -/
private theorem direct_nonempty
    (initial : INIT original) (prior : History priorSites original source)
    (closed : Closed source.erase)
    (old : Marked.RelativeOldHistory F ps (Marked.mark F source.erase) n)
    (labels : History ps source t)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (safe : source.OuterBarsSafe (fun x=>x≠degree))
    (lc : PrerequisiteChain t ls es) (rc : PrerequisiteChain t rs fs)
    (iso : ChainIncidenceIsomorphic (chainSyntaxIncidence t (labels.closed closed) es)
      (chainSyntaxIncidence t (labels.closed closed) fs))
    (le : es=lb++lh::la) (re : fs=rb++rh::ra)
    (lm : ¬degreeReadSafe degree (t.labelAt lh))
    (los : ∀e∈es,e≠lh →degreeReadSafe degree (t.labelAt e))
    (ros : ∀e∈fs,e≠rh →degreeReadSafe degree (t.labelAt e))
    (more : la≠[]) :
    ∃left : ActualUnsafeMarkerCut F ps source t degree ls es,
      ∃right : ActualUnsafeMarkerCut F ps source t degree rs fs,
        left.before=lb ∧right.before=rb ∧left.after=la ∧right.after=ra ∧
        ∃lshot rshot,
          ∃lout : CanonicalAfterFarOutput labels left lshot,
            ∃rout : CanonicalAfterFarOutput labels right rshot,
              CanonicalFarFullComparison closed lout rout := by
  rcases actual_parent_cuts_canonical_far_comparison initial prior closed old labels selected safe lc rc (Classical.choice iso) with all | cuts
  · apply False.elim;apply lm;apply all.1 lh
    rw [le];exact List.mem_append_right _ List.mem_cons_self
  · obtain ⟨left,right,_len,_front,_head,_back,result⟩:=cuts
    obtain ⟨_lh,lf,lae⟩:=locate lc left le los
    obtain ⟨_rh,rf,rae⟩:=locate rc right re ros
    refine ⟨left,right,lf,rf,lae,rae,?_⟩
    rcases result with empty | good
    · exact False.elim (more (lae.symm.trans empty.1))
    · exact good.2.2

end Helpers

namespace TwoCopies
open ForwardFarChainComparisonChecks.TwoCopies

theorem actual_same_parent_singleton_fars :
    ∃left : ActualUnsafeMarkerCut F [[]] source target (.atom 1) [.fn] [[.fn,.fn],[.fn,.fn,.fn]],
      ∃right : ActualUnsafeMarkerCut F [[]] source target (.atom 1) [.fn] [[.fn,.fn],[.fn,.fn,.fn]],
        left.before=[] ∧right.before=[] ∧left.after=[[.fn,.fn,.fn]] ∧right.after=[[.fn,.fn,.fn]] ∧
        ∃ls rs,∃lo : CanonicalAfterFarOutput event.final_history left ls,
          ∃ro : CanonicalAfterFarOutput event.final_history right rs,CanonicalFarFullComparison closed lo ro := by
  apply direct_nonempty initial (.nil source) closed event.final_old event.final_history selected
    (initial.outerBarsSafe _) leftRemaining leftRemaining
    (actual_chain_iso_of_labels event.final_history initial targetClosed leftRemaining leftRemaining rfl) rfl rfl
  · intro safe
    exact CanonicalAfterFarComparisonChecks.TwoCopies.leftMarked (safe _ rfl)
  · intro e member different
    rcases List.mem_cons.mp member with eq |mem
    · exact False.elim (different eq)
    · have eq:=List.mem_singleton.mp mem;subst e
      intro label same
      have eq : label=Label.atom 12:=Option.some.inj same.symm
      subst label;trivial
  · intro e member different
    rcases List.mem_cons.mp member with eq |mem
    · exact False.elim (different eq)
    · have eq:=List.mem_singleton.mp mem;subst e
      intro label same
      have eq : label=Label.atom 12:=Option.some.inj same.symm
      subst label;trivial
  · decide
/-- The two distinct copied APPs have equal safe singleton tails, but
unequal parent head labels; this is an all-safe direct call on those tails. -/
theorem actual_distinct_all_safe_tails :
    (∀e∈([[.fn,.fn,.fn]] : List Path),degreeReadSafe (.atom 1) (target.labelAt e)) ∧
    (∀e∈([[.arg,.fn,.fn]] : List Path),degreeReadSafe (.atom 1) (target.labelAt e)) := by
  rcases actual_parent_cuts_canonical_far_comparison initial (.nil source) closed event.final_old event.final_history selected
      (initial.outerBarsSafe _) leftTail rightTail
      (Classical.choice (actual_chain_iso_of_labels event.final_history initial targetClosed leftTail rightTail rfl)) with all | cuts
  · exact all
  · obtain ⟨l,_r,_⟩:=cuts
    have mem : l.edge∈([[.fn,.fn,.fn]] : List Path) :=
      Eq.mpr (congrArg (fun xs : List Path=>l.edge∈xs) l.split) (List.mem_append_right _ List.mem_cons_self)
    have eq:=List.mem_singleton.mp mem
    have lookup : target.subterm l.edge=some (.lam (.atom 12) (.var (.atom 13) 0)) := by rw [eq];rfl
    have same:=Option.some.inj (l.lookup.symm.trans lookup)
    exact False.elim (l.marked (by rw [same];trivial))

theorem parent_heads_really_differ : target.labelAt [.fn,.fn]≠target.labelAt [.arg,.fn] := by
  intro eq
  cases eq
end TwoCopies

namespace ExistingNoninitial
open SingleUnsafeCopyFunctionAppInputsChecks

theorem actual_pre_before_after_distinct :
    ∃left : ActualUnsafeMarkerCut F [[.fn],[.arg]] source target (.atom 6) leftStart es,
      ∃right : ActualUnsafeMarkerCut F [[.fn],[.arg]] source target (.atom 6) rightStart fs,
        left.before=[leftStart] ∧right.before=[rightStart] ∧
        left.after=[leftHead++[.fn]] ∧right.after=[rightHead++[.fn]] ∧
        ∃ls rs,∃lo : CanonicalAfterFarOutput event.final_history left ls,
          ∃ro : CanonicalAfterFarOutput event.final_history right rs,CanonicalFarFullComparison sourceClosed lo ro := by
  apply direct_nonempty initial prefixHistory sourceClosed event.final_old event.final_history selected sourceSafe
    leftChain rightChain currentIso rfl rfl
  · intro safe
    have marked : ¬copiedArgument.label.OuterBarsSafe (fun x=>x≠Label.atom 6) := by
      intro h;change (Label.atom 6≠Label.atom 6) ∧True at h;exact h.1 rfl
    exact marked (safe _ rfl)
  · exact leftOtherSafe
  · exact rightOtherSafe
  · decide
end ExistingNoninitial

namespace MultipleAfter
abbrev I : Term:=WrappedSuccessfulChains.I
abbrev bare : Term:=.app (.lam (.app (.lam (.app (.var 0) (.var 0)))
  (.app (.lam (.app (.lam (.app (.var 0) (.var 0))) (.app (.var 0) I))) (.app (.var 0) I)))) I
abbrev original : LTerm:=initLabels bare
abbrev contract:=WrappedSuccessfulChains.contractRoot
abbrev modifyBody (f : LTerm→LTerm) : LTerm→LTerm
  | .app a (.lam b body) arg=>.app a (.lam b (f body)) arg
  | t=>t
abbrev modifyRight (f : LTerm→LTerm) : LTerm→LTerm
  | .app a fn arg=>.app a fn (f arg)
  | t=>t
abbrev modifyLeft (f : LTerm→LTerm) : LTerm→LTerm
  | .app a fn arg=>.app a (f fn) arg
  | t=>t
abbrev first : LTerm:=modifyBody (modifyRight (modifyLeft (fun t=>match t with
  | .lam a b=>.lam a (contract b) |t=>t))) original
abbrev source : LTerm:=modifyBody contract first
abbrev middle : LTerm:=modifyBody (modifyLeft contract) source
abbrev target : LTerm:=modifyBody (modifyRight contract) middle
abbrev left : Path:=[.fn,.body,.fn]
abbrev right : Path:=[.fn,.body,.arg]
abbrev F : List Path:=[left,right]
abbrev markRoot (t : Marked) : Marked:=match t with | .red _ b a=>Marked.contract b a |t=>t
abbrev markBody (f : Marked→Marked) : Marked→Marked
  | .app a (.lam b) arg=>.app a (.lam (f b)) arg
  |t=>t
abbrev markLeft (f : Marked→Marked) : Marked→Marked
  | .app a fn arg=>.app a (f fn) arg |t=>t
abbrev markRight (f : Marked→Marked) : Marked→Marked
  | .app a fn arg=>.app a fn (f arg) |t=>t
abbrev markedMiddle:=markBody (markLeft markRoot) (Marked.mark F source.erase)
abbrev markedTarget:=markBody (markRight markRoot) markedMiddle
abbrev body : LTerm:=match middle.subterm (right++[.fn,.body]) with |some t=>t |none=>middle
abbrev argument : LTerm:=match middle.subterm (right++[.arg]) with |some t=>t |none=>middle

def prefixHistory : History [[.fn,.body,.arg,.fn,.body],[.fn,.body]] original source:=
  .cons (.fn (.body (.arg (.fn (.body (.root _ _ _ _))))))
    (.cons (.fn (.body (.root _ _ _ _))) (.nil _))
def preHistory : History [left] source middle:=.cons (.fn (.body (.fn (.root _ _ _ _)))) (.nil _)
def event : SelectedOldTurn F source (.atom 8) [left] middle target right where
  markedBefore:=markedMiddle
  markedAfter:=markedTarget
  beforeOld:=.cons (.appL (.lam (.appL (.redRoot _ _ _)))) (by decide) (.nil _)
  reduction:=.appL (.lam (.appR (.redRoot _ _ _)))
  member:=by decide
  labels:=preHistory
  turn:=.fn (.body (.arg (.root _ _ _ _)))
  beta:=match middle.subterm right with |some t=>t.label |none=>.atom 0
  body:=body
  argument:=argument
  redex:=rfl

theorem initial : INIT original:=init_is_INIT _
theorem originalClosed : Closed original.erase:=by
  simp [Closed,Scoped,original,initLabels,initFrom,nodeCount,LTerm.erase]
theorem sourceClosed : Closed source.erase:=prefixHistory.closed originalClosed
theorem targetClosed : Closed target.erase:=event.final_history.closed sourceClosed

theorem selected (name : Path) (mem : name∈F) : source.degreeAt name=some (.atom 8) := by
  rcases List.mem_cons.mp mem with rfl |mem
  · rfl
  · have eq:=List.mem_singleton.mp mem;subst name;rfl

theorem sourceSafe : source.OuterBarsSafe (fun x=>x≠Label.atom 8) := by
  dsimp [source,first,original,bare,I,WrappedSuccessfulChains.I,contract,WrappedSuccessfulChains.contractRoot,
    modifyBody,modifyLeft,modifyRight,initLabels,initFrom,nodeCount,LTerm.contract,LTerm.subst,LTerm.single,LTerm.prepend,
    LTerm.rename,LTerm.lift,LTerm.label,Label.concat,Label.over,Label.under,Label.atom]
  simp only [LTerm.OuterBarsSafe,Label.OuterBarsSafe]
  decide
abbrev leftStart : Path:=right++[.fn,.arg]
abbrev rightStart : Path:=right++[.arg,.arg]
abbrev leftHead : Path:=right++[.fn,.fn]
abbrev rightHead : Path:=right++[.arg,.fn]
abbrev es : List Path:=[leftStart,leftHead,leftHead++[.fn],[.fn]]
abbrev fs : List Path:=[rightStart,rightHead,rightHead++[.fn],[.fn]]

def outerChain : PrerequisiteChain target [.fn] [[.fn]]:=.redex_lam (p:=[]) rfl

def leftJump : PrerequisiteChain target (leftHead++[.fn]) [[.fn]]:=
  .var (parent:=[.fn]) (rest:=[.arg,.fn,.fn,.fn]) rfl rfl rfl rfl outerChain

def rightJump : PrerequisiteChain target (rightHead++[.fn]) [[.fn]]:=
  .var (parent:=[.fn]) (rest:=[.arg,.arg,.fn,.fn]) rfl rfl rfl rfl outerChain

def leftTail : PrerequisiteChain target leftHead [leftHead++[.fn],[.fn]]:=
  .app rfl (by intro a b h;cases h) leftJump

def rightTail : PrerequisiteChain target rightHead [rightHead++[.fn],[.fn]]:=
  .app rfl (by intro a b h;cases h) rightJump

def leftChain : PrerequisiteChain target leftStart es:=
  .lam (parent:=right++[.fn]) (step:=.arg) rfl (by decide)
    (.app rfl (by intro a b h;cases h) leftTail)
def rightChain : PrerequisiteChain target rightStart fs:=
  .lam (parent:=right++[.arg]) (step:=.arg) rfl (by decide)
    (.app rfl (by intro a b h;cases h) rightTail)

theorem labelsEq : es.map target.labelAt=fs.map target.labelAt:=rfl

theorem currentIso : ChainIncidenceIsomorphic (chainSyntaxIncidence target targetClosed es) (chainSyntaxIncidence target targetClosed fs):=
  actual_chain_iso_of_labels (prefixHistory.append event.final_history) initial targetClosed leftChain rightChain labelsEq

theorem actual_read_labels :
    es.map target.labelAt=[some (.atom 16),some ((Label.atom 15).concat ((Label.atom 8).under.concat (.atom 18))),some (.atom 19),some (.atom 1)] ∧
    fs.map target.labelAt=[some (.atom 16),some ((Label.atom 15).concat ((Label.atom 8).under.concat (.atom 18))),some (.atom 19),some (.atom 1)] := ⟨rfl,rfl⟩

theorem leftMarked : ¬degreeReadSafe (.atom 8) (target.labelAt leftHead) := by
  intro safe
  have h:=safe ((Label.atom 15).concat ((Label.atom 8).under.concat (.atom 18))) rfl
  change (Label.atom 8≠Label.atom 8) ∧True at h
  exact h.1 rfl

theorem leftOtherSafe : ∀e∈es,e≠leftHead →degreeReadSafe (.atom 8) (target.labelAt e) := by
  intro e member different
  rcases List.mem_cons.mp member with rfl |member
  · intro label same
    have eq : label=Label.atom 16:=Option.some.inj same.symm
    subst label;trivial
  · rcases List.mem_cons.mp member with rfl |member
    · exact False.elim (different rfl)
    · rcases List.mem_cons.mp member with rfl |member
      · intro label same
        have eq : label=Label.atom 19:=Option.some.inj same.symm
        subst label;trivial
      · have eq:=List.mem_singleton.mp member;subst e
        intro label same
        have eq : label=Label.atom 1:=Option.some.inj same.symm
        subst label;trivial

theorem rightOtherSafe : ∀e∈fs,e≠rightHead →degreeReadSafe (.atom 8) (target.labelAt e) := by
  intro e member different
  rcases List.mem_cons.mp member with rfl |member
  · intro label same
    have eq : label=Label.atom 16:=Option.some.inj same.symm
    subst label;trivial
  · rcases List.mem_cons.mp member with rfl |member
    · exact False.elim (different rfl)
    · rcases List.mem_cons.mp member with rfl |member
      · intro label same
        have eq : label=Label.atom 19:=Option.some.inj same.symm
        subst label;trivial
      · have eq:=List.mem_singleton.mp member;subst e
        intro label same
        have eq : label=Label.atom 1:=Option.some.inj same.symm
        subst label;trivial

/-- Genuine four-READ chains: lambda ARG, marked copied APP, outer-bound
variable FUNCTION, then the applied outer lambda. AFTER has two edges. -/
theorem actual_two_edge_after_source_comparison :
    ∃lc : ActualUnsafeMarkerCut F [left,right] source target (.atom 8) leftStart es,
      ∃rc : ActualUnsafeMarkerCut F [left,right] source target (.atom 8) rightStart fs,
        lc.before=[leftStart] ∧rc.before=[rightStart] ∧
        lc.after=[leftHead++[.fn],[.fn]] ∧rc.after=[rightHead++[.fn],[.fn]] ∧
        ∃ls rs,∃lo : CanonicalAfterFarOutput event.final_history lc ls,
          ∃ro : CanonicalAfterFarOutput event.final_history rc rs,
            CanonicalFarFullComparison sourceClosed lo ro := by
  exact direct_nonempty initial prefixHistory sourceClosed event.final_old event.final_history selected sourceSafe
    leftChain rightChain currentIso rfl rfl leftMarked leftOtherSafe rightOtherSafe (by decide)

theorem actual_nonempty_context : INIT original ∧Closed original.erase ∧
    History [[.fn,.body,.arg,.fn,.body],[.fn,.body],left,right] original target ∧
    ([left] : List Path)≠[] ∧leftStart≠rightStart ∧
    es.length=4 ∧fs.length=4 ∧([leftHead++[.fn],[.fn]] : List Path).length=2 ∧
    ([rightHead++[.fn],[.fn]] : List Path).length=2 :=
  ⟨initial,originalClosed,prefixHistory.append event.final_history,by decide,by decide,rfl,rfl,rfl,rfl⟩

/-- This is the lexical zero-jump inside the two-edge AFTER, not an extra
edge or a fabricated successful empty chain. -/
theorem actual_zero_jump_tail :
    PrerequisiteChain target (leftHead++[.fn]) [[.fn]] ∧
    PrerequisiteChain target (rightHead++[.fn]) [[.fn]] ∧
    leftHead++[.fn]≠([.fn] : Path) ∧rightHead++[.fn]≠([.fn] : Path) :=
  ⟨leftJump,rightJump,by decide,by decide⟩
end MultipleAfter

namespace EmptyTerminal
open DirectedReadingDecompositionChecks
abbrev old:=DirectedMarkerLeafWordsChecks.RootOverlap.old
abbrev selected:=DirectedMarkerLeafWordsChecks.RootOverlap.selected

theorem actual_opposite_parent_empty_branch :
    ∃l : ActualUnsafeMarkerCut [[.fn]] [[.fn]] source target (.atom 2) [] [[.fn]],
      ∃r : ActualUnsafeMarkerCut [[.fn]] [[.fn]] source target (.atom 2) [.fn] [[.fn]],
        l.after=[] ∧r.after=[] := by
  rcases actual_parent_cuts_canonical_far_comparison initial (.nil source) closed old history selected
      (initial.outerBarsSafe _) successful_function successful_context (.refl _) with all |cuts
  · have bad:=all.1 [.fn] (by simp) _ rfl
    change ((.atom 2 : Label)≠.atom 2) ∧_ at bad
    exact False.elim (bad.1 rfl)
  · obtain ⟨l,r,_len,_front,_head,_back,result⟩:=cuts
    have size:=congrArg List.length l.split
    simp only [List.length_append,List.length_cons,List.length_nil] at size
    have le : l.after=[]:=List.length_eq_zero_iff.mp (by omega)
    rcases result with empty |good
    · exact ⟨l,r,empty⟩
    · exact False.elim (good.1 le)
end EmptyTerminal

#print axioms actual_parent_cuts_canonical_far_comparison
#print axioms TwoCopies.actual_same_parent_singleton_fars
#print axioms TwoCopies.actual_distinct_all_safe_tails
#print axioms TwoCopies.parent_heads_really_differ
#print axioms EmptyTerminal.actual_opposite_parent_empty_branch
#print axioms ExistingNoninitial.actual_pre_before_after_distinct
#print axioms MultipleAfter.actual_read_labels
#print axioms MultipleAfter.actual_two_edge_after_source_comparison
#print axioms MultipleAfter.actual_nonempty_context
#print axioms MultipleAfter.actual_zero_jump_tail
#print axioms CanonicalAfterFarComparisonChecks.TerminalBoundary.actual_terminal_opposite_not_full_source_match
#print axioms ActualPrerequisiteSignedSlotsChecks.TwoCopies.actual_same_edge_two_legal_directions
end Lamping.Checks.ParentCanonicalFarComparisonChecks
