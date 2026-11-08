import Lamping.Lamping.SingleUnsafeCopyArgumentCuts
import Lamping.Checks.WrappedSuccessfulChains
namespace Lamping.Checks.SingleUnsafeCopyArgumentCutsChecks
open Graph Lambda Lambda.Labelled AG SyntaxIncidence
abbrev I : Term:=WrappedSuccessfulChains.I
abbrev Delta : Term:=.lam (.app (.var 0) (.var 0))
abbrev bare : Term:=.app (.lam (.app (.var 0) (.var 0)))
  (.app (.lam (.app (.lam (.app (.var 0) (.var 0))) (.app I (.var 0)))) Delta)
abbrev original : LTerm:=initLabels bare
abbrev first : LTerm:=match original with
  | .app b f (.app c (.lam a body) arg)=>.app b f (.app c (.lam a (WrappedSuccessfulChains.contractRoot body)) arg)
  | t=>t
abbrev source : LTerm:=WrappedSuccessfulChains.contractRoot first
abbrev middle : LTerm:=match source with | .app b f a=>.app b (WrappedSuccessfulChains.contractRoot f) a |t=>t
abbrev target : LTerm:=match middle with | .app b f a=>.app b f (WrappedSuccessfulChains.contractRoot a) |t=>t
abbrev body : LTerm:=match middle with | .app _ _ (.app _ (.lam _ b) _)=>b |t=>t
abbrev argument : LTerm:=match middle with | .app _ _ (.app _ _ a)=>a |t=>t
abbrev F : List Path:=[[.fn],[.arg]]
abbrev markRoot (t : Marked) : Marked:=match t with | .red _ b a=>Marked.contract b a |t=>t
abbrev markedMiddle : Marked:=match Marked.mark F source.erase with
  | .app l f a=>.app l (markRoot f) a |t=>t
abbrev markedTarget : Marked:=match markedMiddle with
  | .app l f a=>.app l f (markRoot a) |t=>t

def prefixHistory : History [[.arg,.fn,.body],[]] original source:=
  .cons (.arg (.fn (.body (.root _ _ _ _)))) (.cons (.root _ _ _ _) (.nil _))
def preHistory : History [[.fn]] source middle:=.cons (.fn (.root _ _ _ _)) (.nil _)
def turn : StepAt [.arg] middle target:=.arg (.root _ _ _ _)
def event : SelectedOldTurn F source (.atom 6) [[.fn]] middle target [.arg] where
  markedBefore:=markedMiddle
  markedAfter:=markedTarget
  beforeOld:=.cons (.appL (.redRoot _ _ _)) (by decide) (.nil _)
  reduction:=.appR (.redRoot _ _ _)
  member:=by decide
  labels:=preHistory
  turn:=turn
  beta:=match middle with | .app _ _ (.app b _ _)=>b |t=>t.label
  body:=body
  argument:=argument
  redex:=rfl

theorem initial : INIT original:=init_is_INIT _
theorem originalClosed : Closed original.erase:=by simp [Closed,Scoped,original,initLabels,initFrom,nodeCount,LTerm.erase]
theorem sourceClosed : Closed source.erase:=prefixHistory.closed originalClosed
theorem targetClosed : Closed target.erase:=event.final_history.closed sourceClosed
theorem selected (name : Path) (member : name∈F) : source.degreeAt name=some (.atom 6) := by
  rcases List.mem_cons.mp member with rfl |member
  · rfl
  · have same:=List.mem_singleton.mp member;subst name;rfl
abbrev copiedDelta : LTerm:=.lam ((Label.atom 15).concat ((Label.atom 6).under.concat (.atom 16)))
  (.app (.atom 17) (.var (.atom 18) 0) (.var (.atom 19) 0))
abbrev leftHead : Path:=[.arg,.fn,.arg]
abbrev rightHead : Path:=[.arg,.arg,.arg]
abbrev leftStart : Path:=leftHead++[.body]
abbrev rightStart : Path:=rightHead++[.body]
abbrev es : List Path:=[leftHead++[.body,.fn],leftHead,[.arg,.fn,.fn]]
abbrev fs : List Path:=[rightHead++[.body,.fn],rightHead,[.arg,.arg,.fn]]
def leftHeadChain : PrerequisiteChain target leftHead [leftHead,[.arg,.fn,.fn]]:=
  .lam (parent:=[.arg,.fn]) (step:=.arg) rfl (by decide) (.redex_app (p:=[.arg,.fn]) rfl)
def rightHeadChain : PrerequisiteChain target rightHead [rightHead,[.arg,.arg,.fn]]:=
  .lam (parent:=[.arg,.arg]) (step:=.arg) rfl (by decide) (.redex_app (p:=[.arg,.arg]) rfl)
def leftChain : PrerequisiteChain target leftStart es:=
  .app rfl (by intro l b wrong;cases wrong)
    (.var (leaf:=leftHead++[.body,.fn]) (parent:=leftHead) (rest:=[.fn]) rfl rfl rfl rfl leftHeadChain)
def rightChain : PrerequisiteChain target rightStart fs:=
  .app rfl (by intro l b wrong;cases wrong)
    (.var (leaf:=rightHead++[.body,.fn]) (parent:=rightHead) (rest:=[.fn]) rfl rfl rfl rfl rightHeadChain)
theorem leftLookup : target.subterm leftHead=some copiedDelta:=rfl
theorem rightLookup : target.subterm rightHead=some copiedDelta:=rfl
theorem labelVectors : es.map target.labelAt=fs.map target.labelAt:=rfl
theorem actual_three_read_labels :
    es.map target.labelAt=[some (.atom 18),some copiedDelta.label,some (.atom 13)] ∧
    fs.map target.labelAt=[some (.atom 18),some copiedDelta.label,some (.atom 13)] := ⟨rfl,rfl⟩
theorem currentIso : ChainIncidenceIsomorphic (chainSyntaxIncidence target targetClosed es) (chainSyntaxIncidence target targetClosed fs) :=
  actual_chain_iso_of_labels (prefixHistory.append event.final_history) initial targetClosed leftChain rightChain labelVectors

theorem leftOtherSafe : ∀e∈es,e≠leftHead →degreeReadSafe (.atom 6) (target.labelAt e) := by
  intro e inside notHead
  rcases List.mem_cons.mp inside with rfl |inside
  · intro label same
    have eq : label=Label.atom 18:=Option.some.inj same.symm
    subst label;trivial
  · rcases List.mem_cons.mp inside with rfl |inside
    · exact False.elim (notHead rfl)
    · have eq:=List.mem_singleton.mp inside;subst e
      intro label same
      have eq : label=Label.atom 13:=Option.some.inj same.symm
      subst label;trivial
theorem rightOtherSafe : ∀e∈fs,e≠rightHead →degreeReadSafe (.atom 6) (target.labelAt e) := by
  intro e inside notHead
  rcases List.mem_cons.mp inside with rfl |inside
  · intro label same
    have eq : label=Label.atom 18:=Option.some.inj same.symm
    subst label;trivial
  · rcases List.mem_cons.mp inside with rfl |inside
    · exact False.elim (notHead rfl)
    · have eq:=List.mem_singleton.mp inside;subst e
      intro label same
      have eq : label=Label.atom 13:=Option.some.inj same.symm
      subst label;trivial

theorem sourceSafe : source.OuterBarsSafe (fun x=>x≠Label.atom 6) := by
  dsimp [source,first,original,bare,I,Delta,WrappedSuccessfulChains.I,WrappedSuccessfulChains.contractRoot,
    initLabels,initFrom,nodeCount,LTerm.contract,LTerm.subst,LTerm.single,LTerm.prepend,
    LTerm.rename,LTerm.lift,LTerm.label,Label.concat,Label.over,Label.under,Label.atom]
  simp only [LTerm.OuterBarsSafe,Label.OuterBarsSafe]
  decide

theorem leftLastSafe : ∀node,middle.subterm ([.arg,.fn,.body]++([.fn]++[.arg]))=some node →node.label.OuterBarsSafe (fun x=>x≠Label.atom 6) := by
  intro node lookup
  have nodeEq:node=.var (.atom 15) 0:=Option.some.inj lookup.symm
  rw [nodeEq];trivial
theorem rightLastSafe : ∀node,middle.subterm ([.arg,.fn,.body]++([.arg]++[.arg]))=some node →node.label.OuterBarsSafe (fun x=>x≠Label.atom 6) := by
  intro node lookup
  have nodeEq:node=.var (.atom 15) 0:=Option.some.inj lookup.symm
  rw [nodeEq];trivial

theorem actual_new_cuts : Nonempty (SingleUnsafeCopyArgumentCuts event sourceClosed leftStart rightStart [.fn] [.arg] es fs) := by
  obtain ⟨iso⟩:=currentIso
  exact single_unsafe_copy_argument_cuts initial prefixHistory sourceClosed event selected sourceSafe
    (by rfl) (by rfl) leftLookup rightLookup leftChain rightChain iso (by simp [es]) (by simp [fs]) leftOtherSafe rightOtherSafe

theorem middleUnsafe : ∃node,middle.subterm [.fn,.fn,.arg]=some node ∧
    ¬node.label.OuterBarsSafe (fun x=>x≠Label.atom 6) := by
  refine ⟨copiedDelta,rfl,?_⟩
  intro safe
  change (Label.atom 6≠Label.atom 6) ∧True at safe
  exact safe.1 rfl

theorem actual_history_and_zero_jump : INIT original ∧Closed original.erase ∧
    History [[.arg,.fn,.body],[],[.fn],[.arg]] original target ∧
    event.labels=preHistory ∧([[.fn]] : List Path)≠[] ∧leftStart≠rightStart ∧
    target.subterm leftStart=some (.app (.atom 17) (.var (.atom 18) 0) (.var (.atom 19) 0)) ∧
    target.subterm rightStart=some (.app (.atom 17) (.var (.atom 18) 0) (.var (.atom 19) 0)) ∧
    PrerequisitePrefix target (leftHead++[.body,.fn]) [] leftHead ∧
    PrerequisitePrefix target (rightHead++[.body,.fn]) [] rightHead := by
  refine ⟨initial,originalClosed,prefixHistory.append event.final_history,rfl,by decide,by decide,rfl,rfl,?_,?_⟩
  · exact .var rfl rfl rfl rfl .refl
  · exact .var rfl rfl rfl rfl .refl

/-- Direct top consumption proves all three literal slots, rather than
replacing the delta BODY chain by a head-only or self-pair regression. -/
theorem actual_nonempty_before_after_cuts : ∃out : SingleUnsafeCopyArgumentCuts event sourceClosed leftStart rightStart [.fn] [.arg] es fs,
    out.left.before=[leftHead++[.body,.fn]] ∧out.right.before=[rightHead++[.body,.fn]] ∧
    out.left.edge=leftHead ∧out.right.edge=rightHead ∧
    out.left.after=[[.arg,.fn,.fn]] ∧out.right.after=[[.arg,.arg,.fn]] ∧
    out.left.before.length=1 ∧out.right.before.length=1 ∧out.left.after.length=1 ∧out.right.after.length=1 ∧
    out.left.reader=leftHead ∧out.right.reader=rightHead ∧out.left.forward=false ∧out.right.forward=false ∧
    out.left.before≠[] ∧out.right.before≠[] ∧out.left.after≠[] ∧out.right.after≠[] ∧
    ChainIncidenceIsomorphic (chainSyntaxIncidence target targetClosed (out.left.edge::out.left.after))
      (chainSyntaxIncidence target targetClosed (out.right.edge::out.right.after)) ∧
    ChainIncidenceIsomorphic (chainSyntaxIncidence target targetClosed out.left.after)
      (chainSyntaxIncidence target targetClosed out.right.after) := by
  obtain ⟨out⟩:=actual_new_cuts
  have ls:=out.left.split
  rw [out.leftEdge] at ls
  have rs:=out.right.split
  rw [out.rightEdge] at rs
  obtain ⟨lb,la⟩:=leftChain.first_created_split_unique ls (by rfl : es=[leftHead++[.body,.fn]]++leftHead::[[.arg,.fn,.fn]])
  obtain ⟨rb,ra⟩:=rightChain.first_created_split_unique rs (by rfl : fs=[rightHead++[.body,.fn]]++rightHead::[[.arg,.arg,.fn]])
  exact ⟨out,lb,rb,out.leftEdge,out.rightEdge,la,ra,
    by rw [lb];rfl,by rw [rb];rfl,by rw [la];rfl,by rw [ra];rfl,
    out.leftReader,out.rightReader,out.leftFalse,out.rightFalse,by rw [lb];simp,by rw [rb];simp,
    out.leftAfterNonempty,out.rightAfterNonempty,out.headIso,out.afterIso⟩

/-- Returned suffix chains/iso/safety feed the accepted safe-LAST supplier.
No desired head chain, old chain or endpoint iso is supplied to the cut top. -/
theorem actual_head_aux_from_returned_cuts : ∃out : SingleUnsafeCopyArgumentCuts event sourceClosed leftStart rightStart [.fn] [.arg] es fs,
    Nonempty (SafeLastCopyArgumentAuxOutput event sourceClosed [.fn] [.arg]
      (out.left.edge::out.left.after) (out.right.edge::out.right.after)) := by
  obtain ⟨out⟩:=actual_new_cuts
  obtain ⟨iso⟩:=out.headIso
  have aux:=safe_last_copy_argument_aux_inputs initial prefixHistory sourceClosed event selected
    (leftParent:=[.fn]) (rightParent:=[.arg]) (by rfl) (by rfl) leftLookup rightLookup
    out.leftHeadChain out.rightHeadChain iso out.leftAfterSafe out.rightAfterSafe leftLastSafe rightLastSafe
  exact ⟨out,aux⟩

#print axioms single_unsafe_copy_argument_cuts
#print axioms initial
#print axioms prefixHistory
#print axioms event
#print axioms leftChain
#print axioms rightChain
#print axioms actual_three_read_labels
#print axioms currentIso
#print axioms leftOtherSafe
#print axioms rightOtherSafe
#print axioms sourceSafe
#print axioms middleUnsafe
#print axioms leftLastSafe
#print axioms rightLastSafe
#print axioms actual_new_cuts
#print axioms actual_history_and_zero_jump
#print axioms actual_nonempty_before_after_cuts
#print axioms actual_head_aux_from_returned_cuts
end Lamping.Checks.SingleUnsafeCopyArgumentCutsChecks
