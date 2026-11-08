import Lamping.Lamping.SingleUnsafeCopyFunctionAppInputs
import Lamping.Checks.WrappedSuccessfulChains
namespace Lamping.Checks.SingleUnsafeCopyFunctionAppInputsChecks
open Graph Lambda Lambda.Labelled AG SyntaxIncidence
abbrev I : Term:=WrappedSuccessfulChains.I
abbrev Delta : Term:=.lam (.app (.var 0) (.var 0))
abbrev bare : Term:=.app (.lam (.app (.var 0) (.var 0)))
  (.app (.lam (.app (.lam (.app (.var 0) (.var 0))) (.app (.var 0) I))) (.app Delta I))
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
abbrev copiedArgument : LTerm:=.app ((Label.atom 13).concat ((Label.atom 6).under.concat (.atom 16)))
  (.lam (.atom 17) (.app (.atom 18) (.var (.atom 19) 0) (.var (.atom 20) 0)))
  (.lam (.atom 21) (.var (.atom 22) 0))
abbrev leftHead : Path:=[.arg,.fn,.fn]
abbrev rightHead : Path:=[.arg,.arg,.fn]
abbrev leftStart : Path:=[.arg,.fn,.arg]
abbrev rightStart : Path:=[.arg,.arg,.arg]
abbrev es : List Path:=[leftStart,leftHead,leftHead++[.fn]]
abbrev fs : List Path:=[rightStart,rightHead,rightHead++[.fn]]
def leftRemaining : PrerequisiteChain target [.arg,.fn] [leftHead,leftHead++[.fn]]:=
  .app rfl (by intro l b wrong;cases wrong) (.redex_app (p:=leftHead) rfl)
def rightRemaining : PrerequisiteChain target [.arg,.arg] [rightHead,rightHead++[.fn]]:=
  .app rfl (by intro l b wrong;cases wrong) (.redex_app (p:=rightHead) rfl)
def leftChain : PrerequisiteChain target leftStart es:=
  .lam (parent:=[.arg,.fn]) (step:=.arg) rfl (by decide) leftRemaining
def rightChain : PrerequisiteChain target rightStart fs:=
  .lam (parent:=[.arg,.arg]) (step:=.arg) rfl (by decide) rightRemaining
theorem leftLookup : target.subterm leftHead=some copiedArgument:=rfl
theorem rightLookup : target.subterm rightHead=some copiedArgument:=rfl
theorem labelVectors : es.map target.labelAt=fs.map target.labelAt:=rfl
theorem actual_three_read_labels :
    es.map target.labelAt=[some (.atom 14),some copiedArgument.label,some (.atom 17)] ∧
    fs.map target.labelAt=[some (.atom 14),some copiedArgument.label,some (.atom 17)] := ⟨rfl,rfl⟩
theorem currentIso : ChainIncidenceIsomorphic (chainSyntaxIncidence target targetClosed es) (chainSyntaxIncidence target targetClosed fs) :=
  actual_chain_iso_of_labels (prefixHistory.append event.final_history) initial targetClosed leftChain rightChain labelVectors

theorem leftOtherSafe : ∀e∈es,e≠leftHead →degreeReadSafe (.atom 6) (target.labelAt e) := by
  intro e inside notHead
  rcases List.mem_cons.mp inside with rfl |inside
  · intro label same
    have eq : label=Label.atom 14:=Option.some.inj same.symm
    subst label;trivial
  · rcases List.mem_cons.mp inside with rfl |inside
    · exact False.elim (notHead rfl)
    · have eq:=List.mem_singleton.mp inside;subst e
      intro label same
      have eq : label=Label.atom 17:=Option.some.inj same.symm
      subst label;trivial
theorem rightOtherSafe : ∀e∈fs,e≠rightHead →degreeReadSafe (.atom 6) (target.labelAt e) := by
  intro e inside notHead
  rcases List.mem_cons.mp inside with rfl |inside
  · intro label same
    have eq : label=Label.atom 14:=Option.some.inj same.symm
    subst label;trivial
  · rcases List.mem_cons.mp inside with rfl |inside
    · exact False.elim (notHead rfl)
    · have eq:=List.mem_singleton.mp inside;subst e
      intro label same
      have eq : label=Label.atom 17:=Option.some.inj same.symm
      subst label;trivial

theorem sourceSafe : source.OuterBarsSafe (fun x=>x≠Label.atom 6) := by
  dsimp [source,first,original,bare,I,Delta,WrappedSuccessfulChains.I,WrappedSuccessfulChains.contractRoot,
    initLabels,initFrom,nodeCount,LTerm.contract,LTerm.subst,LTerm.single,LTerm.prepend,
    LTerm.rename,LTerm.lift,LTerm.label,Label.concat,Label.over,Label.under,Label.atom]
  simp only [LTerm.OuterBarsSafe,Label.OuterBarsSafe]
  decide

theorem leftFirstSafe : ∀node,middle.subterm ([.arg,.fn,.body]++([.fn]++[.fn]))=some node →node.label.OuterBarsSafe (fun x=>x≠Label.atom 6) := by
  intro node lookup
  have nodeEq:node=.var (.atom 13) 0:=Option.some.inj lookup.symm
  rw [nodeEq];trivial
theorem rightFirstSafe : ∀node,middle.subterm ([.arg,.fn,.body]++([.arg]++[.fn]))=some node →node.label.OuterBarsSafe (fun x=>x≠Label.atom 6) := by
  intro node lookup
  have nodeEq:node=.var (.atom 13) 0:=Option.some.inj lookup.symm
  rw [nodeEq];trivial

theorem actual_new_inputs : Nonempty (SingleUnsafeCopyFunctionAppInputs event sourceClosed leftStart rightStart [.fn] [.arg] es fs) := by
  obtain ⟨iso⟩:=currentIso
  exact single_unsafe_copy_function_app_inputs initial prefixHistory sourceClosed event selected sourceSafe
    (by rfl) (by rfl) leftLookup rightLookup leftChain rightChain iso (by simp [es]) (by simp [fs]) leftOtherSafe rightOtherSafe leftFirstSafe rightFirstSafe

theorem sourceNotInit : ¬INIT source := by
  intro init
  have rootLookup : source.subterm []=some source:=rfl
  obtain ⟨n,atomic⟩:=init.1 _ (LTerm.label_mem_of_subterm rootLookup)
  change ((Label.atom 0).concat ((Label.atom 1).over.concat (.atom 2)))=Label.atom n at atomic
  cases atomic

theorem middleUnsafe : ∃node,middle.subterm [.fn,.fn,.fn]=some node ∧
    ¬node.label.OuterBarsSafe (fun x=>x≠Label.atom 6) := by
  refine ⟨copiedArgument,rfl,?_⟩
  intro safe
  change (Label.atom 6≠Label.atom 6) ∧True at safe
  exact safe.1 rfl

theorem actual_nonempty_history_context : INIT original ∧Closed original.erase ∧
    History [[.arg,.fn,.body],[],[.fn],[.arg]] original target ∧
    ([[.fn]] : List Path)≠[] ∧leftStart≠rightStart ∧leftHead≠rightHead ∧
    target.subterm leftStart=some (.lam (.atom 14) (.var (.atom 15) 0)) ∧
    target.subterm rightStart=some (.lam (.atom 14) (.var (.atom 15) 0)) ∧
    target.subterm (leftHead++[.fn])=some (.lam (.atom 17) (.app (.atom 18) (.var (.atom 19) 0) (.var (.atom 20) 0))) ∧
    target.subterm (rightHead++[.fn])=some (.lam (.atom 17) (.app (.atom 18) (.var (.atom 19) 0) (.var (.atom 20) 0))) :=
  ⟨initial,originalClosed,prefixHistory.append event.final_history,by decide,by decide,by decide,rfl,rfl,rfl,rfl⟩

/-- Every final-leaf projection comes from the public supplier at two
actual different starts, nonempty BEFORE/AFTER and relative prefix. -/
theorem actual_final_safe_leaves : ∃out : SingleUnsafeCopyFunctionAppInputs event sourceClosed leftStart rightStart [.fn] [.arg] es fs,
    out.left.before=[leftStart] ∧out.right.before=[rightStart] ∧
    out.left.edge=leftHead ∧out.right.edge=rightHead ∧
    out.left.after=[leftHead++[.fn]] ∧out.right.after=[rightHead++[.fn]] ∧
    out.left.before.length=1 ∧out.right.before.length=1 ∧out.left.after.length=1 ∧out.right.after.length=1 ∧
    out.left.forward=true ∧out.right.forward=true ∧
    out.leftLeaf.pre=[[.fn]] ∧out.rightLeaf.pre=[[.fn]] ∧
    out.leftLeaf.site=[.arg] ∧out.rightLeaf.site=[.arg] ∧
    out.leftLeaf.after=[] ∧out.rightLeaf.after=[] ∧out.leftLeaf.continuation=[] ∧out.rightLeaf.continuation=[] ∧
    out.leftLeaf.reader=[.arg,.fn] ∧out.rightLeaf.reader=[.arg,.arg] ∧
    out.leftLeaf.current=copiedArgument ∧out.rightLeaf.current=copiedArgument ∧
    out.leftGeometry.creationFrames.length=1 ∧out.rightGeometry.creationFrames.length=1 := by
  obtain ⟨out⟩:=actual_new_inputs
  have ls:=out.left.split
  rw [out.leftEdge] at ls
  have rs:=out.right.split
  rw [out.rightEdge] at rs
  obtain ⟨lb,la⟩:=leftChain.first_created_split_unique ls (by rfl : es=[leftStart]++leftHead::[leftHead++[.fn]])
  obtain ⟨rb,ra⟩:=rightChain.first_created_split_unique rs (by rfl : fs=[rightStart]++rightHead::[rightHead++[.fn]])
  have leftCurrent : out.left.node=copiedArgument := by
    have actualLookup:=out.left.lookup
    rw [out.leftEdge] at actualLookup
    exact Option.some.inj (actualLookup.symm.trans leftLookup)
  have rightCurrent : out.right.node=copiedArgument := by
    have actualLookup:=out.right.lookup
    rw [out.rightEdge] at actualLookup
    exact Option.some.inj (actualLookup.symm.trans rightLookup)
  exact ⟨out,lb,rb,out.leftEdge,out.rightEdge,la,ra,
    by rw [lb];rfl,by rw [rb];rfl,by rw [la];rfl,by rw [ra];rfl,
    out.leftTrue,out.rightTrue,out.leftLeafPre,out.rightLeafPre,out.leftLeafSite,out.rightLeafSite,
    out.leftLeafAfter,out.rightLeafAfter,out.leftLeafContinuation,out.rightLeafContinuation,
    out.leftLeafReader,out.rightLeafReader,out.leftLeafCurrent.trans leftCurrent,out.rightLeafCurrent.trans rightCurrent,
    out.leftSingle,out.rightSingle⟩

/-- Existing complete TRUE-head evaluation is consumed, not re-proved.
Physical source matching and its lawful SOURCE REP remain honest conditions. -/
theorem actual_existing_true_evaluations
    {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} {root : B}
    (matching : Matches g root source.erase)
    (sourceSelection : OccurrenceFragmentSelection source g root)
    (representation : ChainRepresentationInvariant sourceClosed sourceSelection)
    (selection : SourceEdgeSelection (initLabels source.erase) g root) (edge : BetaEdge g) :
    ∃out : SingleUnsafeCopyFunctionAppInputs event sourceClosed leftStart rightStart [.fn] [.arg] es fs,
      ∃localTarget,History [[.fn],[.arg]] (initLabels source.erase) localTarget ∧
      ∃lp : PairedMarkerEventGeometry out.leftLeaf (initLabels source.erase) localTarget,
      ∃rp : PairedMarkerEventGeometry out.rightLeaf (initLabels source.erase) localTarget,
        selection.evalLabel edge lp.current.label=selection.evalLabel edge rp.current.label := by
  obtain ⟨out⟩:=actual_new_inputs
  obtain ⟨localTarget,labels,_erase⟩:=lift_history event.final_history.betaHistory (initLabels source.erase) (erase_initLabels source.erase)
  obtain ⟨lp⟩:=paired_marker_leaf_geometry out.leftLeaf labels (erase_initLabels source.erase).symm
  obtain ⟨rp⟩:=paired_marker_leaf_geometry out.rightLeaf labels (erase_initLabels source.erase).symm
  have sameNode : out.left.node.label=out.right.node.label := by
    simpa only [LTerm.labelAt,out.left.lookup,out.right.lookup,Option.map_some,Option.some.injEq] using out.sameHead
  have words:=congrArg (fun label : Label=>label.readLetters true) sameNode
  have evaluated:=paired_marker_same_event_forward_evaluations out.leftLeaf out.rightLeaf lp rp
    (out.leftLeafPre.trans out.rightLeafPre.symm) (out.leftLeafSite.trans out.rightLeafSite.symm)
    matching selected sourceSafe prefixHistory initial sourceClosed sourceSelection representation selection edge words
  exact ⟨out,localTarget,labels,lp,rp,evaluated⟩

#print axioms single_unsafe_copy_function_app_inputs
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
#print axioms sourceNotInit
#print axioms middleUnsafe
#print axioms leftFirstSafe
#print axioms rightFirstSafe
#print axioms actual_new_inputs
#print axioms actual_nonempty_history_context
#print axioms actual_final_safe_leaves
#print axioms actual_existing_true_evaluations
end Lamping.Checks.SingleUnsafeCopyFunctionAppInputsChecks
