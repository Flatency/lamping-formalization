import Lamping.Lamping.SafeLastCopyArgumentAuxInputs
import Lamping.Checks.WrappedSuccessfulChains
namespace Lamping.Checks.SafeLastCopyArgumentAuxInputsChecks
open Graph Lambda Lambda.Labelled AG SyntaxIncidence
abbrev I : Term:=WrappedSuccessfulChains.I
abbrev bare : Term:=.app (.lam (.app (.var 0) (.var 0)))
  (.app (.lam (.app (.lam (.app (.var 0) (.var 0))) (.app I (.var 0)))) I)
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
abbrev newK : LTerm:=.lam ((Label.atom 15).concat ((Label.atom 6).under.concat (.atom 16))) (.var (.atom 17) 0)
abbrev leftStart : Path:=[.arg,.fn,.arg]
abbrev rightStart : Path:=[.arg,.arg,.arg]
abbrev es : List Path:=[leftStart,[.arg,.fn,.fn]]
abbrev fs : List Path:=[rightStart,[.arg,.arg,.fn]]
def leftChain : PrerequisiteChain target leftStart es:=
  .lam (parent:=[.arg,.fn]) (step:=.arg) rfl (by decide) (.redex_app (p:=[.arg,.fn]) rfl)
def rightChain : PrerequisiteChain target rightStart fs:=
  .lam (parent:=[.arg,.arg]) (step:=.arg) rfl (by decide) (.redex_app (p:=[.arg,.arg]) rfl)
theorem leftLookup : target.subterm leftStart=some newK:=rfl
theorem rightLookup : target.subterm rightStart=some newK:=rfl
theorem labelVectors : es.map target.labelAt=fs.map target.labelAt:=rfl
theorem currentIso : ChainIncidenceIsomorphic (chainSyntaxIncidence target targetClosed es) (chainSyntaxIncidence target targetClosed fs) :=
  actual_chain_iso_of_labels (prefixHistory.append event.final_history) initial targetClosed leftChain rightChain labelVectors

theorem leftAfterSafe : ∀e∈es.tail,∀node,target.subterm e=some node →node.label.OuterBarsSafe (fun x=>x≠Label.atom 6) := by
  intro e inside node lookup
  have same:e=[.arg,.fn,.fn]:=List.mem_singleton.mp inside
  subst e
  have nodeEq:node=.lam (.atom 13) (.var (.atom 14) 0):=Option.some.inj lookup.symm
  rw [nodeEq];trivial
theorem rightAfterSafe : ∀e∈fs.tail,∀node,target.subterm e=some node →node.label.OuterBarsSafe (fun x=>x≠Label.atom 6) := by
  intro e inside node lookup
  have same:e=[.arg,.arg,.fn]:=List.mem_singleton.mp inside
  subst e
  have nodeEq:node=.lam (.atom 13) (.var (.atom 14) 0):=Option.some.inj lookup.symm
  rw [nodeEq];trivial
theorem leftLastSafe : ∀node,middle.subterm ([.arg,.fn,.body]++([.fn]++[.arg]))=some node →node.label.OuterBarsSafe (fun x=>x≠Label.atom 6) := by
  intro node lookup
  have nodeEq:node=.var (.atom 15) 0:=Option.some.inj lookup.symm
  rw [nodeEq];trivial
theorem rightLastSafe : ∀node,middle.subterm ([.arg,.fn,.body]++([.arg]++[.arg]))=some node →node.label.OuterBarsSafe (fun x=>x≠Label.atom 6) := by
  intro node lookup
  have nodeEq:node=.var (.atom 15) 0:=Option.some.inj lookup.symm
  rw [nodeEq];trivial

theorem actual_new_inputs : Nonempty (SafeLastCopyArgumentAuxOutput event sourceClosed [.fn] [.arg] es fs) := by
  obtain ⟨iso⟩:=currentIso
  exact safe_last_copy_argument_aux_inputs initial prefixHistory sourceClosed event selected
    (by rfl) (by rfl) leftLookup rightLookup leftChain rightChain iso leftAfterSafe rightAfterSafe leftLastSafe rightLastSafe

private theorem right_context_trace (tail : Path) :
    BetaNodeHistoryPreimage event.labels (.arg::tail) (.arg::tail) := by
  exact .one (step:=StepAt.fn (.root _ _ _ _)) (by rfl)
    (.context (by rintro ⟨relative,equal⟩;cases equal)) (.nil _ _)

theorem sourceSafe : source.OuterBarsSafe (fun x=>x≠Label.atom 6) := by
  dsimp [source,first,original,bare,I,WrappedSuccessfulChains.I,WrappedSuccessfulChains.contractRoot,
    initLabels,initFrom,nodeCount,LTerm.contract,LTerm.subst,LTerm.single,LTerm.prepend,
    LTerm.rename,LTerm.lift,LTerm.label,Label.concat,Label.over,Label.under,Label.atom]
  simp only [LTerm.OuterBarsSafe,Label.OuterBarsSafe]
  decide

theorem middleUnsafe : ∃node,middle.subterm [.fn,.fn,.arg]=some node ∧
    ¬node.label.OuterBarsSafe (fun x=>x≠Label.atom 6) := by
  refine ⟨newK,rfl,?_⟩
  intro safe
  change (Label.atom 6≠Label.atom 6) ∧True at safe
  exact safe.1 rfl

def oldLeftChain : PrerequisiteChain source [.arg,.fn,.body,.fn] [[.arg,.fn,.body,.fn,.fn]]:=.redex_app rfl
def oldRightChain : PrerequisiteChain source [.arg,.fn,.body,.arg] [[.arg,.fn,.body,.arg,.fn]]:=.redex_app rfl

theorem actual_nonempty_prefix_context : INIT original ∧Closed original.erase ∧
    History [[.arg,.fn,.body],[],[.fn],[.arg]] original target ∧
    event.labels=preHistory ∧event.final_history=preHistory.append (.cons turn (.nil target)) ∧
    source.erase=.app (.app (.lam (.app (.app I (.var 0)) (.app I (.var 0)))) I)
      (.app (.lam (.app (.app I (.var 0)) (.app I (.var 0)))) I) ∧leftStart≠rightStart :=
  ⟨initial,originalClosed,prefixHistory.append event.final_history,rfl,rfl,rfl,by decide⟩

/-- This consumes the generalized top at a nonempty relative prefix. Exact
old coordinates and complete endpoint lists are locked by operational trace
and actual incidence uniqueness, never by repeated label equality. -/
theorem actual_full_auxiliary_inputs : ∃out : SafeLastCopyArgumentAuxOutput event sourceClosed [.fn] [.arg] es fs,
    out.leftLast.val=[.arg,.fn,.body,.fn,.arg] ∧out.rightLast.val=[.arg,.fn,.body,.arg,.arg] ∧
    out.leftLast.val≠out.rightLast.val ∧AuxiliaryAt source out.leftLast.val ∧AuxiliaryAt source out.rightLast.val ∧
    SyntaxIncidence.label source out.leftLast=SyntaxIncidence.label source out.rightLast ∧
    SyntaxIncidence.label source out.leftLast=.atom 15 ∧SyntaxIncidence.label source out.rightLast=.atom 15 ∧
    out.left.sourceEdges=[[.arg,.fn,.body,.fn,.fn]] ∧out.right.sourceEdges=[[.arg,.fn,.body,.arg,.fn]] ∧
    UncreatedNodeHistoryPreimage event.labels [.arg,.fn,.body,.fn,.arg] out.leftLast.val ∧
    UncreatedNodeHistoryPreimage event.labels [.arg,.fn,.body,.arg,.arg] out.rightLast.val ∧
    SuccessfulEndpointIso source sourceClosed (SyntaxIncidence.source source out.leftLast) (SyntaxIncidence.source source out.rightLast) ∧
    SuccessfulEndpointIso source sourceClosed (SyntaxIncidence.target source sourceClosed out.leftLast) (SyntaxIncidence.target source sourceClosed out.rightLast) := by
  obtain ⟨out⟩:=actual_new_inputs
  have lt : BetaNodeHistoryPreimage event.labels out.left.current.last.val [.arg,.fn,.body,.fn,.arg] := by
    rw [out.left.current.lastPath];exact right_context_trace _
  have rt : BetaNodeHistoryPreimage event.labels out.right.current.last.val [.arg,.fn,.body,.arg,.arg] := by
    rw [out.right.current.lastPath];exact right_context_trace _
  have lp:=out.left.trace.unique lt
  have rp:=out.right.trace.unique rt
  have ll : source.subterm out.leftLast.val=some (.var (.atom 15) 0) := by rw [lp];rfl
  have rl : source.subterm out.rightLast.val=some (.var (.atom 15) 0) := by rw [rp];rfl
  let leftParent : ProperPosition source:=⟨[.arg,.fn,.body,.fn],Or.inl ⟨_,_,_,rfl⟩⟩
  let rightParent : ProperPosition source:=⟨[.arg,.fn,.body,.arg],Or.inl ⟨_,_,_,rfl⟩⟩
  have ls : Source source out.leftLast.val (some leftParent) := by rw [lp];exact ⟨.arg,_,_,rfl,rfl,.arg⟩
  have rs : Source source out.rightLast.val (some rightParent) := by rw [rp];exact ⟨.arg,_,_,rfl,rfl,.arg⟩
  have lpar : out.left.sourceParent=leftParent:=Option.some.inj (out.left.sourceSpec.unique ls)
  have rpar : out.right.sourceParent=rightParent:=Option.some.inj (out.right.sourceSpec.unique rs)
  have lc : PrerequisiteChain source [.arg,.fn,.body,.fn] out.left.sourceEdges := by
    have c:=out.left.sourceChain;rw [lpar] at c;exact c
  have rc : PrerequisiteChain source [.arg,.fn,.body,.arg] out.right.sourceEdges := by
    have c:=out.right.sourceChain;rw [rpar] at c;exact c
  have lu : UncreatedNodeHistoryPreimage event.labels [.arg,.fn,.body,.fn,.arg] out.leftLast.val := by
    have c:=out.left.uncreated;rw [out.left.current.lastPath] at c;exact c
  have ru : UncreatedNodeHistoryPreimage event.labels [.arg,.fn,.body,.arg,.arg] out.rightLast.val := by
    have c:=out.right.uncreated;rw [out.right.current.lastPath] at c;exact c
  exact ⟨out,lp,rp,by rw [lp,rp];decide,out.leftAux,out.rightAux,out.sameLabel,
    SyntaxIncidence.label_of_lookup source out.leftLast ll,SyntaxIncidence.label_of_lookup source out.rightLast rl,
    lc.unique oldLeftChain,rc.unique oldRightChain,lu,ru,out.sourceIso,out.targetIso⟩

theorem actual_target_singletons : ∃out : SafeLastCopyArgumentAuxOutput event sourceClosed [.fn] [.arg] es fs,
    EndpointChain source (SyntaxIncidence.target source sourceClosed out.leftLast) [[.arg,.fn]] ∧
    EndpointChain source (SyntaxIncidence.target source sourceClosed out.rightLast) [[.arg,.fn]] := by
  obtain ⟨out⟩:=actual_new_inputs
  let selectedLambda : ProperPosition source:=⟨[.arg,.fn],Or.inr ⟨_,_,rfl⟩⟩
  have lt : BetaNodeHistoryPreimage event.labels out.left.current.selectedLambda.val selectedLambda.val := by
    rw [out.left.current.selectedPath];exact right_context_trace _
  have rt : BetaNodeHistoryPreimage event.labels out.right.current.selectedLambda.val selectedLambda.val := by
    rw [out.right.current.selectedPath];exact right_context_trace _
  have ls := out.left.targetPrefixTrace.unique (.proper lt)
  have rs := out.right.targetPrefixTrace.unique (.proper rt)
  have lp : out.left.selectedName++[.fn]=[.arg,.fn] :=
    out.left.selectedPath.symm.trans (congrArg Subtype.val (Option.some.inj ls))
  have rp : out.right.selectedName++[.fn]=[.arg,.fn] :=
    out.right.selectedPath.symm.trans (congrArg Subtype.val (Option.some.inj rs))
  have lc : EndpointChain source (SyntaxIncidence.target source sourceClosed out.leftLast) [[.arg,.fn]] := by
    rw [SyntaxIncidence.target_eq_of_spec source sourceClosed out.leftLast out.left.targetSpec]
    rw [←lp];exact out.left.targetChain
  have rc : EndpointChain source (SyntaxIncidence.target source sourceClosed out.rightLast) [[.arg,.fn]] := by
    rw [SyntaxIncidence.target_eq_of_spec source sourceClosed out.rightLast out.right.targetSpec]
    rw [←rp];exact out.right.targetChain
  exact ⟨out,lc,rc⟩

theorem actual_nonempty_relative_prefix : ([[.fn]] : List Path)≠[] := by decide

#print axioms safe_last_copy_argument_aux_inputs
#print axioms SafeLastCopyArgumentAuxOutput.leftAux
#print axioms SafeLastCopyArgumentAuxOutput.rightAux
#print axioms initial
#print axioms prefixHistory
#print axioms event
#print axioms leftChain
#print axioms rightChain
#print axioms currentIso
#print axioms leftAfterSafe
#print axioms rightAfterSafe
#print axioms leftLastSafe
#print axioms rightLastSafe
#print axioms sourceSafe
#print axioms middleUnsafe
#print axioms actual_new_inputs
#print axioms actual_nonempty_prefix_context
#print axioms actual_full_auxiliary_inputs
#print axioms actual_target_singletons
#print axioms actual_nonempty_relative_prefix
end Lamping.Checks.SafeLastCopyArgumentAuxInputsChecks
