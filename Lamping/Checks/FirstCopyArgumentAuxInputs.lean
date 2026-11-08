import Lamping.Lamping.FirstCopyArgumentAuxInputs
import Lamping.Checks.WrappedSuccessfulChains
namespace Lamping.Checks.FirstCopyArgumentAuxInputsChecks
open Graph Lambda Lambda.Labelled AG SyntaxIncidence
abbrev I : Term:=WrappedSuccessfulChains.I
abbrev bare : Term:=.app (.lam (.app (.lam (.app (.var 0) (.var 0))) (.app I (.var 0)))) I
abbrev original : LTerm:=initLabels bare
abbrev source : LTerm:=match original with
  | .app beta (.lam alpha body) arg=>.app beta (.lam alpha (WrappedSuccessfulChains.contractRoot body)) arg
  | other=>other
abbrev body : LTerm:=match source with | .app _ (.lam _ body) _=>body |other=>other
abbrev argument : LTerm:=match source with | .app _ _ arg=>arg |other=>other
abbrev target : LTerm:=WrappedSuccessfulChains.contractRoot source
abbrev F : List Path:=[[]]
abbrev newK : LTerm:=.lam ((Label.atom 10).concat ((Label.atom 1).under.concat (.atom 11))) (.var (.atom 12) 0)
abbrev leftStart : Path:=[.fn,.arg]
abbrev rightStart : Path:=[.arg,.arg]
abbrev es : List Path:=[leftStart,[.fn,.fn]]
abbrev fs : List Path:=[rightStart,[.arg,.fn]]
def prefixStep : StepAt [.fn,.body] original source:=.fn (.body (.root _ _ _ _))
def prefixHistory : History [[.fn,.body]] original source:=.cons prefixStep (.nil _)
def turn : StepAt [] source target:=.root _ _ _ _
def event : SelectedOldTurn F source (.atom 1) [] source target [] where
  markedBefore:=Marked.mark F source.erase
  markedAfter:=.app [] (.app [[.fn,.body,.fn]] (.lam (.var 0)) (.lam (.var 0)))
    (.app [[.fn,.body,.arg]] (.lam (.var 0)) (.lam (.var 0)))
  beforeOld:=.nil _
  reduction:=by
    change Marked.ReductionAt []
      (.red [[]] (.app [] (.app [[.fn,.body,.fn]] (.lam (.var 0)) (.var 0))
        (.app [[.fn,.body,.arg]] (.lam (.var 0)) (.var 0))) (.lam (.var 0)))
      (.app [] (.app [[.fn,.body,.fn]] (.lam (.var 0)) (.lam (.var 0)))
        (.app [[.fn,.body,.arg]] (.lam (.var 0)) (.lam (.var 0))))
    exact .redRoot _ _ _
  member:=by decide
  labels:=.nil _
  turn:=turn
  beta:=.atom 0
  body:=body
  argument:=argument
  redex:=rfl

theorem initial : INIT original:=init_is_INIT _
theorem originalClosed : Closed original.erase:=by simp [Closed,Scoped,original,initLabels,initFrom,nodeCount,LTerm.erase]
theorem sourceClosed : Closed source.erase:=prefixHistory.closed originalClosed
theorem targetClosed : Closed target.erase:=event.final_history.closed sourceClosed
theorem selected (name : Path) (member : name∈F) : source.degreeAt name=some (.atom 1) := by
  have same:=List.mem_singleton.mp member;subst name;rfl

def leftChain : PrerequisiteChain target leftStart es:=
  .lam (parent:=[.fn]) (step:=.arg) rfl (by decide) (.redex_app (p:=[.fn]) rfl)
def rightChain : PrerequisiteChain target rightStart fs:=
  .lam (parent:=[.arg]) (step:=.arg) rfl (by decide) (.redex_app (p:=[.arg]) rfl)
theorem leftLookup : target.subterm leftStart=some newK:=rfl
theorem rightLookup : target.subterm rightStart=some newK:=rfl
theorem labelVectors : es.map target.labelAt=fs.map target.labelAt:=rfl
theorem currentIso : ChainIncidenceIsomorphic (chainSyntaxIncidence target targetClosed es) (chainSyntaxIncidence target targetClosed fs) :=
  actual_chain_iso_of_labels (prefixHistory.append event.final_history) initial targetClosed leftChain rightChain labelVectors

theorem leftAfterSafe : ∀e∈es.tail,∀node,target.subterm e=some node →node.label.OuterBarsSafe (fun x=>x≠Label.atom 1) := by
  intro e inside node lookup
  have same:e=[.fn,.fn]:=List.mem_singleton.mp inside
  subst e
  have nodeEq:node=.lam (.atom 8) (.var (.atom 9) 0):=Option.some.inj lookup.symm
  rw [nodeEq];trivial

theorem rightAfterSafe : ∀e∈fs.tail,∀node,target.subterm e=some node →node.label.OuterBarsSafe (fun x=>x≠Label.atom 1) := by
  intro e inside node lookup
  have same:e=[.arg,.fn]:=List.mem_singleton.mp inside
  subst e
  have nodeEq:node=.lam (.atom 8) (.var (.atom 9) 0):=Option.some.inj lookup.symm
  rw [nodeEq];trivial

theorem actual_new_inputs : Nonempty (FirstCopyArgumentAuxOutput event sourceClosed [.fn] [.arg] es fs) := by
  obtain ⟨iso⟩:=currentIso
  exact first_copy_argument_aux_inputs initial prefixHistory sourceClosed event selected
    (by rfl) (by rfl) leftLookup rightLookup leftChain rightChain iso leftAfterSafe rightAfterSafe

theorem sourceNotInit : ¬INIT source := by
  intro init
  have bodyAt : source.subterm [.fn,.body]=some body:=rfl
  obtain ⟨n,atomic⟩:=init.1 _ (LTerm.label_mem_of_subterm bodyAt)
  change ((Label.atom 2).concat ((Label.atom 3).over.concat (.atom 4)))=Label.atom n at atomic
  cases atomic

theorem sourceSafe : source.OuterBarsSafe (fun x=>x≠Label.atom 1) := by
  dsimp [source,original,bare,I,WrappedSuccessfulChains.I,WrappedSuccessfulChains.contractRoot,
    initLabels,initFrom,nodeCount,LTerm.contract,LTerm.subst,LTerm.single,LTerm.prepend,
    LTerm.rename,LTerm.lift,LTerm.label,Label.concat,Label.over,Label.under,Label.atom]
  simp only [LTerm.OuterBarsSafe,Label.OuterBarsSafe]
  decide

theorem actual_two_event_context : INIT original ∧Closed original.erase ∧
    History [[.fn,.body],[]] original target ∧¬INIT source ∧
    source.erase=.app (.lam (.app (.app I (.var 0)) (.app I (.var 0)))) I ∧
    target.erase=.app (.app I I) (.app I I) ∧leftStart≠rightStart :=
  ⟨initial,originalClosed,prefixHistory.append event.final_history,sourceNotInit,rfl,rfl,by decide⟩

def oldLeftChain : PrerequisiteChain source [.fn,.body,.fn] [[.fn,.body,.fn,.fn]]:=.redex_app rfl
def oldRightChain : PrerequisiteChain source [.fn,.body,.arg] [[.fn,.body,.arg,.fn]]:=.redex_app rfl

/-- This actual new top supplies FULL old labels and all four successful
SOURCE endpoint chains/isos at two distinct real variable edges. -/
theorem actual_full_auxiliary_inputs : ∃out : FirstCopyArgumentAuxOutput event sourceClosed [.fn] [.arg] es fs,
    out.leftLast.val=[.fn,.body,.fn,.arg] ∧out.rightLast.val=[.fn,.body,.arg,.arg] ∧
    out.leftLast.val≠out.rightLast.val ∧AuxiliaryAt source out.leftLast.val ∧AuxiliaryAt source out.rightLast.val ∧
    SyntaxIncidence.label source out.leftLast=SyntaxIncidence.label source out.rightLast ∧
    SyntaxIncidence.label source out.leftLast=.atom 10 ∧SyntaxIncidence.label source out.rightLast=.atom 10 ∧
    out.leftSourceEdges=[[.fn,.body,.fn,.fn]] ∧out.rightSourceEdges=[[.fn,.body,.arg,.fn]] ∧
    EndpointChain source (SyntaxIncidence.target source sourceClosed out.leftLast) [[.fn]] ∧
    EndpointChain source (SyntaxIncidence.target source sourceClosed out.rightLast) [[.fn]] ∧
    SuccessfulEndpointIso source sourceClosed (SyntaxIncidence.source source out.leftLast) (SyntaxIncidence.source source out.rightLast) ∧
    SuccessfulEndpointIso source sourceClosed (SyntaxIncidence.target source sourceClosed out.leftLast) (SyntaxIncidence.target source sourceClosed out.rightLast) := by
  obtain ⟨out⟩:=actual_new_inputs
  have lp : out.leftLast.val=[.fn,.body,.fn,.arg]:=out.left.lastPath
  have rp : out.rightLast.val=[.fn,.body,.arg,.arg]:=out.right.lastPath
  have leftLookup : source.subterm out.leftLast.val=some (.var (.atom 10) 0) := by rw [lp];rfl
  have rightLookup : source.subterm out.rightLast.val=some (.var (.atom 10) 0) := by rw [rp];rfl
  have lc : PrerequisiteChain source [.fn,.body,.fn] out.leftSourceEdges :=
    Eq.mp (congrArg (fun p : Path=>PrerequisiteChain source p out.leftSourceEdges) out.left.sourceParentPath) out.leftSourceChain
  have rc : PrerequisiteChain source [.fn,.body,.arg] out.rightSourceEdges :=
    Eq.mp (congrArg (fun p : Path=>PrerequisiteChain source p out.rightSourceEdges) out.right.sourceParentPath) out.rightSourceChain
  have lt : EndpointChain source (SyntaxIncidence.target source sourceClosed out.leftLast) [[.fn]] := by
    rw [SyntaxIncidence.target_eq_of_spec source sourceClosed out.leftLast out.left.targetSpec]
    exact out.left.targetChain
  have rt : EndpointChain source (SyntaxIncidence.target source sourceClosed out.rightLast) [[.fn]] := by
    rw [SyntaxIncidence.target_eq_of_spec source sourceClosed out.rightLast out.right.targetSpec]
    exact out.right.targetChain
  exact ⟨out,lp,rp,by rw [lp,rp];decide,out.leftAux,out.rightAux,out.sameLabel,
    SyntaxIncidence.label_of_lookup source out.leftLast leftLookup,
    SyntaxIncidence.label_of_lookup source out.rightLast rightLookup,
    lc.unique oldLeftChain,rc.unique oldRightChain,lt,rt,out.sourceIso,out.targetIso⟩

#print axioms first_copy_argument_aux_inputs
#print axioms FirstCopyArgumentAuxOutput.leftAux
#print axioms FirstCopyArgumentAuxOutput.rightAux
#print axioms initial
#print axioms prefixHistory
#print axioms event
#print axioms leftChain
#print axioms rightChain
#print axioms currentIso
#print axioms leftAfterSafe
#print axioms rightAfterSafe
#print axioms actual_new_inputs
#print axioms sourceNotInit
#print axioms sourceSafe
#print axioms actual_two_event_context
#print axioms actual_full_auxiliary_inputs
end Lamping.Checks.FirstCopyArgumentAuxInputsChecks
