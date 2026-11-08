import Lamping.Lamping.ExpandedLastEndpointChains
import Lamping.Lamping.SafeReadSourceEndpointIso
import Lamping.Lamping.ActualChainForwardOrder
import Lamping.Lamping.ForwardFarChainComparison
namespace Lamping.AG
open Graph Lambda Lambda.Labelled SyntaxIncidence
variable {source target t : LTerm}

private theorem append_last_inj {p q : Path} {s t : Step} (same : p++[s]=q++[t]) : p=q ∧s=t := by
  have reverse:=congrArg List.reverse same
  simp only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append] at reverse
  have parts:=List.cons.inj reverse
  exact ⟨by simpa only [List.reverse_reverse] using congrArg List.reverse parts.2,parts.1⟩

private theorem arg_parent (lookup : t.subterm (p++[.arg])=some node) :
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

private theorem lambda_arg_tail
    (lookup : t.subterm (p++[.arg])=some (.lam stamp inner))
    (chain : PrerequisiteChain t (p++[.arg]) es) :
    es=(p++[.arg])::es.tail ∧PrerequisiteChain t p es.tail ∧es.tail≠[] := by
  rcases chain.lambda_cases lookup with ⟨parent,a,arg,fn,atApp,split⟩ |
    ⟨parent,child,tail,readerEq,notFn,listEq,actual⟩
  · have wrong:Step.arg=Step.fn:=(append_last_inj fn).2
    cases wrong
  · have parentEq:parent=p := (append_last_inj readerEq).1.symm
    subst parent
    rw [listEq]
    exact ⟨rfl,actual,actual.nonempty⟩

/-- Finite actual normal COPY-ARG geometry. There is no endpoint homomorphism
at the created lambda: its proper APP parent is genuinely retained. -/
structure NormalCopyArgumentGeometry
    (event : SelectedOldTurn F source degree [] source target site)
    (parent : Path) (stamp : Label) (inner : LTerm) (edges : List Path) where
  variableLabel : Label
  bodyLookup : event.body.subterm (parent++[.arg])=some (.var variableLabel (binderDepth (parent++[.arg])))
  last : Edge source
  lastPath : last.val=(site++[.fn,.body])++(parent++[.arg])
  lastLookup : source.subterm last.val=some (.var variableLabel (binderDepth (parent++[.arg])))
  auxiliary : AuxiliaryAt source last.val
  formula : stamp.letters=variableLabel.letters++(.under degree)::event.argument.label.letters
  currentLookup : target.subterm (site++(parent++[.arg]))=some (.lam stamp inner)
  sourceParent : ProperPosition source
  sourceParentPath : sourceParent.val=(site++[.fn,.body])++parent
  currentParent : ProperPosition target
  currentParentPath : currentParent.val=site++parent
  sourceSpec : Source source last.val (some sourceParent)
  currentSource : Source target (site++(parent++[.arg])) (some currentParent)
  parentOrigin : BetaNodePreimage event.body event.argument site currentParent.val sourceParent.val
  parentTrace : BetaNodeHistoryPreimage event.final_history currentParent.val sourceParent.val
  split : edges=(site++(parent++[.arg]))::edges.tail
  afterChain : EndpointChain target (some currentParent) edges.tail
  afterNonempty : edges.tail≠[]
  selectedLambda : ProperPosition source
  selectedPath : selectedLambda.val=site++[.fn]
  targetSpec : Target source last.val (some selectedLambda)
  targetChain : EndpointChain source (some selectedLambda) [site++[.fn]]

private theorem normal_copy_geometry
    (event : SelectedOldTurn F source degree [] source target site)
    (occurs : ArgumentOccurrence event.body.erase (parent++[.arg]))
    (lookup : target.subterm (site++(parent++[.arg]))=some (.lam stamp inner))
    (chain : PrerequisiteChain target (site++(parent++[.arg])) edges) :
    Nonempty (NormalCopyArgumentGeometry event parent stamp inner edges) := by
  have localLookup : (LTerm.contract event.beta degree event.body event.argument).subterm (parent++[.arg])=some (.lam stamp inner) := by
    rw [LTerm.subterm_append,event.turn.contract_lookup event.redex,Option.bind_some] at lookup
    exact lookup
  obtain ⟨variableLabel,bodyLookup,labelEq⟩:=LTerm.contract_argument_incoming_label occurs localLookup
  rw [if_neg (by simp)] at labelEq
  have formula : stamp.letters=variableLabel.letters++(.under degree)::event.argument.label.letters := by
    change (.lam stamp inner : LTerm).label.letters=_
    rw [labelEq]
    simp only [Label.letters_concat,Label.under,Label.letters,List.cons_append,List.nil_append]
  have lastLookup : source.subterm ((site++[.fn,.body])++(parent++[.arg]))=
      some (.var variableLabel (binderDepth (parent++[.arg]))) := by
    rw [List.append_assoc,LTerm.subterm_append,event.redex]
    exact bodyLookup
  let last : Edge source:=⟨(site++[.fn,.body])++(parent++[.arg]),by rw [←LTerm.erase_subterm,lastLookup];rfl⟩
  have lastSplit : last.val=((site++[.fn,.body])++parent)++[.arg] := by simp only [last,List.append_assoc]
  have auxiliary : AuxiliaryAt source last.val := by
    constructor
    · rintro ⟨oldParent,a,fn,arg,split,atParent⟩
      have wrong:Step.arg=Step.fn:=(append_last_inj (lastSplit.symm.trans split)).2
      cases wrong
    · rintro ⟨a,b,atLambda⟩
      rw [lastLookup] at atLambda
      cases atLambda
  have splitLookup : source.subterm (((site++[.fn,.body])++parent)++[.arg])=some (.var variableLabel (binderDepth (parent++[.arg]))) := by
    simpa only [List.append_assoc] using lastLookup
  obtain ⟨oldStamp,oldFn,oldArg,atOldParent⟩:=arg_parent splitLookup
  let oldParent : ProperPosition source:=⟨(site++[.fn,.body])++parent,Or.inl ⟨oldStamp,oldFn,oldArg,atOldParent⟩⟩
  have sourceSpec : Source source last.val (some oldParent):=⟨.arg,_,_,lastSplit,atOldParent,.arg⟩
  have copySplit : site++(parent++[.arg])=(site++parent)++[.arg] := (List.append_assoc _ _ _).symm
  have copyLookup : target.subterm ((site++parent)++[.arg])=some (.lam stamp inner):=copySplit ▸ lookup
  obtain ⟨curStamp,curFn,curArg,atCurrentParent⟩:=arg_parent copyLookup
  let currentParent : ProperPosition target:=⟨site++parent,Or.inl ⟨curStamp,curFn,curArg,atCurrentParent⟩⟩
  have currentSource : Source target (site++(parent++[.arg])) (some currentParent):=⟨.arg,_,_,copySplit,atCurrentParent,.arg⟩
  have atBody : event.body.subterm parent=some (.app oldStamp oldFn oldArg) := by
    rw [List.append_assoc,LTerm.subterm_append,event.redex] at atOldParent
    exact atOldParent
  have origin : BetaNodePreimage event.body event.argument site currentParent.val oldParent.val :=
    .retained atBody (by intro a impossible;cases impossible)
  have parentTrace : BetaNodeHistoryPreimage event.final_history currentParent.val oldParent.val :=
    .one (step:=event.turn) event.redex origin (.nil _ _)
  obtain ⟨split,afterChain,afterNonempty⟩:=lambda_arg_tail copyLookup (copySplit ▸ chain)
  have actualSplit : edges=(site++(parent++[.arg]))::edges.tail := by rw [copySplit];exact split
  have lamAt : source.subterm (site++[.fn])=some (.lam degree event.body) := by rw [LTerm.subterm_append,event.redex];rfl
  let selectedLambda : ProperPosition source:=⟨site++[.fn],Or.inr ⟨degree,event.body,lamAt⟩⟩
  have toSelected : Target source last.val (some selectedLambda) := by
    refine Or.inr ⟨variableLabel,_,degree,event.body,parent++[.arg],lastLookup,lamAt,?_,rfl⟩
    simp only [last,selectedLambda,List.append_assoc,List.cons_append,List.nil_append]
  exact ⟨⟨variableLabel,bodyLookup,last,rfl,lastLookup,auxiliary,formula,lookup,oldParent,rfl,currentParent,rfl,
    sourceSpec,currentSource,origin,parentTrace,actualSplit,afterChain,afterNonempty,selectedLambda,rfl,toSelected,
    PrerequisiteChain.redex_lam event.redex⟩⟩

private theorem reflect_after
    (event : SelectedOldTurn F source degree [] source target site)
    (closed : Closed source.erase)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (geometry : NormalCopyArgumentGeometry event parent stamp inner edges)
    (safe : ∀e∈edges.tail,∀node,target.subterm e=some node →node.label.OuterBarsSafe (fun x=>x≠degree)) :
    ∃oldEdges,EndpointChain source (some geometry.sourceParent) oldEdges ∧
      BetaEdgeHistoryPreimages event.final_history edges.tail oldEdges ∧
      edges.tail.map target.labelAt=oldEdges.map source.labelAt ∧edges.tail.length=oldEdges.length ∧
      ChainIncidenceIsomorphic
        (chainSyntaxIncidence target (event.final_history.closed closed) edges.tail)
        (chainSyntaxIncidence source closed oldEdges) := by
  obtain ⟨oldStart,oldEdges,oldChain,startTrace,edgeTraces,labels,length,iso⟩:=
    event.final_old.marker_free_chain_incidence_preimages closed (event.final_history.closed closed)
      (DegreeAligned.initial source F) event.final_history selected geometry.afterChain safe
  have same:=startTrace.unique geometry.parentTrace
  subst oldStart
  exact ⟨oldEdges,oldChain,edgeTraces,labels,length,iso⟩

/-- Actual SOURCE Aux inputs, constructed from a first relative COPY ARG pair.
Original INIT history is retained; no piece equality or Joint is a field. -/
structure FirstCopyArgumentAuxOutput
    (event : SelectedOldTurn F source degree [] source target site)
    (sourceClosed : Closed source.erase) (leftParent rightParent : Path)
    (es fs : List Path) where
  leftStamp : Label
  leftInner : LTerm
  rightStamp : Label
  rightInner : LTerm
  left : NormalCopyArgumentGeometry event leftParent leftStamp leftInner es
  right : NormalCopyArgumentGeometry event rightParent rightStamp rightInner fs
  fullCurrentLabels : es.map target.labelAt=fs.map target.labelAt
  afterLabels : es.tail.map target.labelAt=fs.tail.map target.labelAt
  sameVariableLabel : left.variableLabel=right.variableLabel
  sameLabel : SyntaxIncidence.label source left.last=SyntaxIncidence.label source right.last
  leftSourceEdges : List Path
  rightSourceEdges : List Path
  leftSourceChain : EndpointChain source (some left.sourceParent) leftSourceEdges
  rightSourceChain : EndpointChain source (some right.sourceParent) rightSourceEdges
  leftSlots : BetaEdgeHistoryPreimages event.final_history es.tail leftSourceEdges
  rightSlots : BetaEdgeHistoryPreimages event.final_history fs.tail rightSourceEdges
  leftSourceLabels : es.tail.map target.labelAt=leftSourceEdges.map source.labelAt
  rightSourceLabels : fs.tail.map target.labelAt=rightSourceEdges.map source.labelAt
  leftLength : es.tail.length=leftSourceEdges.length
  rightLength : fs.tail.length=rightSourceEdges.length
  leftReflection : ChainIncidenceIsomorphic
    (chainSyntaxIncidence target (event.final_history.closed sourceClosed) es.tail)
    (chainSyntaxIncidence source sourceClosed leftSourceEdges)
  rightReflection : ChainIncidenceIsomorphic
    (chainSyntaxIncidence target (event.final_history.closed sourceClosed) fs.tail)
    (chainSyntaxIncidence source sourceClosed rightSourceEdges)
  sourceIso : SuccessfulEndpointIso source sourceClosed
    (SyntaxIncidence.source source left.last) (SyntaxIncidence.source source right.last)
  targetIso : SuccessfulEndpointIso source sourceClosed
    (SyntaxIncidence.target source sourceClosed left.last) (SyntaxIncidence.target source sourceClosed right.last)

namespace FirstCopyArgumentAuxOutput
variable {event : SelectedOldTurn F source degree [] source target site} {closed : Closed source.erase}
abbrev leftLast (out : FirstCopyArgumentAuxOutput event closed p q es fs) : Edge source := out.left.last
abbrev rightLast (out : FirstCopyArgumentAuxOutput event closed p q es fs) : Edge source := out.right.last
theorem leftAux (out : FirstCopyArgumentAuxOutput event closed p q es fs) : AuxiliaryAt source out.leftLast.val := out.left.auxiliary
theorem rightAux (out : FirstCopyArgumentAuxOutput event closed p q es fs) : AuxiliaryAt source out.rightLast.val := out.right.auxiliary
end FirstCopyArgumentAuxOutput

/-- SAME original INIT/history and actual complete chains supply the head and
AFTER comparisons. Only normal nonempty COPY APP-ARG is claimed. -/
theorem first_copy_argument_aux_inputs
    {original : LTerm} {prior : List Path}
    (initial : INIT original) (prefixHistory : History prior original source)
    (sourceClosed : Closed source.erase)
    (event : SelectedOldTurn F source degree [] source target site)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (leftOccurs : ArgumentOccurrence event.body.erase (leftParent++[.arg]))
    (rightOccurs : ArgumentOccurrence event.body.erase (rightParent++[.arg]))
    (leftLookup : target.subterm (site++(leftParent++[.arg]))=some (.lam leftStamp leftInner))
    (rightLookup : target.subterm (site++(rightParent++[.arg]))=some (.lam rightStamp rightInner))
    (leftChain : PrerequisiteChain target (site++(leftParent++[.arg])) es)
    (rightChain : PrerequisiteChain target (site++(rightParent++[.arg])) fs)
    (iso : ChainIncidenceIso (chainSyntaxIncidence target (event.final_history.closed sourceClosed) es)
      (chainSyntaxIncidence target (event.final_history.closed sourceClosed) fs))
    (leftSafe : ∀e∈es.tail,∀node,target.subterm e=some node →node.label.OuterBarsSafe (fun x=>x≠degree))
    (rightSafe : ∀e∈fs.tail,∀node,target.subterm e=some node →node.label.OuterBarsSafe (fun x=>x≠degree)) :
    Nonempty (FirstCopyArgumentAuxOutput event sourceClosed leftParent rightParent es fs) := by
  obtain ⟨left⟩:=normal_copy_geometry event leftOccurs leftLookup leftChain
  obtain ⟨right⟩:=normal_copy_geometry event rightOccurs rightLookup rightChain
  have full:=actual_chain_labels_forward (prefixHistory.append event.final_history) initial
    (event.final_history.closed sourceClosed) leftChain rightChain iso
  have pieces : target.labelAt (site++(leftParent++[.arg]))=target.labelAt (site++(rightParent++[.arg])) ∧
      es.tail.map target.labelAt=fs.tail.map target.labelAt := by
    have split:=full
    rw [left.split,right.split,List.map_cons,List.map_cons] at split
    exact List.cons.inj split
  have leftLabel : target.labelAt (site++(leftParent++[.arg]))=some leftStamp := by simp only [LTerm.labelAt,leftLookup,Option.map_some,LTerm.label]
  have rightLabel : target.labelAt (site++(rightParent++[.arg]))=some rightStamp := by simp only [LTerm.labelAt,rightLookup,Option.map_some,LTerm.label]
  have labelEq:=Option.some.inj (leftLabel.symm.trans (pieces.1.trans rightLabel))
  have words:=congrArg Label.letters labelEq
  rw [left.formula,right.formula] at words
  have variableEq : left.variableLabel=right.variableLabel:=Label.letters_injective (List.append_cancel_right words)
  have sameLabel : SyntaxIncidence.label source left.last=SyntaxIncidence.label source right.last := by
    rw [SyntaxIncidence.label_of_lookup source left.last left.lastLookup,
      SyntaxIncidence.label_of_lookup source right.last right.lastLookup]
    exact variableEq
  have currentIso : ChainIncidenceIsomorphic
      (chainSyntaxIncidence target (event.final_history.closed sourceClosed) es.tail)
      (chainSyntaxIncidence target (event.final_history.closed sourceClosed) fs.tail) :=
    actual_chain_iso_of_labels (prefixHistory.append event.final_history) initial (event.final_history.closed sourceClosed)
      left.afterChain right.afterChain pieces.2
  obtain ⟨les,lc,lt,ll,len,li⟩:=reflect_after event sourceClosed selected left leftSafe
  obtain ⟨res,rc,rt,rl,ren,ri⟩:=reflect_after event sourceClosed selected right rightSafe
  have sourceIso : SuccessfulEndpointIso source sourceClosed
      (SyntaxIncidence.source source left.last) (SyntaxIncidence.source source right.last) := by
    rw [SyntaxIncidence.source_eq_of_spec source left.last left.sourceSpec,
      SyntaxIncidence.source_eq_of_spec source right.last right.sourceSpec]
    obtain ⟨li⟩:=li;obtain ⟨ri⟩:=ri;obtain ⟨currentIso⟩:=currentIso
    exact ⟨les,res,lc,rc,⟨li.symm.trans (currentIso.trans ri)⟩⟩
  have targetIso : SuccessfulEndpointIso source sourceClosed
      (SyntaxIncidence.target source sourceClosed left.last) (SyntaxIncidence.target source sourceClosed right.last) := by
    rw [SyntaxIncidence.target_eq_of_spec source sourceClosed left.last left.targetSpec,
      SyntaxIncidence.target_eq_of_spec source sourceClosed right.last right.targetSpec]
    have same : left.selectedLambda=right.selectedLambda:=Subtype.ext (left.selectedPath.trans right.selectedPath.symm)
    rw [←same]
    exact SuccessfulEndpointIso.refl_of_chain left.targetChain
  exact ⟨⟨leftStamp,leftInner,rightStamp,rightInner,left,right,full,pieces.2,variableEq,sameLabel,
    les,res,lc,rc,lt,rt,ll,rl,len,ren,li,ri,sourceIso,targetIso⟩⟩

end Lamping.AG
