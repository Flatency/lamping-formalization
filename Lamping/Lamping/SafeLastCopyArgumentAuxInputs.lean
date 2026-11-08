import Lamping.Lamping.FirstCopyArgumentAuxInputs
import Lamping.Lambda.SafeIncomingHistory
import Lamping.Lambda.AuxiliaryNodeHistoryOrigins
namespace Lamping.AG
open Graph Lambda Lambda.Labelled SyntaxIncidence
variable {source middle target t : LTerm}

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
structure MiddleCopyArgumentGeometry
    (event : SelectedOldTurn F source degree pre middle target site)
    (parent : Path) (stamp : Label) (inner : LTerm) (edges : List Path) where
  variableLabel : Label
  bodyLookup : event.body.subterm (parent++[.arg])=some (.var variableLabel (binderDepth (parent++[.arg])))
  last : Edge middle
  lastPath : last.val=(site++[.fn,.body])++(parent++[.arg])
  lastLookup : middle.subterm last.val=some (.var variableLabel (binderDepth (parent++[.arg])))
  auxiliary : AuxiliaryAt middle last.val
  formula : stamp.letters=variableLabel.letters++(.under degree)::event.argument.label.letters
  currentLookup : target.subterm (site++(parent++[.arg]))=some (.lam stamp inner)
  sourceParent : ProperPosition middle
  sourceParentPath : sourceParent.val=(site++[.fn,.body])++parent
  currentParent : ProperPosition target
  currentParentPath : currentParent.val=site++parent
  sourceSpec : Source middle last.val (some sourceParent)
  currentSource : Source target (site++(parent++[.arg])) (some currentParent)
  parentOrigin : BetaNodePreimage event.body event.argument site currentParent.val sourceParent.val
  parentTrace : BetaNodeHistoryPreimage (.cons event.turn (.nil target)) currentParent.val sourceParent.val
  split : edges=(site++(parent++[.arg]))::edges.tail
  afterChain : EndpointChain target (some currentParent) edges.tail
  afterNonempty : edges.tail≠[]
  selectedLambda : ProperPosition middle
  selectedPath : selectedLambda.val=site++[.fn]
  targetSpec : Target middle last.val (some selectedLambda)
  targetChain : EndpointChain middle (some selectedLambda) [site++[.fn]]

private theorem middle_copy_geometry
    (event : SelectedOldTurn F source degree pre middle target site)
    (occurs : ArgumentOccurrence event.body.erase (parent++[.arg]))
    (lookup : target.subterm (site++(parent++[.arg]))=some (.lam stamp inner))
    (chain : PrerequisiteChain target (site++(parent++[.arg])) edges) :
    Nonempty (MiddleCopyArgumentGeometry event parent stamp inner edges) := by
  have localLookup : (LTerm.contract event.beta degree event.body event.argument).subterm (parent++[.arg])=some (.lam stamp inner) := by
    rw [LTerm.subterm_append,event.turn.contract_lookup event.redex,Option.bind_some] at lookup
    exact lookup
  obtain ⟨variableLabel,bodyLookup,labelEq⟩:=LTerm.contract_argument_incoming_label occurs localLookup
  rw [if_neg (by simp)] at labelEq
  have formula : stamp.letters=variableLabel.letters++(.under degree)::event.argument.label.letters := by
    change (.lam stamp inner : LTerm).label.letters=_
    rw [labelEq]
    simp only [Label.letters_concat,Label.under,Label.letters,List.cons_append,List.nil_append]
  have lastLookup : middle.subterm ((site++[.fn,.body])++(parent++[.arg]))=
      some (.var variableLabel (binderDepth (parent++[.arg]))) := by
    rw [List.append_assoc,LTerm.subterm_append,event.redex]
    exact bodyLookup
  let last : Edge middle:=⟨(site++[.fn,.body])++(parent++[.arg]),by rw [←LTerm.erase_subterm,lastLookup];rfl⟩
  have lastSplit : last.val=((site++[.fn,.body])++parent)++[.arg] := by simp only [last,List.append_assoc]
  have auxiliary : AuxiliaryAt middle last.val := by
    constructor
    · rintro ⟨oldParent,a,fn,arg,split,atParent⟩
      have wrong:Step.arg=Step.fn:=(append_last_inj (lastSplit.symm.trans split)).2
      cases wrong
    · rintro ⟨a,b,atLambda⟩
      rw [lastLookup] at atLambda
      cases atLambda
  have splitLookup : middle.subterm (((site++[.fn,.body])++parent)++[.arg])=some (.var variableLabel (binderDepth (parent++[.arg]))) := by
    simpa only [List.append_assoc] using lastLookup
  obtain ⟨oldStamp,oldFn,oldArg,atOldParent⟩:=arg_parent splitLookup
  let oldParent : ProperPosition middle:=⟨(site++[.fn,.body])++parent,Or.inl ⟨oldStamp,oldFn,oldArg,atOldParent⟩⟩
  have sourceSpec : Source middle last.val (some oldParent):=⟨.arg,_,_,lastSplit,atOldParent,.arg⟩
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
  have parentTrace : BetaNodeHistoryPreimage (.cons event.turn (.nil target)) currentParent.val oldParent.val :=
    .one (step:=event.turn) event.redex origin (.nil _ _)
  obtain ⟨split,afterChain,afterNonempty⟩:=lambda_arg_tail copyLookup (copySplit ▸ chain)
  have actualSplit : edges=(site++(parent++[.arg]))::edges.tail := by rw [copySplit];exact split
  have lamAt : middle.subterm (site++[.fn])=some (.lam degree event.body) := by rw [LTerm.subterm_append,event.redex];rfl
  let selectedLambda : ProperPosition middle:=⟨site++[.fn],Or.inr ⟨degree,event.body,lamAt⟩⟩
  have toSelected : Target middle last.val (some selectedLambda) := by
    refine Or.inr ⟨variableLabel,_,degree,event.body,parent++[.arg],lastLookup,lamAt,?_,rfl⟩
    simp only [last,selectedLambda,List.append_assoc,List.cons_append,List.nil_append]
  exact ⟨⟨variableLabel,bodyLookup,last,rfl,lastLookup,auxiliary,formula,lookup,oldParent,rfl,currentParent,rfl,
    sourceSpec,currentSource,origin,parentTrace,actualSplit,afterChain,afterNonempty,selectedLambda,rfl,toSelected,
    PrerequisiteChain.redex_lam event.redex⟩⟩


private theorem node_append
    {ps qs : List Path} {a b c : LTerm}
    {firstHistory : History ps a b} {lastHistory : History qs b c}
    (first : BetaNodeHistoryPreimage firstHistory mid old)
    (last : BetaNodeHistoryPreimage lastHistory current mid) :
    BetaNodeHistoryPreimage (firstHistory.append lastHistory) current old := by
  induction first with
  | nil => exact last
  | @one _ _ _ _ _ _ _ _ _ _ _ _ step _ redex origin tail ih =>
    exact .one (step:=step) redex origin (ih last)

/-- This side keeps the actual middle variable separate from its own original
SOURCE occurrence. The endpoint traces concern actual incidences, not a
homomorphism of the created incoming lambda. -/
structure SafeLastCopyArgumentGeometry
    (event : SelectedOldTurn F source degree pre middle target site)
    (closed : Closed source.erase) (parent : Path) (stamp : Label) (inner : LTerm)
    (edges : List Path) where
  current : MiddleCopyArgumentGeometry event parent stamp inner edges
  last : Edge source
  originalLabel : Label
  originalIndex : Nat
  lookup : source.subterm last.val=some (.var originalLabel originalIndex)
  fullLabel : originalLabel=current.variableLabel
  trace : BetaNodeHistoryPreimage event.labels current.last.val last.val
  uncreated : UncreatedNodeHistoryPreimage event.labels current.last.val last.val
  auxiliary : AuxiliaryAt source last.val
  sourceParent : ProperPosition source
  sourceSpec : Source source last.val (some sourceParent)
  sourcePrefixTrace : BetaVertexHistoryPreimage event.labels (some current.sourceParent) (some sourceParent)
  parentTrace : BetaNodeHistoryPreimage event.final_history current.currentParent.val sourceParent.val
  selectedName : Path
  selectedMember : selectedName∈F
  selectedBeta : Label
  selectedBody : LTerm
  selectedArgument : LTerm
  selectedRedex : source.subterm selectedName=some (.app selectedBeta (.lam degree selectedBody) selectedArgument)
  selectedLambda : ProperPosition source
  selectedPath : selectedLambda.val=selectedName++[.fn]
  targetPrefixTrace : BetaVertexHistoryPreimage event.labels (some current.selectedLambda) (some selectedLambda)
  targetSpec : Target source last.val (some selectedLambda)
  targetChain : EndpointChain source (some selectedLambda) [selectedName++[.fn]]
  sourceEdges : List Path
  sourceChain : EndpointChain source (some sourceParent) sourceEdges
  slots : BetaEdgeHistoryPreimages event.final_history edges.tail sourceEdges
  labels : edges.tail.map target.labelAt=sourceEdges.map source.labelAt
  length : edges.tail.length=sourceEdges.length
  reflection : ChainIncidenceIsomorphic
    (chainSyntaxIncidence target (event.final_history.closed closed) edges.tail)
    (chainSyntaxIncidence source closed sourceEdges)

private theorem safe_last_geometry
    (event : SelectedOldTurn F source degree pre middle target site)
    (closed : Closed source.erase)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (geometry : MiddleCopyArgumentGeometry event parent stamp inner edges)
    (lastSafe : ∀node,middle.subterm ((site++[.fn,.body])++(parent++[.arg]))=some node →
      node.label.OuterBarsSafe (fun x=>x≠degree))
    (afterSafe : ∀e∈edges.tail,∀node,target.subterm e=some node →node.label.OuterBarsSafe (fun x=>x≠degree)) :
    ∃out : SafeLastCopyArgumentGeometry event closed parent stamp inner edges,out.current=geometry := by
  have midSafe : (LTerm.var geometry.variableLabel (binderDepth (parent++[.arg]))).label.OuterBarsSafe (fun x=>x≠degree) :=
    lastSafe _ (geometry.lastPath ▸ geometry.lastLookup)
  obtain ⟨oldPosition,oldNode,oldLookup,trace⟩:=event.labels.node_preimage_from_lookup geometry.lastLookup
  have uncreated:=event.beforeOld.safe_incoming_uncreated (DegreeAligned.initial source F) selected trace geometry.lastLookup midSafe
  obtain ⟨old,atOld,sameLabel⟩:=uncreated.source_label geometry.lastLookup
  obtain ⟨tagNode,tagLookup,_,tagEq⟩:=trace.lastAtom_constructor geometry.lastLookup
  have tagSame:=Option.some.inj (tagLookup.symm.trans atOld)
  rw [tagSame] at tagEq
  cases old with
  | app => cases tagEq
  | lam => cases tagEq
  | var oldLabel oldIndex =>
    let last : Edge source:=⟨oldPosition,by rw [←LTerm.erase_subterm,atOld];rfl⟩
    obtain ⟨_,_,aux⟩:=trace.auxiliary_source geometry.lastLookup geometry.auxiliary
    obtain ⟨sourceNode,oldSource,sourceLookup,sourceLabel,sourceSpec,sourceTrace⟩:=uncreated.source_history geometry.lastLookup geometry.sourceSpec
    cases sourceTrace with
    | @proper _ sourceParent sourceNodeTrace =>
      have parentTrace : BetaNodeHistoryPreimage event.final_history geometry.currentParent.val sourceParent.val :=
        node_append sourceNodeTrace geometry.parentTrace
      obtain ⟨oldTarget,targetSpec,targetTrace⟩:=trace.target_history geometry.targetSpec
      obtain ⟨name,chosen,originalRedex,_,fnTrace⟩:=event.beforeOld.selected_app_function_preimages event.labels event.member
      obtain ⟨beta,alpha,body,argument,redex⟩:=originalRedex
      have degreeEq:=selected name chosen
      simp only [LTerm.degreeAt,redex,Option.bind_some,LTerm.degree,Option.some.injEq] at degreeEq
      subst alpha
      have atFn : source.subterm (name++[.fn])=some (.lam degree body) := by rw [LTerm.subterm_append,redex];rfl
      let selectedLambda : ProperPosition source:=⟨name++[.fn],Or.inr ⟨degree,body,atFn⟩⟩
      have binderTrace : BetaNodeHistoryPreimage event.labels geometry.selectedLambda.val selectedLambda.val := by
        rw [geometry.selectedPath];exact fnTrace
      have targetEq:=targetTrace.unique (.proper binderTrace)
      rw [targetEq] at targetSpec
      obtain ⟨oldStart,oldEdges,oldChain,startTrace,edgeTraces,labels,length,iso⟩:=
        event.final_old.marker_free_chain_incidence_preimages closed (event.final_history.closed closed)
          (DegreeAligned.initial source F) event.final_history selected geometry.afterChain afterSafe
      have same:=startTrace.unique parentTrace
      subst oldStart
      exact ⟨⟨geometry,last,oldLabel,oldIndex,atOld,sameLabel,trace,uncreated,aux,
        sourceParent,sourceSpec,.proper sourceNodeTrace,parentTrace,name,chosen,beta,body,argument,redex,
        selectedLambda,rfl,.proper binderTrace,targetSpec,.redex_lam redex,oldEdges,oldChain,edgeTraces,labels,length,iso⟩,rfl⟩

/-- Full original SOURCE Aux inputs for a normal copied ARG lambda pair.
Only the two actual middle LAST incoming labels and the CURRENT AFTERs
are required safe; the relative OLD prefix may be nonempty and unsafe. -/
structure SafeLastCopyArgumentAuxOutput
    (event : SelectedOldTurn F source degree pre middle target site)
    (sourceClosed : Closed source.erase) (leftParent rightParent : Path)
    (es fs : List Path) where
  leftStamp : Label
  leftInner : LTerm
  rightStamp : Label
  rightInner : LTerm
  left : SafeLastCopyArgumentGeometry event sourceClosed leftParent leftStamp leftInner es
  right : SafeLastCopyArgumentGeometry event sourceClosed rightParent rightStamp rightInner fs
  fullCurrentLabels : es.map target.labelAt=fs.map target.labelAt
  afterLabels : es.tail.map target.labelAt=fs.tail.map target.labelAt
  middleLabelEq : left.current.variableLabel=right.current.variableLabel
  originalLabelEq : left.originalLabel=right.originalLabel
  sameLabel : SyntaxIncidence.label source left.last=SyntaxIncidence.label source right.last
  sourceIso : SuccessfulEndpointIso source sourceClosed
    (SyntaxIncidence.source source left.last) (SyntaxIncidence.source source right.last)
  targetIso : SuccessfulEndpointIso source sourceClosed
    (SyntaxIncidence.target source sourceClosed left.last) (SyntaxIncidence.target source sourceClosed right.last)

namespace SafeLastCopyArgumentAuxOutput
variable {event : SelectedOldTurn F source degree pre middle target site} {closed : Closed source.erase}
abbrev leftLast (out : SafeLastCopyArgumentAuxOutput event closed p q es fs) : Edge source := out.left.last
abbrev rightLast (out : SafeLastCopyArgumentAuxOutput event closed p q es fs) : Edge source := out.right.last
theorem leftAux (out : SafeLastCopyArgumentAuxOutput event closed p q es fs) : AuxiliaryAt source out.leftLast.val := out.left.auxiliary
theorem rightAux (out : SafeLastCopyArgumentAuxOutput event closed p q es fs) : AuxiliaryAt source out.rightLast.val := out.right.auxiliary
end SafeLastCopyArgumentAuxOutput

theorem safe_last_copy_argument_aux_inputs
    {original : LTerm} {prior : List Path}
    (initial : INIT original) (prefixHistory : History prior original source)
    (sourceClosed : Closed source.erase)
    (event : SelectedOldTurn F source degree pre middle target site)
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
    (rightSafe : ∀e∈fs.tail,∀node,target.subterm e=some node →node.label.OuterBarsSafe (fun x=>x≠degree))
    (leftLastSafe : ∀node,middle.subterm ((site++[.fn,.body])++(leftParent++[.arg]))=some node →node.label.OuterBarsSafe (fun x=>x≠degree))
    (rightLastSafe : ∀node,middle.subterm ((site++[.fn,.body])++(rightParent++[.arg]))=some node →node.label.OuterBarsSafe (fun x=>x≠degree)) :
    Nonempty (SafeLastCopyArgumentAuxOutput event sourceClosed leftParent rightParent es fs) := by
  obtain ⟨lm⟩:=middle_copy_geometry event leftOccurs leftLookup leftChain
  obtain ⟨rm⟩:=middle_copy_geometry event rightOccurs rightLookup rightChain
  obtain ⟨left,leftCurrent⟩:=safe_last_geometry event sourceClosed selected lm leftLastSafe leftSafe
  obtain ⟨right,rightCurrent⟩:=safe_last_geometry event sourceClosed selected rm rightLastSafe rightSafe
  have full:=actual_chain_labels_forward (prefixHistory.append event.final_history) initial
    (event.final_history.closed sourceClosed) leftChain rightChain iso
  have pieces : target.labelAt (site++(leftParent++[.arg]))=target.labelAt (site++(rightParent++[.arg])) ∧
      es.tail.map target.labelAt=fs.tail.map target.labelAt := by
    have split:=full
    rw [lm.split,rm.split,List.map_cons,List.map_cons] at split
    exact List.cons.inj split
  have leftLabel : target.labelAt (site++(leftParent++[.arg]))=some leftStamp := by simp only [LTerm.labelAt,leftLookup,Option.map_some,LTerm.label]
  have rightLabel : target.labelAt (site++(rightParent++[.arg]))=some rightStamp := by simp only [LTerm.labelAt,rightLookup,Option.map_some,LTerm.label]
  have labelEq:=Option.some.inj (leftLabel.symm.trans (pieces.1.trans rightLabel))
  have words:=congrArg Label.letters labelEq
  rw [lm.formula,rm.formula] at words
  have middleEq : lm.variableLabel=rm.variableLabel:=Label.letters_injective (List.append_cancel_right words)
  have middleCurrentEq : left.current.variableLabel=right.current.variableLabel := by
    rw [leftCurrent,rightCurrent];exact middleEq
  have originalEq : left.originalLabel=right.originalLabel:=left.fullLabel.trans (middleCurrentEq.trans right.fullLabel.symm)
  have sameLabel : SyntaxIncidence.label source left.last=SyntaxIncidence.label source right.last := by
    rw [SyntaxIncidence.label_of_lookup source left.last left.lookup,
      SyntaxIncidence.label_of_lookup source right.last right.lookup]
    exact originalEq
  have currentIso : ChainIncidenceIsomorphic
      (chainSyntaxIncidence target (event.final_history.closed sourceClosed) es.tail)
      (chainSyntaxIncidence target (event.final_history.closed sourceClosed) fs.tail) :=
    actual_chain_iso_of_labels (prefixHistory.append event.final_history) initial (event.final_history.closed sourceClosed)
      lm.afterChain rm.afterChain pieces.2
  have sourceIso : SuccessfulEndpointIso source sourceClosed
      (SyntaxIncidence.source source left.last) (SyntaxIncidence.source source right.last) := by
    rw [SyntaxIncidence.source_eq_of_spec source left.last left.sourceSpec,
      SyntaxIncidence.source_eq_of_spec source right.last right.sourceSpec]
    obtain ⟨li⟩:=left.reflection;obtain ⟨ri⟩:=right.reflection;obtain ⟨ci⟩:=currentIso
    exact ⟨left.sourceEdges,right.sourceEdges,left.sourceChain,right.sourceChain,⟨li.symm.trans (ci.trans ri)⟩⟩
  have targetIso : SuccessfulEndpointIso source sourceClosed
      (SyntaxIncidence.target source sourceClosed left.last) (SyntaxIncidence.target source sourceClosed right.last) := by
    rw [SyntaxIncidence.target_eq_of_spec source sourceClosed left.last left.targetSpec,
      SyntaxIncidence.target_eq_of_spec source sourceClosed right.last right.targetSpec]
    have sameMiddle : left.current.selectedLambda=right.current.selectedLambda:=Subtype.ext
      (left.current.selectedPath.trans right.current.selectedPath.symm)
    have rightTrace:=right.targetPrefixTrace
    rw [←sameMiddle] at rightTrace
    have same:=left.targetPrefixTrace.unique rightTrace
    rw [←same]
    exact SuccessfulEndpointIso.refl_of_chain left.targetChain
  exact ⟨⟨leftStamp,leftInner,rightStamp,rightInner,left,right,full,pieces.2,middleCurrentEq,originalEq,sameLabel,sourceIso,targetIso⟩⟩

end Lamping.AG
