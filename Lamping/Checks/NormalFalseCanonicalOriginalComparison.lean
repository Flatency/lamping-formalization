import Lamping.Lamping.NormalFalseCanonicalOriginalComparison
import Lamping.Checks.FalseCopyFirstSafeLabels
namespace Lamping.Checks.NormalFalseCanonicalOriginalComparisonChecks
open Graph Lambda Lambda.Labelled AG SyntaxIncidence
open SafeLastCopyArgumentAuxInputsChecks
open FalseCopyFirstSafeLabelsChecks

private theorem empty_coordinates {source target : LTerm} {ps : List Path}
    {labels : History ps source target}
    (trace : BetaNodeHistoryPreimage labels p old) (empty : ps=[]) : p=old := by
  subst ps
  cases trace
  rfl

private theorem one_context_coordinates {source target : LTerm} {ps : List Path}
    {labels : History ps source target}
    (trace : BetaNodeHistoryPreimage labels p old) (single : ps=[site])
    (outside : ¬∃relative,p=site++relative) : p=old := by
  subst ps
  cases trace with
  | one redex origin tail =>
    cases tail
    exact (origin.unique (.context outside)).symm

private theorem one_uncreated {source target body argument : LTerm} {ps : List Path}
    {labels : History ps source target}
    (trace : UncreatedNodeHistoryPreimage labels p old) (single : ps=[site])
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument)) :
    ¬BetaCreatedIncoming body site p := by
  subst ps
  cases trace with
  | one actual origin uncreated tail =>
    cases tail
    have same:=Option.some.inj (actual.symm.trans redex)
    cases same
    exact uncreated


private theorem false_copy_shape
    {body argument t : LTerm} {site edge reader oldReader first last : Path}
    (origin : BetaIncomingReadingOrigin body argument site edge reader oldReader first last)
    (reading : PrerequisiteReadsDirected t reader edge false) (notresult : edge≠site) :
    ∃q,edge=site++q ∧first=site++[.arg] ∧last=(site++[.fn,.body])++q := by
  cases origin with
  | resultFunction result function =>
    have size:=congrArg List.length (reading.2.symm.trans (result.trans function));simp at size
  | resultLambda result _ _ => exact False.elim (notresult result)
  | copyFunction occurs copy read =>
    have size:=congrArg List.length reading.2
    simp only [copy,read,List.length_append,List.length_singleton] at size
    omega
  | copyLambda occurs copy _ _ => exact ⟨_,copy,rfl,rfl⟩


/-- Direct natural high on the two already-returned GIVEN geometries and
recents. Neither geometry is re-created to fit the comparison. -/
theorem actual_given_cross_prefix_aux :
    ∃el esnap,
    ∃eg : SpineIncidenceProvenance F source (.atom 6) false earlyCut.spine earlyCut.lookup el esnap,
    ∃er : RecentSpineFrame eg,
    ∃ll lsnap,
    ∃lg : SpineIncidenceProvenance F source (.atom 6) false lateCut.spine lateCut.lookup ll lsnap,
    ∃lr : RecentSpineFrame lg,
    ∃left : CanonicalAfterFarOutput event.final_history earlyCut esnap,
    ∃right : CanonicalAfterFarOutput event.final_history lateCut lsnap,
    ∃comparison : GivenNormalFalseOriginalComparison er lr sourceClosed left right,
      er.packet.pre=[] ∧er.packet.site=[.fn] ∧er.suffixSites=[[.arg]] ∧
      lr.packet.pre=[[.fn]] ∧lr.packet.site=[.arg] ∧lr.suffixSites=[] ∧
      comparison.leftOriginal.oldEdge=[.fn,.fn,.body,.fn,.arg] ∧
      comparison.rightOriginal.oldEdge=[.arg,.fn,.body,.fn,.arg] ∧
      comparison.leftOriginal.oldEdge≠comparison.rightOriginal.oldEdge ∧
      comparison.leftOriginal.original.label=.atom 15 ∧
      comparison.rightOriginal.original.label=.atom 15 ∧
      comparison.leftOriginal.sourceEdges=[[.fn,.fn,.body,.fn,.fn]] ∧
      comparison.rightOriginal.sourceEdges=[[.arg,.fn,.body,.fn,.fn]] ∧
      comparison.leftOriginal.targetEdges=[[.fn,.fn]] ∧
      comparison.rightOriginal.targetEdges=[[.arg,.fn]] := by
  obtain ⟨el,esnap,eg,ec,er,ex,elow,eo,ll,lsnap,lg,lc,lr,lx,llow,lo,
    ep,et,ef,lp,lt,lf,eOld,lOld,_distinct,_labels⟩:=actual_different_prefix_false_labels
  have eh : earlyCut.edge=er.packet.edge:=one_context_coordinates er.uncreatedSuffix.to_node ef
    (by rintro ⟨relative,equal⟩;cases equal)
  have lh : lateCut.edge=lr.packet.edge:=empty_coordinates lr.uncreatedSuffix.to_node lf
  have em : er.packet.middle=SafeLastCopyArgumentAuxInputsChecks.source := by
    have history:=er.packet.event.labels
    rw [ep] at history
    exact history.deterministic (.nil _)
  have lm : lr.packet.middle=middle := by
    have history:=lr.packet.event.labels
    rw [lp] at history
    exact history.deterministic preHistory
  obtain ⟨eq,eqHead,eqFirst,eqLast⟩:=false_copy_shape er.packet.origin er.packet.reading (by rw [←eh,et];decide)
  obtain ⟨lq,lqHead,lqFirst,lqLast⟩:=false_copy_shape lr.packet.origin lr.packet.reading (by rw [←lh,lt];decide)
  have eqPath : eq=[.fn,.arg] := by
    have actual:=eqHead
    rw [←eh,et] at actual
    exact List.cons.inj actual |>.2 |>.symm
  have lqPath : lq=[.fn,.arg] := by
    have actual:=lqHead
    rw [←lh,lt] at actual
    exact List.cons.inj actual |>.2 |>.symm
  have enormal : er.packet.last=(er.packet.site++[.fn,.body])++[.fn,.arg] := by rw [eqLast,eqPath]
  have lnormal : lr.packet.last=(lr.packet.site++[.fn,.body])++[.fn,.arg] := by rw [lqLast,lqPath]
  have eSafe : ∀node,er.packet.middle.subterm er.packet.first=some node →node.label.OuterBarsSafe (fun x=>x≠Label.atom 6) := by
    intro node lookup
    rw [em,eqFirst,et] at lookup
    have same : node=.lam (.atom 16) (.var (.atom 17) 0):=Option.some.inj lookup.symm
    rw [same];trivial
  have lSafe : ∀node,lr.packet.middle.subterm lr.packet.first=some node →node.label.OuterBarsSafe (fun x=>x≠Label.atom 6) := by
    intro node lookup
    rw [lm,lqFirst,lt] at lookup
    have same : node=.lam (.atom 16) (.var (.atom 17) 0):=Option.some.inj lookup.symm
    rw [same];trivial
  have whole : ChainIncidenceIsomorphic
      (chainSyntaxIncidence target targetClosed earlyEdges) (chainSyntaxIncidence target targetClosed es) :=
    actual_chain_iso_of_labels (prefixHistory.append event.final_history) initial targetClosed earlyChain leftChain (by rfl)
  obtain ⟨iso⟩:=whole
  obtain ⟨left,right,⟨comparison⟩⟩:=actual_given_normal_false_original_comparison
    (leftCut:=earlyCut) (rightCut:=lateCut) (labels:=event.final_history) er lr initial prefixHistory
    sourceClosed event.final_old selected sourceSafe iso (by decide)
    ⟨[.fn,.arg],by decide,enormal⟩ ⟨[.fn,.arg],by decide,lnormal⟩ eSafe lSafe
  have eTrace:=comparison.leftOriginal.nodeTrace.unique eo.nodeTrace
  have lTrace:=comparison.rightOriginal.nodeTrace.unique lo.nodeTrace
  have ePosition : comparison.leftOriginal.oldEdge=[.fn,.fn,.body,.fn,.arg]:=eTrace.trans eOld
  have lPosition : comparison.rightOriginal.oldEdge=[.arg,.fn,.body,.fn,.arg]:=lTrace.trans lOld
  have eNode : comparison.leftOriginal.original=.var (.atom 15) 0 :=
    Option.some.inj (comparison.leftOriginal.lookup.symm.trans (show source.subterm comparison.leftOriginal.oldEdge=some (.var (.atom 15) 0) from by rw [ePosition];rfl))
  have lNode : comparison.rightOriginal.original=.var (.atom 15) 0 :=
    Option.some.inj (comparison.rightOriginal.lookup.symm.trans (show source.subterm comparison.rightOriginal.oldEdge=some (.var (.atom 15) 0) from by rw [lPosition];rfl))
  let eParent : ProperPosition source:=⟨[.fn,.fn,.body,.fn],Or.inl ⟨_,_,_,rfl⟩⟩
  let rp : ProperPosition source:=⟨[.arg,.fn,.body,.fn],Or.inl ⟨_,_,_,rfl⟩⟩
  have eSource : Source source comparison.leftOriginal.oldEdge (some eParent) := by
    rw [ePosition];exact ⟨.arg,_,_,rfl,rfl,.arg⟩
  have rSource : Source source comparison.rightOriginal.oldEdge (some rp) := by
    rw [lPosition];exact ⟨.arg,_,_,rfl,rfl,.arg⟩
  have efp : comparison.leftOriginal.fromVertex=eParent:=Option.some.inj (comparison.leftOriginal.sourceSpec.unique eSource)
  have rfp : comparison.rightOriginal.fromVertex=rp:=Option.some.inj (comparison.rightOriginal.sourceSpec.unique rSource)
  have eChain : PrerequisiteChain source [.fn,.fn,.body,.fn] comparison.leftOriginal.sourceEdges := by
    have actual:=comparison.leftOriginal.sourceChain
    rw [efp] at actual;exact actual
  have rChain : PrerequisiteChain source [.arg,.fn,.body,.fn] comparison.rightOriginal.sourceEdges := by
    have actual:=comparison.rightOriginal.sourceChain
    rw [rfp] at actual;exact actual
  let eb : ProperPosition source:=⟨[.fn,.fn],Or.inr ⟨.atom 6,body,rfl⟩⟩
  let rb : ProperPosition source:=⟨[.arg,.fn],Or.inr ⟨.atom 6,body,rfl⟩⟩
  have eTarget : Target source comparison.leftOriginal.oldEdge (some eb) := by
    rw [ePosition]
    exact Or.inr ⟨.atom 15,0,.atom 6,body,[.fn,.arg],rfl,rfl,rfl,rfl⟩
  have rTarget : Target source comparison.rightOriginal.oldEdge (some rb) := by
    rw [lPosition]
    exact Or.inr ⟨.atom 15,0,.atom 6,body,[.fn,.arg],rfl,rfl,rfl,rfl⟩
  have ebp : comparison.leftOriginal.toVertex=eb:=Option.some.inj (comparison.leftOriginal.targetSpec.unique eTarget)
  have rbp : comparison.rightOriginal.toVertex=rb:=Option.some.inj (comparison.rightOriginal.targetSpec.unique rTarget)
  have ebChain : PrerequisiteChain source [.fn,.fn] comparison.leftOriginal.targetEdges := by
    have actual:=comparison.leftOriginal.targetChain
    rw [ebp] at actual;exact actual
  have rbChain : PrerequisiteChain source [.arg,.fn] comparison.rightOriginal.targetEdges := by
    have actual:=comparison.rightOriginal.targetChain
    rw [rbp] at actual;exact actual
  refine ⟨el,esnap,eg,er,ll,lsnap,lg,lr,left,right,comparison,?_,et,ef,lp,lt,lf,ePosition,lPosition,
    by rw [ePosition,lPosition];decide,?_,?_,?_,?_,?_,?_⟩
  · exact ep
  · rw [eNode];rfl
  · rw [lNode];rfl
  · exact eChain.unique (.redex_app (p:=[.fn,.fn,.body,.fn]) rfl)
  · exact rChain.unique (.redex_app (p:=[.arg,.fn,.body,.fn]) rfl)
  · exact ebChain.unique (.redex_lam (p:=[.fn]) rfl)
  · exact rbChain.unique (.redex_lam (p:=[.arg]) rfl)


/-- The graph hypothesis is a legitimate SOURCE Aux invariant. No fixture
claims that invariant unconditionally, and only SOURCE literal pieces follow. -/
theorem actual_source_aux_literal_pieces
    {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} {root : B}
    (selection : OccurrenceFragmentSelection source g root)
    (auxiliary : AuxiliarySeparation sourceClosed selection) :
    ∃left right : Edge source,
      left.val=[.fn,.fn,.body,.fn,.arg] ∧right.val=[.arg,.fn,.body,.fn,.arg] ∧left≠right ∧
      AuxiliaryAt source left.val ∧AuxiliaryAt source right.val ∧
      SyntaxIncidence.label source left=SyntaxIncidence.label source right ∧
      SuccessfulEndpointIso source sourceClosed (SyntaxIncidence.source source left) (SyntaxIncidence.source source right) ∧
      SuccessfulEndpointIso source sourceClosed (SyntaxIncidence.target source sourceClosed left) (SyntaxIncidence.target source sourceClosed right) ∧
      (selection left).fragment.segments=(selection right).fragment.segments := by
  obtain ⟨el,esnap,eg,er,ll,lsnap,lg,lr,l,r,comparison,
    _ep,_et,_ef,_lp,_lt,_lf,ePos,lPos,distinct,_labels⟩:=actual_given_cross_prefix_aux
  let left : Edge source:=(GivenNormalFalseOriginalComparison.leftOutput (left:=l) (right:=r) er lr comparison).originalEdge
  let right : Edge source:=(GivenNormalFalseOriginalComparison.rightOutput (left:=l) (right:=r) er lr comparison).originalEdge
  have same : SyntaxIncidence.label source left=SyntaxIncidence.label source right := by
    rw [SyntaxIncidence.label_of_lookup source _ comparison.leftOriginal.lookup,
      SyntaxIncidence.label_of_lookup source _ comparison.rightOriginal.lookup]
    exact comparison.labelEq
  have sourceIso : SuccessfulEndpointIso source sourceClosed (SyntaxIncidence.source source left) (SyntaxIncidence.source source right) := by
    rw [SyntaxIncidence.source_eq_of_spec source _ comparison.leftOriginal.sourceSpec,
      SyntaxIncidence.source_eq_of_spec source _ comparison.rightOriginal.sourceSpec]
    exact comparison.sourceIso
  have targetIso : SuccessfulEndpointIso source sourceClosed (SyntaxIncidence.target source sourceClosed left) (SyntaxIncidence.target source sourceClosed right) := by
    rw [SyntaxIncidence.target_eq_of_spec source sourceClosed _ comparison.leftOriginal.targetSpec,
      SyntaxIncidence.target_eq_of_spec source sourceClosed _ comparison.rightOriginal.targetSpec]
    exact comparison.targetIso
  exact ⟨left,right,ePos,lPos,(fun eq=>distinct (congrArg Subtype.val eq)),
    comparison.leftAux,comparison.rightAux,same,sourceIso,targetIso,GivenNormalFalseOriginalComparison.source_fragments (left:=l) (right:=r) er lr comparison selection auxiliary⟩

namespace Terminal
abbrev bare : Term:=.app (.lam (.app (.var 0) I)) I
abbrev original : LTerm:=initLabels bare
abbrev current : LTerm:=WrappedSuccessfulChains.contractRoot original
abbrev body : LTerm:=.app (.atom 2) (.var (.atom 3) 0) (.lam (.atom 4) (.var (.atom 5) 0))
abbrev argument : LTerm:=.lam (.atom 6) (.var (.atom 7) 0)

def actualHistory : History [[]] original current:=.cons (.root _ _ _ _) (.nil _)
def actualChain : PrerequisiteChain current [.fn] [[.fn]]:=.redex_lam (p:=[]) rfl

def actualOrigin : BetaIncomingReadingOrigin body argument [] [.fn] [.fn] [.arg] [.arg] [.fn,.body,.fn] :=
  .copyLambda rfl rfl rfl rfl

/-- Normal nonempty q alone allows a terminal FUNCTION variable LAST,
which is nonAux. The high requires actual nonempty AFTER instead. -/
theorem actual_terminal_scope_boundary :
    INIT original ∧History [[]] original current ∧
    PrerequisiteChain current [.fn] [[.fn]] ∧
    original.subterm []=some (.app (.atom 0) (.lam (.atom 1) body) argument) ∧
    original.subterm [.fn,.body,.fn]=some (.var (.atom 3) 0) ∧
    ¬AuxiliaryAt original [.fn,.body,.fn] ∧
    ([.fn] : Path)≠[] ∧([[.fn]] : List Path).tail=[] := by
  refine ⟨init_is_INIT _,actualHistory,actualChain,rfl,rfl,?_,by decide,rfl⟩
  intro aux
  exact aux.1 ⟨[.fn,.body],.atom 2,.var (.atom 3) 0,.lam (.atom 4) (.var (.atom 5) 0),rfl,rfl⟩
end Terminal

#print axioms actual_given_cross_prefix_aux
#print axioms actual_source_aux_literal_pieces
#print axioms Terminal.actualHistory
#print axioms Terminal.actualChain
#print axioms Terminal.actualOrigin
#print axioms Terminal.actual_terminal_scope_boundary
end Lamping.Checks.NormalFalseCanonicalOriginalComparisonChecks
