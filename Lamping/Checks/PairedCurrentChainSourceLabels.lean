import Lamping.Lamping.PairedCurrentChainSourceLabels
import Lamping.Checks.ActualUnsafeMarkerLeaves
namespace Lamping.Checks.PairedCurrentChainSourceLabelsChecks
open Graph Lambda Lambda.Labelled AG SyntaxIncidence

namespace NoninitialDistinct
abbrev I : Term:=WrappedSuccessfulChains.I
abbrev K : Term:=.lam (.app (.var 0) I)
abbrev A : Term:=.app (.lam (.app I (.var 0))) K
abbrev original : LTerm:=initLabels (.app (.lam (.app (.var 0) (.var 0))) A)
abbrev source : LTerm:=WrappedSuccessfulChains.contractRoot original
abbrev left : LTerm:=match source with | .app _ l _=>l |t=>t
abbrev right : LTerm:=match source with | .app _ _ r=>r |t=>t
abbrev middle : LTerm:=.app source.label (WrappedSuccessfulChains.contractRoot left) right
abbrev current : LTerm:=.app source.label (WrappedSuccessfulChains.contractRoot left) (WrappedSuccessfulChains.contractRoot right)
abbrev body : LTerm:=.app (.atom 7) (.lam (.atom 8) (.var (.atom 9) 0)) (.var (.atom 10) 0)
abbrev argument : LTerm:=.lam (.atom 11) (.app (.atom 12) (.var (.atom 13) 0) (.lam (.atom 14) (.var (.atom 15) 0)))
abbrev F : List Path:=[[.fn],[.arg]]
abbrev leftStart : Path:=[.fn,.arg]
abbrev rightStart : Path:=[.arg,.arg]
abbrev leftEdges : List Path:=[leftStart,[.fn,.fn]]
abbrev rightEdges : List Path:=[rightStart,[.arg,.fn]]
abbrev newArgument : LTerm:=.lam (((Label.atom 10).concat (Label.atom 6).under).concat (.atom 11))
  (.app (.atom 12) (.var (.atom 13) 0) (.lam (.atom 14) (.var (.atom 15) 0)))
abbrev markedI : Marked:=.lam (.var 0)
abbrev markedK : Marked:=.lam (.app [] (.var 0) markedI)
abbrev markedPiece (name : Path) : Marked:=.app [name] markedI markedK

def prefixHistory : History [[]] original source:=.cons (.root _ _ _ _) (.nil _)
def firstStep : StepAt [.fn] source middle:=.fn (.root _ _ _ _)
def secondStep : StepAt [.arg] middle current:=.arg (.root _ _ _ _)
def labels : History [[.fn],[.arg]] source current:=.cons firstStep (.cons secondStep (.nil _))
def old : Marked.RelativeOldHistory F [[.fn],[.arg]] (Marked.mark F source.erase) (.app [] (markedPiece [.fn,.fn,.body]) (markedPiece [.arg,.fn,.body])):=
  .cons (.appL (.redRoot _ _ _)) (by decide) (.cons (.appR (.redRoot _ _ _)) (by decide) (.nil _))
theorem initial : INIT original:=init_is_INIT _
theorem originalClosed : Closed original.erase:=by simp [Closed,Scoped,original,initLabels,initFrom,nodeCount,LTerm.erase]
theorem sourceClosed : Closed source.erase:=prefixHistory.closed originalClosed
theorem currentClosed : Closed current.erase:=labels.closed sourceClosed
theorem sourceNotInit : ¬INIT source:=root_contract_not_INIT _ _ _ _
theorem selected (name : Path) (member : name∈F) : source.degreeAt name=some (.atom 6) := by
  rcases List.mem_cons.mp member with rfl |member
  · rfl
  · have same:=List.mem_singleton.mp member;subst name;rfl

theorem sourceSafe : source.OuterBarsSafe (fun x=>x≠Label.atom 6) := by
  dsimp [source,original,A,K,I,WrappedSuccessfulChains.I,WrappedSuccessfulChains.contractRoot,
    initLabels,initFrom,nodeCount,LTerm.contract,LTerm.subst,LTerm.single,LTerm.prepend,LTerm.rename,LTerm.lift,
    LTerm.label,Label.concat,Label.over,Label.under,Label.atom]
  simp only [LTerm.OuterBarsSafe,Label.OuterBarsSafe]
  decide

def leftTrace : BetaNodeHistoryPreimage labels leftStart leftStart:=
  .one (step:=firstStep) (by rfl) (.copied (body:=body) (argument:=argument) (q:=[.arg]) (relative:=[]) (old:=argument) rfl rfl)
    (.one (step:=secondStep) (by rfl) (.context (by rintro ⟨rest,eq⟩;cases eq)) (.nil _ _))
def rightTrace : BetaNodeHistoryPreimage labels rightStart rightStart:=
  .one (step:=firstStep) (by rfl) (.context (by rintro ⟨rest,eq⟩;cases eq))
    (.one (step:=secondStep) (by rfl) (.copied (body:=body) (argument:=argument) (q:=[.arg]) (relative:=[]) (old:=argument) rfl rfl) (.nil _ _))
def leftChain : PrerequisiteChain current leftStart leftEdges:=
  .lam (parent:=[.fn]) (step:=.arg) rfl (by decide) (.redex_app rfl)
def rightChain : PrerequisiteChain current rightStart rightEdges:=
  .lam (parent:=[.arg]) (step:=.arg) rfl (by decide) (.redex_app rfl)
def originalLeftChain : PrerequisiteChain source leftStart leftEdges:=
  .lam (parent:=[.fn]) (step:=.arg) rfl (by decide) (.redex_app rfl)
def originalRightChain : PrerequisiteChain source rightStart rightEdges:=
  .lam (parent:=[.arg]) (step:=.arg) rfl (by decide) (.redex_app rfl)

theorem currentIso : ChainIncidenceIsomorphic (chainSyntaxIncidence current currentClosed leftEdges)
    (chainSyntaxIncidence current currentClosed rightEdges) :=
  actual_chain_iso_of_labels (prefixHistory.append labels) initial currentClosed leftChain rightChain rfl

theorem marked : ¬degreeReadSafe (.atom 6) (current.labelAt leftStart) := by
  intro safe
  apply firstStep.created_label_not_safe (show source.subterm [.fn]=some (.app left.label (.lam (.atom 6) body) argument) from rfl)
    (current:=newArgument) (edge:=leftStart) (by rfl) (by decide)
  exact safe _ rfl

private theorem cut_after_nonempty (cut : ActualUnsafeMarkerCut F [[.fn],[.arg]] source current (.atom 6) start leftEdges) :
    cut.after≠[] := by
  have beforeEmpty : cut.before=[] := by
    cases front : cut.before with
    | nil => rfl
    | cons head tail =>
      have split:=cut.split;rw [front] at split
      have eq:head=leftStart := (List.cons.inj split).1.symm
      have good:=cut.safeBefore head (by rw [front];exact List.mem_cons_self)
      rw [eq] at good;exact False.elim (marked good)
  have split:=cut.split;rw [beforeEmpty,List.nil_append] at split
  have afterEq : cut.after=[[.fn,.fn]] := (List.cons.inj split).2.symm
  rw [afterEq];simp

theorem actual_noninitial_distinct_reflection :
    ∃left : ActualUnsafeMarkerCut F [[.fn],[.arg]] source current (.atom 6) leftStart leftEdges,
    ∃right : ActualUnsafeMarkerCut F [[.fn],[.arg]] source current (.atom 6) rightStart rightEdges,
      left.after≠[] ∧left.forward=right.forward ∧
      left.before.map current.labelAt=right.before.map current.labelAt ∧
      current.labelAt left.edge=current.labelAt right.edge ∧
      leftEdges.map source.labelAt=rightEdges.map source.labelAt ∧
      ChainIncidenceIsomorphic (chainSyntaxIncidence source sourceClosed leftEdges) (chainSyntaxIncidence source sourceClosed rightEdges) := by
  obtain ⟨iso⟩:=currentIso
  rcases paired_current_chain_source_labels initial prefixHistory old labels selected sourceSafe sourceClosed currentClosed
      leftChain rightChain iso leftTrace rightTrace with all | same | opposite
  · exact False.elim (marked (all.1.1 leftStart (List.mem_cons_self)))
  · obtain ⟨left,right,direction,front,head,les,res,lc,rc,fullEq,sourceIso⟩:=same
    have lEq:=lc.unique originalLeftChain
    have rEq:=rc.unique originalRightChain
    subst les;subst res
    exact ⟨left,right,cut_after_nonempty left,direction,front,head,fullEq,sourceIso⟩
  · obtain ⟨left,right,empty,_,_,_,_⟩:=opposite
    exact False.elim (cut_after_nonempty left empty)

theorem unsafeMiddle : ¬middle.OuterBarsSafe (fun x=>x≠Label.atom 6) := by
  intro safe
  have bad:=firstStep.created_label_not_safe
    (show source.subterm [.fn]=some (.app left.label (.lam (.atom 6) body) argument) from rfl)
    (current:=newArgument) (edge:=leftStart) (by rfl) (by decide)
  exact bad ((LTerm.outerBarsSafe_iff _ _).mp safe _ (LTerm.label_mem_of_subterm (by rfl : middle.subterm leftStart=some newArgument)))

theorem actual_history_and_roles : INIT original ∧Closed original.erase ∧
    History [[],[.fn],[.arg]] original current ∧¬INIT source ∧
    ¬middle.OuterBarsSafe (fun x=>x≠Label.atom 6) ∧leftStart≠rightStart ∧
    current.subterm leftStart=some newArgument ∧current.subterm rightStart=some newArgument :=
  ⟨initial,originalClosed,prefixHistory.append labels,sourceNotInit,unsafeMiddle,by decide,rfl,rfl⟩
end NoninitialDistinct

namespace ZeroJump
open NoninitialDistinct
abbrev leftLeaf : Path:=leftStart++[.body,.fn]
abbrev rightLeaf : Path:=rightStart++[.body,.fn]
def leftLeafTrace : BetaNodeHistoryPreimage labels leftLeaf leftLeaf:=
  .one (step:=firstStep) (by rfl) (.copied (body:=body) (argument:=argument) (q:=[.arg]) (relative:=[.body,.fn]) (old:=.var (.atom 13) 0) rfl rfl)
    (.one (step:=secondStep) (by rfl) (.context (by rintro ⟨rest,eq⟩;cases eq)) (.nil _ _))
def rightLeafTrace : BetaNodeHistoryPreimage labels rightLeaf rightLeaf:=
  .one (step:=firstStep) (by rfl) (.context (by rintro ⟨rest,eq⟩;cases eq))
    (.one (step:=secondStep) (by rfl) (.copied (body:=body) (argument:=argument) (q:=[.arg]) (relative:=[.body,.fn]) (old:=.var (.atom 13) 0) rfl rfl) (.nil _ _))
def leftLeafChain : PrerequisiteChain current leftLeaf leftEdges:=
  .var (parent:=leftStart) (rest:=[.fn]) rfl rfl rfl rfl leftChain
def rightLeafChain : PrerequisiteChain current rightLeaf rightEdges:=
  .var (parent:=rightStart) (rest:=[.fn]) rfl rfl rfl rfl rightChain
def originalLeftLeafChain : PrerequisiteChain source leftLeaf leftEdges:=
  .var (parent:=leftStart) (rest:=[.fn]) rfl rfl rfl rfl originalLeftChain
def originalRightLeafChain : PrerequisiteChain source rightLeaf rightEdges:=
  .var (parent:=rightStart) (rest:=[.fn]) rfl rfl rfl rfl originalRightChain

theorem actual_binder_start_reflection : ∃es fs,
    PrerequisiteChain source leftLeaf es ∧PrerequisiteChain source rightLeaf fs ∧
    es.map source.labelAt=fs.map source.labelAt ∧
    ChainIncidenceIsomorphic (chainSyntaxIncidence source sourceClosed es) (chainSyntaxIncidence source sourceClosed fs) := by
  obtain ⟨iso⟩:=currentIso
  rcases paired_current_chain_source_labels initial prefixHistory old labels selected sourceSafe sourceClosed currentClosed
      leftLeafChain rightLeafChain iso leftLeafTrace rightLeafTrace with safe | same | opposite
  · exact False.elim (marked (safe.1.1 leftStart List.mem_cons_self))
  · obtain ⟨l,r,d,front,head,es,fs,lc,rc,equal,oldIso⟩:=same
    exact ⟨es,fs,lc,rc,equal,oldIso⟩
  · obtain ⟨l,r,empty,_,_,_,_⟩:=opposite
    exact False.elim (NoninitialDistinct.cut_after_nonempty l empty)

theorem actual_safe_incoming_not_read_safe :
    current.subterm leftLeaf=some (.var (.atom 13) 0) ∧
    current.labelAt leftLeaf=some (.atom 13) ∧
    (Label.atom 13).OuterBarsSafe (fun x=>x≠Label.atom 6) ∧
    ¬degreeReadSafe (.atom 6) (current.labelAt leftStart) ∧leftLeaf≠leftStart :=
  ⟨rfl,rfl,by trivial,marked,by decide⟩
end ZeroJump

namespace Terminal
open DirectedReadingDecompositionChecks
abbrev currentClosed : Closed target.erase:=history.closed closed
abbrev old := DirectedMarkerLeafWordsChecks.RootOverlap.old
abbrev selected := DirectedMarkerLeafWordsChecks.RootOverlap.selected
abbrev sourceSafe := initial.outerBarsSafe (fun x=>x≠Label.atom 2)

def appTrace : BetaNodeHistoryPreimage history [] []:=
  .one (step:=step) (by rfl) (.context (by rintro ⟨rest,eq⟩;cases eq)) (.nil _ _)
def lamTrace : BetaNodeHistoryPreimage history [.fn] [.fn,.arg]:=
  .one (step:=step) (by rfl) (.copied (body:=.var (.atom 3) 0) (argument:=arg) (q:=[]) (relative:=[]) rfl rfl) (.nil _ _)
def oldApp : PrerequisiteChain source [] [[.fn],[.fn,.fn]]:=
  .app rfl (by intro a b impossible;cases impossible) (.redex_app rfl)
def oldLam : PrerequisiteChain source [.fn,.arg] [[.fn,.arg],[.fn,.fn]]:=
  .lam (parent:=[.fn]) (step:=.arg) rfl (by decide) (.redex_app rfl)

theorem no_complete_old_label_match : ¬∃es fs,PrerequisiteChain source [] es ∧
    PrerequisiteChain source [.fn,.arg] fs ∧es.map source.labelAt=fs.map source.labelAt := by
  rintro ⟨es,fs,lc,rc,equal⟩
  have le:=lc.unique oldApp
  have re:=rc.unique oldLam
  rw [le,re] at equal
  have different : [[Step.fn],[.fn,.fn]].map source.labelAt≠[[.fn,.arg],[.fn,.fn]].map source.labelAt := by decide
  exact different equal

theorem no_original_bare_iso : ¬ChainIncidenceIsomorphic
    (chainSyntaxIncidence source closed [[.fn],[.fn,.fn]])
    (chainSyntaxIncidence source closed [[.fn,.arg],[.fn,.fn]]) := by
  rintro ⟨iso⟩
  have same:=actual_chain_labels_forward (.nil source) initial closed oldApp oldLam iso
  exact no_complete_old_label_match ⟨_,_,oldApp,oldLam,same⟩

theorem actual_opposite_terminal_exception :
    ∃left : ActualUnsafeMarkerCut [[.fn]] [[.fn]] source target (.atom 2) [] [[.fn]],
    ∃right : ActualUnsafeMarkerCut [[.fn]] [[.fn]] source target (.atom 2) [.fn] [[.fn]],
      left.after=[] ∧right.after=[] ∧left.forward≠right.forward := by
  rcases paired_current_chain_source_labels initial (.nil source) old history selected sourceSafe closed currentClosed
      successful_function successful_context (ChainIncidenceIso.refl _) appTrace lamTrace with safe | same | opposite
  · obtain ⟨_,es,fs,lc,rc,equal,_⟩:=safe
    exact False.elim (no_complete_old_label_match ⟨es,fs,lc,rc,equal⟩)
  · obtain ⟨l,r,d,front,head,es,fs,lc,rc,equal,_⟩:=same
    exact False.elim (no_complete_old_label_match ⟨es,fs,lc,rc,equal⟩)
  · obtain ⟨l,r,le,re,d,_,_⟩:=opposite
    exact ⟨l,r,le,re,d⟩

private theorem root_cut_true
    (cut : ActualUnsafeMarkerCut [[.fn]] [[.fn]] source target (.atom 2) [] [[.fn]]) : cut.forward=true := by
  have sizes:=congrArg List.length cut.split
  simp only [List.length_append,List.length_cons,List.length_nil] at sizes
  have empty : cut.before=[]:=List.length_eq_zero_iff.mp (by omega)
  have zeroPrefix {t : LTerm} {start finish : Path} {es : List Path}
      (segment : PrerequisitePrefix t start es finish) (empty : es=[])
      (proper : ∀stamp index,t.subterm start≠some (.var stamp index)) : finish=start := by
    cases segment with
    | refl => rfl
    | app => cases empty
    | lam => cases empty
    | var lookup => exact False.elim (proper _ _ lookup)
  have reader : cut.reader=[] := zeroPrefix cut.segment empty (by intro stamp index same;cases same)
  have edge : cut.edge=[.fn] := by
    have split:=cut.split;rw [empty,List.nil_append] at split
    exact (List.cons.inj split).1.symm
  cases f:cut.forward
  · have same:=cut.reading.2;rw [f] at same
    change cut.edge=cut.reader at same
    rw [edge,reader] at same;cases same
  · rfl

theorem actual_same_sign_terminal_positive :
    ∃left right : ActualUnsafeMarkerCut [[.fn]] [[.fn]] source target (.atom 2) [] [[.fn]],
      left.forward=true ∧right.forward=true ∧
      ∃es fs,PrerequisiteChain source [] es ∧PrerequisiteChain source [] fs ∧
        es.map source.labelAt=fs.map source.labelAt ∧
        ChainIncidenceIsomorphic (chainSyntaxIncidence source closed es) (chainSyntaxIncidence source closed fs) := by
  have marked : ¬degreeReadSafe (.atom 2) (target.labelAt [.fn]) := by
    intro safe
    exact (step.created_label_not_safe (by rfl) (current:=result) (edge:=[.fn]) (by rfl) (Or.inl rfl)) (safe _ rfl)
  rcases paired_current_chain_source_labels initial (.nil source) old history selected sourceSafe closed currentClosed
      successful_function successful_function (ChainIncidenceIso.refl _) appTrace appTrace with safe | same | opposite
  · exact False.elim (marked (safe.1.1 [.fn] (List.mem_singleton_self _)))
  · obtain ⟨l,r,d,front,head,es,fs,lc,rc,equal,iso⟩:=same
    exact ⟨l,r,root_cut_true l,root_cut_true r,es,fs,lc,rc,equal,iso⟩
  · obtain ⟨l,r,_,_,different,_,_⟩:=opposite
    exact False.elim (different ((root_cut_true l).trans (root_cut_true r).symm))
end Terminal

namespace AllSafe
open ActualUnsafeMarkerLeavesChecks.Nonterminal
abbrev rootChain : PrerequisiteChain source [] [[.fn]]:=.redex_app rfl
abbrev safe : source.OuterBarsSafe (fun x=>x≠Label.atom 99):=initial.outerBarsSafe _

theorem actual_safe_source_vectors : ∃es fs,PrerequisiteChain source [] es ∧PrerequisiteChain source [] fs ∧
    es.map source.labelAt=fs.map source.labelAt ∧
    ChainIncidenceIsomorphic (chainSyntaxIncidence source sourceClosed es) (chainSyntaxIncidence source sourceClosed fs) := by
  have old : Marked.RelativeOldHistory [] [] (Marked.mark [] source.erase) (Marked.mark [] source.erase):=.nil _
  rcases paired_current_chain_source_labels initial (.nil source) old (.nil source)
      (degree:=.atom 99) (by intro name member;cases member) safe sourceClosed sourceClosed
      rootChain rootChain (ChainIncidenceIso.refl _) (.nil _ _) (.nil _ _) with good | same | opposite
  · exact good.2
  · obtain ⟨l,r,rest⟩:=same
    exact False.elim (l.marked ((LTerm.outerBarsSafe_iff _ _).mp safe _ (LTerm.label_mem_of_subterm l.lookup)))
  · obtain ⟨l,r,rest⟩:=opposite
    exact False.elim (l.marked ((LTerm.outerBarsSafe_iff _ _).mp safe _ (LTerm.label_mem_of_subterm l.lookup)))
end AllSafe

#print axioms paired_current_chain_source_labels
#print axioms NoninitialDistinct.old
#print axioms NoninitialDistinct.leftTrace
#print axioms NoninitialDistinct.rightTrace
#print axioms NoninitialDistinct.actual_noninitial_distinct_reflection
#print axioms NoninitialDistinct.actual_history_and_roles
#print axioms NoninitialDistinct.unsafeMiddle
#print axioms Terminal.no_complete_old_label_match
#print axioms Terminal.no_original_bare_iso
#print axioms Terminal.actual_opposite_terminal_exception
#print axioms Terminal.actual_same_sign_terminal_positive
#print axioms AllSafe.actual_safe_source_vectors
#print axioms ZeroJump.actual_binder_start_reflection
#print axioms ZeroJump.actual_safe_incoming_not_read_safe
end Lamping.Checks.PairedCurrentChainSourceLabelsChecks
