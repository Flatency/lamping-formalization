import Lamping.Lamping.TerminalHeadSuppliers
import Lamping.Lamping.NonterminalFarBoundary
import Lamping.Lamping.LocalSourceFragmentEvaluation

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

private theorem lambda_chain_first
    (chain : PrerequisiteChain t p edges) (lookup : t.subterm p=some (.lam stamp body)) :
    ∃tail,edges=p::tail := by
  cases chain with
  | redex_app atApp => rw [lookup] at atApp;cases atApp
  | redex_lam => exact ⟨[],rfl⟩
  | app atApp => rw [lookup] at atApp;cases atApp
  | lam => exact ⟨_,rfl⟩
  | var atVar => rw [lookup] at atVar;cases atVar

private theorem local_lambda_basis
    {source target : LTerm}
    (history : History ps (initLabels source.erase) target)
    (lookup : target.subterm p=some (.lam stamp body)) (last : stamp.lastAtom=some n) :
    ∃oldPosition env ctx oldBody,
      SourceSubterm [] .external (initLabels source.erase) oldPosition env ctx (.lam (.atom n) oldBody) ∧
      BetaNodeHistoryPreimage history p oldPosition := by
  obtain ⟨oldPosition,_node,_atNode,trace⟩ := history.node_preimage_from_lookup lookup
  obtain ⟨old,atOld,lastAtom,tag⟩ := trace.lastAtom_constructor lookup
  cases old with
  | var => cases tag
  | app => cases tag
  | lam oldStamp oldBody =>
    obtain ⟨m,atomic⟩ := (init_is_INIT source.erase).1 oldStamp (LTerm.label_mem_of_subterm atOld)
    have equal : n=m := by
      have atoms := last.symm.trans lastAtom
      simpa only [LTerm.label,atomic,Label.lastAtom,Label.atom,Option.some.injEq] using atoms
    subst m
    rw [atomic] at atOld
    obtain ⟨env,ctx,occurrence⟩ := SourceSubterm.of_lookup _ atOld [] .external
    exact ⟨oldPosition,env,ctx,oldBody,occurrence,trace⟩

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}

/-- The complete SOURCE chains refer to the OWN original lambda nodes.
Their actual first slots identify the writing-last atoms; no Aux or
original APP/lambda parent-start comparison is used. -/
theorem terminal_lambda_writing_last_atom_evaluations
    {original source current localTarget : LTerm}
    {prior ps F : List Path} {degree : Label} {marked : Marked}
    {lp rp : Path} {la ll ra rl llocal rlocal : Label}
    {lb larg rb rarg llbody rlbody : LTerm} {n m : Nat}
    (initial : INIT original) (prefixHistory : History prior original source)
    (closed : Closed source.erase)
    (old : Marked.RelativeOldHistory F ps (Marked.mark F source.erase) marked)
    (labels : History ps source current)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (localHistory : History ps (initLabels source.erase) localTarget)
    (leftRedex : current.subterm lp=some (.app la (.lam ll lb) larg))
    (rightRedex : current.subterm rp=some (.app ra (.lam rl rb) rarg))
    (sameCurrent : ll=rl)
    (leftLocal : localTarget.subterm (lp++[.fn])=some (.lam llocal llbody))
    (rightLocal : localTarget.subterm (rp++[.fn])=some (.lam rlocal rlbody))
    (leftLast : llocal.lastAtom=some n) (rightLast : rlocal.lastAtom=some m)
    (matching : Matches g root source.erase)
    (sourceSelection : OccurrenceFragmentSelection source g root)
    (sourceREP : ChainRepresentationInvariant closed sourceSelection)
    (selection : SourceEdgeSelection (initLabels source.erase) g root) :
    selection.atomWord n=selection.atomWord m := by
  obtain ⟨leftOld,le,lc,lbody,locc,ltrace⟩ := local_lambda_basis localHistory leftLocal leftLast
  obtain ⟨rightOld,re,rc,rbody,rocc,rtrace⟩ := local_lambda_basis localHistory rightLocal rightLast
  have lt := NonterminalFarBoundary.local_trace_global localHistory labels ltrace
  have rt := NonterminalFarBoundary.local_trace_global localHistory labels rtrace
  have leftCurrent : current.subterm (lp++[.fn])=some (.lam ll lb) := by
    rw [LTerm.subterm_append,leftRedex];rfl
  have rightCurrent : current.subterm (rp++[.fn])=some (.lam rl rb) := by
    rw [LTerm.subterm_append,rightRedex];rfl
  obtain ⟨leftActual,_ln,_atLeft,actualLeft⟩ := labels.node_preimage_from_lookup leftCurrent
  obtain ⟨rightActual,_rn,_atRight,actualRight⟩ := labels.node_preimage_from_lookup rightCurrent
  have leftLock : leftActual=leftOld := actualLeft.unique lt
  have rightLock : rightActual=rightOld := actualRight.unique rt
  have ownLeft : BetaNodeHistoryPreimage labels (lp++[.fn]) leftOld := leftLock ▸ actualLeft
  have ownRight : BetaNodeHistoryPreimage labels (rp++[.fn]) rightOld := rightLock ▸ actualRight
  have factor : (initLabels source.erase).relabel (initialRelabelling source 0)=source :=
    initialRelabelling_factor source 0
  have lat : source.subterm leftOld=some
      (.lam ((Label.atom n).relabel (initialRelabelling source 0)) (lbody.relabel (initialRelabelling source 0))) := by
    simpa only [factor,LTerm.relabel] using InteriorSourceBlock.lookup_relabel locc.lookup (initialRelabelling source 0)
  have rat : source.subterm rightOld=some
      (.lam ((Label.atom m).relabel (initialRelabelling source 0)) (rbody.relabel (initialRelabelling source 0))) := by
    simpa only [factor,LTerm.relabel] using InteriorSourceBlock.lookup_relabel rocc.lookup (initialRelabelling source 0)
  obtain ⟨es,fs,leftChain,rightChain,_vectors,iso⟩ := actual_redex_lambda_origin_chain_comparison
    initial prefixHistory old labels selected sourceSafe closed leftRedex rightRedex sameCurrent ownLeft ownRight
  obtain ⟨leftTail,leftSplit⟩ := lambda_chain_first leftChain lat
  obtain ⟨rightTail,rightSplit⟩ := lambda_chain_first rightChain rat
  let leftPosition : Position source.erase := ⟨leftOld,by rw [←LTerm.erase_subterm,lat];rfl⟩
  let rightPosition : Position source.erase := ⟨rightOld,by rw [←LTerm.erase_subterm,rat];rfl⟩
  have images := (sourceREP leftChain rightChain).mpr iso
  have pieces := same_chain_representation_slot (n:=0) sourceSelection leftChain rightChain images
    leftPosition rightPosition (by rw [leftSplit];rfl) (by rw [rightSplit];rfl)
  have localMatching : Matches g root (initLabels source.erase).erase := by simpa only [erase_initLabels] using matching
  have leftValue := selection.atomWord_occurrence_segments (init_is_INIT _) localMatching matching
    locc rfl (sourceSelection leftPosition)
  have rightValue := selection.atomWord_occurrence_segments (init_is_INIT _) localMatching matching
    rocc rfl (sourceSelection rightPosition)
  exact leftValue.trans (pieces.trans rightValue.symm)
end
end Lamping.AG