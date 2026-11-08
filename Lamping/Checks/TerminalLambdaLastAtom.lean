import Lamping.Lamping.TerminalLambdaLastAtom
import Lamping.Checks.TerminalHeadSuppliers

namespace Lamping.Checks.TerminalLambdaLastAtomChecks
open Graph Lambda Lambda.Labelled AG

private theorem local_lambda_actual
    {source current localTarget : LTerm}
    (labels : History ps source current)
    (localHistory : History ps (initLabels source.erase) localTarget)
    (lookup : current.subterm p=some (.lam stamp body)) :
    ∃localStamp localBody n,localTarget.subterm p=some (.lam localStamp localBody) ∧
      localStamp.lastAtom=some n := by
  have same := SpineReannotation.history_erase labels localHistory (erase_initLabels source.erase).symm
  obtain ⟨node,atNode,erased⟩ := SpineReannotation.paired_lookup same lookup
  cases node with
  | var => cases erased
  | app => cases erased
  | lam a b =>
    obtain ⟨oldPosition,_old,_atOld,trace⟩ := localHistory.node_preimage_from_lookup atNode
    obtain ⟨ancestor,atAncestor,last,_tag⟩ := trace.lastAtom_constructor atNode
    obtain ⟨n,atomic⟩ := (init_is_INIT source.erase).1 ancestor.label (LTerm.label_mem_of_subterm atAncestor)
    have result : a.lastAtom=ancestor.label.lastAtom := last
    rw [atomic] at result
    exact ⟨a,b,n,atNode,result⟩

section Physical
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}

namespace RootOverlap
open DirectedReadingDecompositionChecks
open PairedCurrentChainSourceLabelsChecks.Terminal

theorem actual_marked_q0_writing_last
    (matching : Matches g root source.erase)
    (sourceSelection : OccurrenceFragmentSelection source g root)
    (sourceREP : ChainRepresentationInvariant closed sourceSelection)
    (selection : SourceEdgeSelection (initLabels source.erase) g root) :
    ¬result.label.OuterBarsSafe (fun d=>d≠Label.atom 2) ∧
    result.label.lastAtom=some 4 ∧selection.atomWord 4=selection.atomWord 4 := by
  have value := terminal_lambda_writing_last_atom_evaluations initial (.nil source) closed
    old history selected sourceSafe history (lp:=[]) (rp:=[])
    (by rfl) (by rfl) rfl (by rfl) (by rfl) (by rfl) (by rfl)
    matching sourceSelection sourceREP selection
  refine ⟨?_,rfl,value⟩
  exact step.created_label_not_safe (by rfl) (current:=result) rfl (Or.inl rfl)

theorem retained_parent_start_negative :
    ¬∃es fs,PrerequisiteChain source [] es ∧PrerequisiteChain source [.fn,.arg] fs ∧
      es.map source.labelAt=fs.map source.labelAt := no_complete_old_label_match

theorem actual_full_overlap_words :
    result.label.readLetters true=[.atom 1,.over (.atom 2),.atom 3,.under (.atom 2),.atom 4] ∧
    result.label.readLetters false=[.atom 4,.under (.atom 2),.atom 3,.over (.atom 2),.atom 1] :=
  actual_overlap_words
end RootOverlap

namespace CP53
open SingleUnsafeCopyFunctionAppInputsChecks
abbrev localSource : LTerm := initLabels source.erase
abbrev localMiddle : LTerm := match localSource with | .app a f x=>.app a (WrappedSuccessfulChains.contractRoot f) x |t=>t
abbrev localTarget : LTerm := match localMiddle with | .app a f x=>.app a f (WrappedSuccessfulChains.contractRoot x) |t=>t

def localHistory : History [[.fn],[.arg]] localSource localTarget :=
  .cons (.fn (.root _ _ _ _)) (.cons (.arg (.root _ _ _ _)) (.nil _))

theorem actual_distinct_writing_last
    (matching : Matches g root source.erase)
    (sourceSelection : OccurrenceFragmentSelection source g root)
    (sourceREP : ChainRepresentationInvariant sourceClosed sourceSelection)
    (selection : SourceEdgeSelection (initLabels source.erase) g root) :
    ∃ls lb rs rb n m,
      localTarget.subterm (leftHead++[.fn])=some (.lam ls lb) ∧ls.lastAtom=some n ∧
      localTarget.subterm (rightHead++[.fn])=some (.lam rs rb) ∧rs.lastAtom=some m ∧
      leftHead++[.fn]≠rightHead++[.fn] ∧n=m ∧
      selection.atomWord n=selection.atomWord m := by
  obtain ⟨ls,lb,n,ll,ln⟩ : ∃s b n,localTarget.subterm (leftHead++[.fn])=some (.lam s b) ∧s.lastAtom=some n :=
    ⟨_,_,_,rfl,rfl⟩
  obtain ⟨rs,rb,m,rl,rn⟩ : ∃s b m,localTarget.subterm (rightHead++[.fn])=some (.lam s b) ∧s.lastAtom=some m :=
    ⟨_,_,_,rfl,rfl⟩
  have value := terminal_lambda_writing_last_atom_evaluations initial prefixHistory sourceClosed
    event.final_old event.final_history selected sourceSafe localHistory (lp:=leftHead) (rp:=rightHead)
    (by rfl) (by rfl) rfl ll rl ln rn matching sourceSelection sourceREP selection
  have sameAtom : n=m := by
    have actual : (localTarget.subterm (leftHead++[.fn])).map (fun t=>t.label.lastAtom)=
        (localTarget.subterm (rightHead++[.fn])).map (fun t=>t.label.lastAtom) := by rfl
    simpa only [ll,rl,Option.map_some,LTerm.label,ln,rn,Option.some.injEq] using actual
  exact ⟨ls,lb,rs,rb,n,m,ll,ln,rl,rn,by decide,sameAtom,value⟩

theorem actual_degree_safe_lambda : degreeReadSafe (.atom 6) (target.labelAt (leftHead++[.fn])) := by
  intro label eq
  have actual : label=Label.atom 17 := Option.some.inj eq.symm
  subst label
  trivial
end CP53

namespace Nested
open UniformOldNodeLabelSuffixChecks
open DirectedMarkerSpineIncidenceChecks.Nested

theorem forward_schedule_writing_last
    (matching : Matches g root sourceWrapped.erase)
    (sourceSelection : OccurrenceFragmentSelection sourceWrapped g root)
    (sourceREP : ChainRepresentationInvariant sourceClosed sourceSelection)
    (selection : SourceEdgeSelection (initLabels sourceWrapped.erase) g root) :
    ∃leaf snapshot,
    ∃geometry : SpineIncidenceProvenance family sourceWrapped (.atom 10) true forwardSpine
      (by rfl : targetForward.subterm [.fn]=some target) leaf snapshot,
    ∃localTarget,∃_localHistory : History [[.fn],[.fn]] (initLabels sourceWrapped.erase) localTarget,
    ∃stamp body n,2≤geometry.creationFrames.length ∧leaf.after≠[] ∧
      localTarget.subterm [.fn]=some (.lam stamp body) ∧stamp.lastAtom=some n ∧
      selection.atomWord n=selection.atomWord n := by
  obtain ⟨leaf,snapshot,geometry,multiple,after,_⟩ := PairedMarkerSpineReannotationChecks.Nested.forward_multiple_frames
  obtain ⟨localTarget,localHistory,_⟩ := lift_history labelsForward.betaHistory
    (initLabels sourceWrapped.erase) (erase_initLabels _)
  obtain ⟨a,l,b,arg,redex⟩ : ∃a l b arg,targetForward.subterm []=some (.app a (.lam l b) arg) := ⟨_,_,_,_,rfl⟩
  have atLambda : targetForward.subterm [.fn]=some (.lam l b) := by
    change targetForward.subterm (([] : Path)++[.fn])=_
    rw [LTerm.subterm_append,redex];rfl
  obtain ⟨stamp,body,n,atLocal,last⟩ := local_lambda_actual labelsForward localHistory atLambda
  have value := terminal_lambda_writing_last_atom_evaluations initial globalPrefix sourceClosed oldForward
    labelsForward selected sourceSafe localHistory redex redex rfl atLocal atLocal last last
    matching sourceSelection sourceREP selection
  exact ⟨leaf,snapshot,geometry,localTarget,localHistory,stamp,body,n,multiple,after,atLocal,last,value⟩

theorem reverse_schedule_writing_last
    (matching : Matches g root sourceWrapped.erase)
    (sourceSelection : OccurrenceFragmentSelection sourceWrapped g root)
    (sourceREP : ChainRepresentationInvariant sourceClosed sourceSelection)
    (selection : SourceEdgeSelection (initLabels sourceWrapped.erase) g root) :
    ∃leaf snapshot,
    ∃geometry : SpineIncidenceProvenance family sourceWrapped (.atom 10) false reverseSpine
      (by rfl : targetReverse.subterm [.fn]=some reverseResult) leaf snapshot,
    ∃localTarget,∃_localHistory : History [[.fn,.arg],[.fn]] (initLabels sourceWrapped.erase) localTarget,
    ∃stamp body n,2≤geometry.creationFrames.length ∧leaf.after≠[] ∧
      localTarget.subterm [.fn]=some (.lam stamp body) ∧stamp.lastAtom=some n ∧
      selection.atomWord n=selection.atomWord n := by
  obtain ⟨leaf,snapshot,geometry,multiple,after,_⟩ := PairedMarkerSpineReannotationChecks.Nested.reverse_multiple_frames
  obtain ⟨localTarget,localHistory,_⟩ := lift_history labelsReverse.betaHistory
    (initLabels sourceWrapped.erase) (erase_initLabels _)
  obtain ⟨a,l,b,arg,redex⟩ : ∃a l b arg,targetReverse.subterm []=some (.app a (.lam l b) arg) := ⟨_,_,_,_,rfl⟩
  have atLambda : targetReverse.subterm [.fn]=some (.lam l b) := by
    change targetReverse.subterm (([] : Path)++[.fn])=_
    rw [LTerm.subterm_append,redex];rfl
  obtain ⟨stamp,body,n,atLocal,last⟩ := local_lambda_actual labelsReverse localHistory atLambda
  have value := terminal_lambda_writing_last_atom_evaluations initial globalPrefix sourceClosed oldReverse
    labelsReverse selected sourceSafe localHistory redex redex rfl atLocal atLocal last last
    matching sourceSelection sourceREP selection
  exact ⟨leaf,snapshot,geometry,localTarget,localHistory,stamp,body,n,multiple,after,atLocal,last,value⟩
end Nested
end Physical

#print axioms terminal_lambda_writing_last_atom_evaluations
#print axioms RootOverlap.actual_marked_q0_writing_last
#print axioms RootOverlap.retained_parent_start_negative
#print axioms RootOverlap.actual_full_overlap_words
#print axioms CP53.localHistory
#print axioms CP53.actual_distinct_writing_last
#print axioms CP53.actual_degree_safe_lambda
#print axioms Nested.forward_schedule_writing_last
#print axioms Nested.reverse_schedule_writing_last
end Lamping.Checks.TerminalLambdaLastAtomChecks