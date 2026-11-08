import Lamping.Lamping.NonterminalSpineHeadComparison
import Lamping.Checks.GivenParentCanonicalFarComparison
import Lamping.Checks.PairedSpineNearComparison

namespace Lamping.Checks.NonterminalSpineHeadComparisonChecks
open Graph Lambda Lambda.Labelled AG SyntaxIncidence

section TrueTransport
variable {original source current localTarget : LTerm} {prior ps F : List Path}
variable {degree : Lambda.Labelled.Label} {marked : Marked}
variable {ls rs : Path} {les res : List Path} {labels : History ps source current}
variable {lc : ActualUnsafeMarkerCut F ps source current degree ls les}
variable {rc : ActualUnsafeMarkerCut F ps source current degree rs res}
variable (leftTrue : lc.forward=true) (rightTrue : rc.forward=true)
variable {ll : DirectedMarkerLeafOutput F source degree true ps (lc.node.label.readLetters true)}
variable {rl : DirectedMarkerLeafOutput F source degree true ps (rc.node.label.readLetters true)}
variable {lsnap : IncomingIncidenceSnapshot current lc.edge}
variable {rsnap : IncomingIncidenceSnapshot current rc.edge}
variable {lg : SpineIncidenceProvenance F source degree true (lc.asTrueSpine leftTrue) lc.lookup ll lsnap}
variable {rg : SpineIncidenceProvenance F source degree true (rc.asTrueSpine rightTrue) rc.lookup rl rsnap}
variable {localHistory : History ps (initLabels source.erase) localTarget}
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}

/-- Only transport the GIVEN true-indexed records, without rerunning geometry. -/
private theorem compare_true_pairs
    (initial : INIT original) (priorHistory : History prior original source)
    (closed : Closed source.erase)
    (old : Marked.RelativeOldHistory F ps (Marked.mark F source.erase) marked)
    (selected : ∀p∈F,source.degreeAt p=some degree)
    (safe : source.OuterBarsSafe (fun x=>x≠degree))
    (lm : lc.after≠[]) (rm : rc.after≠[])
    (iso : ChainIncidenceIso (chainSyntaxIncidence current (labels.closed closed) les)
      (chainSyntaxIncidence current (labels.closed closed) res))
    (lo : CanonicalAfterFarOutput labels lc lsnap) (ro : CanonicalAfterFarOutput labels rc rsnap)
    (lp : PairedSpineReannotation lg localHistory (erase_initLabels source.erase).symm)
    (rp : PairedSpineReannotation rg localHistory (erase_initLabels source.erase).symm)
    (ln : SpineNearFirstAtom lp) (rn : SpineNearFirstAtom rp)
    (matching : Matches g root source.erase)
    (sourceSelection : OccurrenceFragmentSelection source g root)
    (sourceJoint : JointRepresentation closed sourceSelection)
    (selection : SourceEdgeSelection (initLabels source.erase) g root) (physical : BetaEdge g) :
    selection.evalLabel physical lp.current.label=selection.evalLabel physical rp.current.label := by
  cases lc
  cases rc
  cases leftTrue
  cases rightTrue
  exact paired_nonterminal_spine_head_evaluations initial priorHistory closed old selected safe lm rm iso
    lo ro lp rp ln rn matching sourceSelection sourceJoint selection physical
end TrueTransport

namespace CP53
open SingleUnsafeCopyFunctionAppInputsChecks

/-- Real noninitial SOURCE, distinct current coordinates, SAME returned
geometries and ONE supplied local history; direct NEW complete-head comparison. -/
theorem actual_true_complete_heads
    {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} {root : B}
    (matching : Matches g root source.erase)
    (sourceSelection : OccurrenceFragmentSelection source g root)
    (sourceJoint : JointRepresentation sourceClosed sourceSelection)
    (selection : SourceEdgeSelection (initLabels source.erase) g root) (physical : BetaEdge g) :
    ∃out : SingleUnsafeCopyFunctionAppInputs event sourceClosed leftStart rightStart [.fn] [.arg] es fs,
      out.left.edge≠out.right.edge ∧out.left.forward=true ∧out.right.forward=true ∧
      ∃localTarget,∃localHistory : History [[.fn],[.arg]] (initLabels source.erase) localTarget,
      ∃lp : PairedSpineReannotation out.leftGeometry localHistory (erase_initLabels source.erase).symm,
      ∃rp : PairedSpineReannotation out.rightGeometry localHistory (erase_initLabels source.erase).symm,
      ∃_lo : CanonicalAfterFarOutput event.final_history out.left out.leftSnapshot,
      ∃_ro : CanonicalAfterFarOutput event.final_history out.right out.rightSnapshot,
        selection.evalLabel physical lp.current.label=selection.evalLabel physical rp.current.label := by
  obtain ⟨out⟩:=actual_new_inputs
  obtain ⟨localTarget,localHistory,_erase⟩:=lift_history event.final_history.betaHistory
    (initLabels source.erase) (erase_initLabels source.erase)
  obtain ⟨lp⟩:=out.leftGeometry.paired_reannotation localHistory (erase_initLabels _).symm
  obtain ⟨rp⟩:=out.rightGeometry.paired_reannotation localHistory (erase_initLabels _).symm
  obtain ⟨ln⟩:=Lamping.AG.PairedSpineReannotation.near_first_atom lp selected
  obtain ⟨rn⟩:=Lamping.AG.PairedSpineReannotation.near_first_atom rp selected
  obtain ⟨lo⟩:=out.left.canonical_far_output event.final_history sourceClosed out.leftAfterNonempty out.leftSnapshot
  obtain ⟨ro⟩:=out.right.canonical_far_output event.final_history sourceClosed out.rightAfterNonempty out.rightSnapshot
  obtain ⟨iso⟩:=currentIso
  have same:=compare_true_pairs out.leftTrue out.rightTrue initial prefixHistory sourceClosed event.final_old
    selected sourceSafe out.leftAfterNonempty out.rightAfterNonempty iso lo ro lp rp ln rn
    matching sourceSelection sourceJoint selection physical
  refine ⟨out,?_,out.leftTrue,out.rightTrue,localTarget,localHistory,lp,rp,lo,ro,same⟩
  rw [out.leftEdge,out.rightEdge]
  decide

theorem actual_original_context :
    INIT original ∧History [[.arg,.fn,.body],[],[.fn],[.arg]] original target ∧
      leftStart≠rightStart ∧¬INIT source ∧es.length=3 ∧fs.length=3 :=
  GivenParentCanonicalFarComparisonChecks.CP53.actual_history_distinct_starts
end CP53

namespace CP57
open SafeLastCopyArgumentAuxInputsChecks FalseCopyFirstSafeLabelsChecks

/-- Retain the already GIVEN early/late geometries, recents and canonicals.
The NEW comparison evaluates their complete heads, not only original LAST. -/
theorem actual_false_given_complete_heads
    {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} {root : B}
    (matching : Matches g root source.erase)
    (sourceSelection : OccurrenceFragmentSelection source g root)
    (sourceJoint : JointRepresentation sourceClosed sourceSelection)
    (selection : SourceEdgeSelection (initLabels source.erase) g root) (physical : BetaEdge g) :
    ∃el esnap,
    ∃eg : SpineIncidenceProvenance F source (.atom 6) false earlyCut.spine earlyCut.lookup el esnap,
    ∃er : RecentSpineFrame eg,
    ∃ll lsnap,
    ∃lg : SpineIncidenceProvenance F source (.atom 6) false lateCut.spine lateCut.lookup ll lsnap,
    ∃lr : RecentSpineFrame lg,
    ∃_lo : CanonicalAfterFarOutput event.final_history earlyCut esnap,
    ∃_ro : CanonicalAfterFarOutput event.final_history lateCut lsnap,
      er.packet.pre=[] ∧er.packet.site=[.fn] ∧er.suffixSites=[[.arg]] ∧
      lr.packet.pre=[[.fn]] ∧lr.packet.site=[.arg] ∧lr.suffixSites=[] ∧
      ∃localTarget,∃localHistory : History [[.fn],[.arg]] (initLabels source.erase) localTarget,
      ∃lp : PairedSpineReannotation eg localHistory (erase_initLabels source.erase).symm,
      ∃rp : PairedSpineReannotation lg localHistory (erase_initLabels source.erase).symm,
        selection.evalLabel physical lp.current.label=selection.evalLabel physical rp.current.label := by
  obtain ⟨el,esnap,eg,er,ll,lsnap,lg,lr,lo,ro,_good,ep,et,ef,lpPre,lt,lf⟩:=
    GivenParentCanonicalFarComparisonChecks.CP57.actual_same_given_cross_prefix_context
  obtain ⟨localTarget,localHistory,_erase⟩:=lift_history event.final_history.betaHistory
    (initLabels source.erase) (erase_initLabels source.erase)
  obtain ⟨lp⟩:=eg.paired_reannotation localHistory (erase_initLabels _).symm
  obtain ⟨rp⟩:=lg.paired_reannotation localHistory (erase_initLabels _).symm
  obtain ⟨ln⟩:=Lamping.AG.PairedSpineReannotation.near_first_atom lp selected
  obtain ⟨rn⟩:=Lamping.AG.PairedSpineReannotation.near_first_atom rp selected
  obtain ⟨iso⟩:=actual_chain_iso_of_labels (prefixHistory.append event.final_history) initial targetClosed
    earlyChain leftChain (by rfl)
  have same:=paired_nonterminal_spine_head_evaluations initial prefixHistory sourceClosed event.final_old
    selected sourceSafe (by decide) (by decide) iso lo ro lp rp ln rn matching sourceSelection
    sourceJoint selection physical
  exact ⟨el,esnap,eg,er,ll,lsnap,lg,lr,lo,ro,ep,et,ef,lpPre,lt,lf,localTarget,localHistory,lp,rp,same⟩
end CP57

#print axioms CP53.actual_true_complete_heads
#print axioms CP53.actual_original_context
#print axioms CP57.actual_false_given_complete_heads
end Lamping.Checks.NonterminalSpineHeadComparisonChecks
