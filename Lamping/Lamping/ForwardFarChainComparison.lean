import Lamping.Lamping.ForwardExpandedFarOrigins
import Lamping.Lamping.PairedCurrentChainSourceLabels

namespace Lamping.Lambda.Labelled
private theorem old_append (first : Marked.RelativeOldHistory F ps a b)
    (last : Marked.RelativeOldHistory F qs b c) :
    Marked.RelativeOldHistory F (ps++qs) a c := by
  induction first with
  | nil => exact last
  | cons reduction member rest ih => exact .cons reduction member (ih last)

theorem SelectedOldTurn.final_old
    (event : SelectedOldTurn F source degree pre middle target site) :
    Marked.RelativeOldHistory F (pre++[site]) (Marked.mark F source.erase) event.markedAfter :=
  old_append event.beforeOld (.cons event.reduction event.member (.nil _))
end Lamping.Lambda.Labelled

namespace Lamping.AG
open Graph Lambda Lambda.Labelled SyntaxIncidence
variable {source middle target initialSource : LTerm}

/-- Actual complete FAR chains, with their exact producer-returned lists. -/
def ForwardFarFullComparison (closed : Closed source.erase)
    {event : SelectedOldTurn F source degree pre middle target site}
    (left : ForwardExpandedFarOutput event lr le lo lf ll la)
    (right : ForwardExpandedFarOutput event rr re ro rf rl ra) : Prop :=
  left.sourceEdges.map source.labelAt=right.sourceEdges.map source.labelAt ∧
    ChainIncidenceIsomorphic (chainSyntaxIncidence source closed left.sourceEdges)
      (chainSyntaxIncidence source closed right.sourceEdges)

/-- This is the precise remaining exception of the CURRENT tail comparator,
not a failure to produce original chains. The parent AFTER can be nonempty. -/
def ForwardFarTerminalException
    (_event : SelectedOldTurn F source degree pre middle target site)
    (leftEdge rightEdge : Path) (leftAfter rightAfter : List Path) : Prop :=
  ∃left : ActualUnsafeMarkerCut F (pre++[site]) source target degree leftEdge leftAfter,
    ∃right : ActualUnsafeMarkerCut F (pre++[site]) source target degree rightEdge rightAfter,
      left.after=[] ∧right.after=[] ∧left.forward≠right.forward ∧
      left.before.map target.labelAt=right.before.map target.labelAt ∧
      target.labelAt left.edge=target.labelAt right.edge

/-- The original FAR starts and chains are constructed internally from the
two actual forward expansions. Only CURRENT tail incidence iso is supplied. -/
theorem SelectedOldTurn.forward_far_chain_comparison
    (event : SelectedOldTurn F source degree pre middle target site)
    (initial : INIT initialSource) (prefixHistory : History prior initialSource source)
    (closed : Closed source.erase)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (leftOrigin : BetaIncomingReadingOrigin event.body event.argument site le lr lo lf ll)
    (rightOrigin : BetaIncomingReadingOrigin event.body event.argument site re rr ro rf rl)
    (leftReading : PrerequisiteReadsDirected target lr le true)
    (rightReading : PrerequisiteReadsDirected target rr re true)
    (leftLookup : target.subterm le=some leftNode)
    (rightLookup : target.subterm re=some rightNode)
    (leftRemaining : PrerequisiteChain target lr (le::la))
    (rightRemaining : PrerequisiteChain target rr (re::ra))
    (leftMore : la≠[]) (rightMore : ra≠[])
    (iso : ChainIncidenceIso
      (chainSyntaxIncidence target (event.final_history.closed closed) la)
      (chainSyntaxIncidence target (event.final_history.closed closed) ra)) :
    ∃left : ForwardExpandedFarOutput event lr le lo lf ll la,
      ∃right : ForwardExpandedFarOutput event rr re ro rf rl ra,
        ForwardFarFullComparison closed left right ∨ForwardFarTerminalException event le re la ra := by
  obtain ⟨left⟩:=event.forward_expanded_far_output closed leftOrigin leftReading leftLookup leftRemaining leftMore
  obtain ⟨right⟩:=event.forward_expanded_far_output closed rightOrigin rightReading rightLookup rightRemaining rightMore
  refine ⟨left,right,?_⟩
  rcases paired_current_chain_source_labels initial prefixHistory event.final_old event.final_history selected sourceSafe
      closed (event.final_history.closed closed) left.currentTail right.currentTail iso left.currentTrace right.currentTrace
      with safe | same | opposite
  · obtain ⟨_safe,les,res,lc,rc,labels,oldIso⟩:=safe
    have l:=lc.unique left.sourceChain
    have r:=rc.unique right.sourceChain
    exact Or.inl (by simpa only [ForwardFarFullComparison,←l,←r] using And.intro labels oldIso)
  · obtain ⟨lcut,rcut,_sign,_front,_head,les,res,lc,rc,labels,oldIso⟩:=same
    have l:=lc.unique left.sourceChain
    have r:=rc.unique right.sourceChain
    exact Or.inl (by simpa only [ForwardFarFullComparison,←l,←r] using And.intro labels oldIso)
  · exact Or.inr opposite

/-- A legal SOURCE REP IH gives ordered source images only in a proved good
branch; this asserts no physical LAST/fulltail reconstruction. -/
theorem ForwardFarFullComparison.source_images
    {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} {root : B} {closed : Closed source.erase}
    {event : SelectedOldTurn F source degree pre middle target site}
    {left : ForwardExpandedFarOutput event lr le lo lf ll la}
    {right : ForwardExpandedFarOutput event rr re ro rf rl ra}
    (comparison : ForwardFarFullComparison closed left right)
    (selection : OccurrenceFragmentSelection source g root)
    (representation : ChainRepresentationInvariant closed selection) :
    SameChainRepresentation selection left.sourceChain right.sourceChain :=
  (representation left.sourceChain right.sourceChain).mpr comparison.2

#print axioms SelectedOldTurn.forward_far_chain_comparison
#print axioms ForwardFarFullComparison.source_images
end Lamping.AG
