import Lamping.Lamping.BetaChainEvaluatedResiduals
import Lamping.Lamping.ActualCurrentAfterChains

namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {current : LTerm} {g : Net signature N B W} {root : B}

/-- Only the forward implication for actual whole-chain pairs of strictly
smaller max length. A future well-founded proof supplies this IH; it is not
full target REP or an assumption stored in a graph/history. -/
def ChainForwardBelow (closed : Closed current.erase)
    (selection : OccurrenceFragmentSelection current g root) (bound : Nat) : Prop :=
  ∀{p q es fs} (first : PrerequisiteChain current p es) (second : PrerequisiteChain current q fs),
    max es.length fs.length<bound →
    ChainIncidenceIsomorphic (chainSyntaxIncidence current closed es) (chainSyntaxIncidence current closed fs) →
      SameChainRepresentation selection first second
end

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Graph.Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))

/-- Derived physical/evaluator data at the EXACT actual AFTER cuts. Every
field is a theorem output; no caller supplies this package as an invariant. -/
structure BoundedAfterPhysicalOutput
    {root : B} {source target localTarget : LTerm} {F ps : List Path} {degree : Label}
    {ls rs : Path} {les res : List Path}
    (left : ActualUnsafeMarkerCut F ps source target degree ls les)
    (right : ActualUnsafeMarkerCut F ps source target degree rs res)
    (edge : BetaEdge site.net)
    (selection : SourceEdgeSelection (initLabels source.erase) site.net root)
    (targetSelection : OccurrenceFragmentSelection target site.reduce root) where
  leftMore : left.after≠[]
  rightMore : right.after≠[]
  sameDirection : left.forward=right.forward
  beforeLength : left.before.length=right.before.length
  beforeLabels : left.before.map target.labelAt=right.before.map target.labelAt
  headLabels : target.labelAt left.edge=target.labelAt right.edge
  afterLabels : left.after.map target.labelAt=right.after.map target.labelAt
  leftNext : Path
  rightNext : Path
  leftStart : ActualAfterStart target left.reader left.edge leftNext
  rightStart : ActualAfterStart target right.reader right.edge rightNext
  leftChain : PrerequisiteChain target leftNext left.after
  rightChain : PrerequisiteChain target rightNext right.after
  strictlySmaller : max left.after.length right.after.length<max les.length res.length
  physical : SameChainRepresentation targetSelection leftChain rightChain
  leftEvaluation : EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection leftChain
  rightEvaluation : EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection rightChain
  evaluations : leftEvaluation.blocks site=rightEvaluation.blocks site

theorem BoundedAfterPhysicalOutput.first_blocks
    {root : B} {source target localTarget : LTerm} {F ps : List Path} {degree : Label}
    {ls rs : Path} {les res : List Path}
    {left : ActualUnsafeMarkerCut F ps source target degree ls les}
    {right : ActualUnsafeMarkerCut F ps source target degree rs res}
    {edge : BetaEdge site.net}
    {selection : SourceEdgeSelection (initLabels source.erase) site.net root}
    {targetSelection : OccurrenceFragmentSelection target site.reduce root}
    (out : BoundedAfterPhysicalOutput site (localTarget:=localTarget) left right edge selection targetSelection) :
    (canonicalChainImage targetSelection out.leftChain).head?=(canonicalChainImage targetSelection out.rightChain).head? ∧
      (out.leftEvaluation.blocks site).head?=(out.rightEvaluation.blocks site).head? :=
  ⟨congrArg List.head? out.physical,congrArg List.head? out.evaluations⟩

/-- Internally cut an actual parent iso pair and use only the genuine
strictly-shorter CURRENT-chain IH. ONE actual beta producer links the tail
physical equality to complete ordered local evaluator block equality.
This is not the missing outer induction or the unsafe-head reconstruction. -/
theorem PathSite.beta_bounded_actual_after_comparison
    {root : B} {source target initialSource : LTerm} {ps F prior : List Path} {marked oldMarked : Marked}
    {ls rs : Path} {les res : List Path} {degree : Label}
    (closed : Closed source.erase) (matching : Matches site.net root source.erase)
    (inputs : RootInputs site.net root)
    {boundary : B→Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {heights : B→Int} (balance : IndexedLevelBalance site.net heights) (rootDepth : heights root=0)
    (transparency : Transparency site.net root)
    (relative : Marked.RelativeHistory ps (Marked.mark (site.betaSyntaxFiber root source.erase) source.erase) marked)
    (normal : Marked.Normal marked) (history : History ps source target)
    (initial : INIT initialSource) (prefixHistory : History prior initialSource source)
    (old : Marked.RelativeOldHistory F ps (Marked.mark F source.erase) oldMarked)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (targetSelection : OccurrenceFragmentSelection target site.reduce root)
    (first : PrerequisiteChain target ls les) (second : PrerequisiteChain target rs res)
    (iso : ChainIncidenceIso (chainSyntaxIncidence target (history.closed closed) les)
      (chainSyntaxIncidence target (history.closed closed) res))
    (ih : ChainForwardBelow (history.closed closed) targetSelection (max les.length res.length)) :
    ∃localTarget,History ps (initLabels source.erase) localTarget ∧
      ∃edge : BetaEdge site.net,∃selection : SourceEdgeSelection (initLabels source.erase) site.net root,
        SiteBetaGeometry site edge ∧
        (((∀e∈les,degreeReadSafe degree (target.labelAt e)) ∧(∀e∈res,degreeReadSafe degree (target.labelAt e))) ∨
          (∃left : ActualUnsafeMarkerCut F ps source target degree ls les,
            ∃right : ActualUnsafeMarkerCut F ps source target degree rs res,left.after=[] ∧right.after=[]) ∨
          (∃left : ActualUnsafeMarkerCut F ps source target degree ls les,
            ∃right : ActualUnsafeMarkerCut F ps source target degree rs res,
              Nonempty (BoundedAfterPhysicalOutput site (localTarget:=localTarget) left right edge selection targetSelection))) := by
  obtain ⟨localTarget,localHistory,_erase,_targetMatches,edge,selection,geometry,allChains⟩ :=
    site.beta_evaluated_chain_residuals closed matching inputs flow positive balance rootDepth transparency
      relative normal history targetSelection
  refine ⟨localTarget,localHistory,edge,selection,geometry,?_⟩
  rcases actual_first_unsafe_current_after initial prefixHistory old history selected sourceSafe (history.closed closed)
      first second iso with safe|cuts
  · exact Or.inl safe
  · obtain ⟨left,right,beforeLength,front,head,afterLabels,smallerLeft,smallerRight,afterCase⟩ := cuts
    rcases afterCase with terminal|nonempty
    · exact Or.inr (Or.inl ⟨left,right,terminal⟩)
    · obtain ⟨leftMore,rightMore,sameDirection,ln,rn,lg,rg,lc,rc,tailIso⟩ := nonempty
      have smaller : max left.after.length right.after.length<max les.length res.length := by omega
      have physical := ih lc rc smaller tailIso
      obtain ⟨leval⟩ := allChains lc
      obtain ⟨reval⟩ := allChains rc
      have evaluations := leval.blocks_eq_of_target_images site geometry reval physical
      exact Or.inr (Or.inr ⟨left,right,⟨{
        leftMore:=leftMore,rightMore:=rightMore,sameDirection:=sameDirection
        beforeLength:=beforeLength,beforeLabels:=front,headLabels:=head,afterLabels:=afterLabels
        leftNext:=ln,rightNext:=rn,leftStart:=lg,rightStart:=rg,leftChain:=lc,rightChain:=rc
        strictlySmaller:=smaller,physical:=physical,leftEvaluation:=leval,rightEvaluation:=reval,evaluations:=evaluations }⟩⟩)
end

#print axioms BoundedAfterPhysicalOutput.first_blocks
#print axioms PathSite.beta_bounded_actual_after_comparison
end Lamping.AG
