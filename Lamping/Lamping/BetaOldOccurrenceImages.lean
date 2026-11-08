import Lamping.Lamping.BetaUncreatedRootResiduals
import Lamping.Lamping.BetaUncreatedFragmentResiduals
import Lamping.Lamping.BetaCanonicalComparison
import Lamping.Lamping.BetaAtomicComparison

namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
variable {root : B} {source target : LTerm} {ps F : List Path} {marked m n : Marked}
variable {d : Path →Option Labelled.Label} {degree : Labelled.Label}

theorem PathSite.beta_marker_free_occurrence_images
    (closed : Closed source.erase) (matching : Matches site.net root source.erase)
    (inputs : RootInputs site.net root)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {heights : B → Int} (balance : IndexedLevelBalance site.net heights) (rootDepth : heights root=0)
    (transparency : Transparency site.net root)
    (relative : Marked.RelativeHistory ps (Marked.mark (site.betaSyntaxFiber root source.erase) source.erase) marked)
    (normal : Marked.Normal marked) (history : History ps source target)
    (old : Marked.RelativeOldHistory F ps m n) (aligned : DegreeAligned d m source)
    (selected : ∀ path∈F,d path=some degree) :
    ∀ (p : Path) (child : OccurrenceFragment target site.reduce root p),
      child.term.label.OuterBarsSafe (fun payload=>payload≠degree) →
      ∃ oldPosition oldNode,source.subterm oldPosition=some oldNode ∧
        BetaNodeHistoryPreimage history p oldPosition ∧
        ∀ oldFragment : OccurrenceFragment source site.net root oldPosition,
          ∃ exterior : List (Endpoint (cutFragment site.net (pathPartition (.beta i) V) site.closed)),
            child.fragment.segments.map (plugEnd _ _).invFun=exterior.map Sum.inl ∧
            oldFragment.fragment.segments=exterior.map site.outsideEnd := by
  obtain ⟨rootEdge,rootGeometry,atRoot⟩ := site.beta_uncreated_root_residuals closed matching inputs flow positive
    balance rootDepth transparency relative normal history old aligned selected
  obtain ⟨childEdge,childGeometry,atChild⟩ := site.beta_uncreated_child_residuals closed matching inputs flow positive
    balance rootDepth transparency relative normal history old aligned selected
  intro p child safe
  rcases child.occurrence.last_departure with ⟨empty,_external⟩ |
    ⟨parent,step,parentTerm,split,atParent,role⟩
  · subst p
    obtain ⟨oldPosition,oldNode,lookup,trace,residual⟩ := atRoot child safe
    refine ⟨oldPosition,oldNode,lookup,trace,?_⟩
    intro oldFragment
    exact (residual oldFragment).atomic_exterior site rootGeometry oldFragment.fragment.emptyWord
  · have departure : SourceDeparture parentTerm step
        (sourceEdge child.environment child.context child.term).fromPort := by
      cases child.term <;> exact role
    change p=parent++[step] at split
    subst p
    obtain ⟨oldPosition,oldNode,lookup,trace,residual⟩ := atChild parent step parentTerm atParent child departure safe
    refine ⟨oldPosition,oldNode,lookup,trace,?_⟩
    intro oldFragment
    exact (residual oldFragment).atomic_exterior site childGeometry oldFragment.fragment.emptyWord

private theorem exterior_map_injective {A C : Type} {f : A →C}
    (injective : Function.Injective f) {xs ys : List A} (same : xs.map f=ys.map f) : xs=ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> first | rfl | cases same
  | cons x xs ih =>
    cases ys with
    | nil => cases same
    | cons y ys =>
      obtain ⟨head,tail⟩ := List.cons.inj same
      rw [injective head,ih tail]

/-- Actual old occurrence images compare literal whole pieces even when
one image was obtained from a root cut and the other from a child cut.
The witnesses may use different proofs of the same site's beta geometry. -/
theorem PathSite.beta_exterior_occurrence_equality
    {left right : List (Endpoint site.reduce)} {oldLeft oldRight : List (Endpoint site.net)}
    (first : ∃ exterior : List (Endpoint (cutFragment site.net (pathPartition (.beta i) V) site.closed)),
      left.map (plugEnd _ _).invFun=exterior.map Sum.inl ∧oldLeft=exterior.map site.outsideEnd)
    (second : ∃ exterior : List (Endpoint (cutFragment site.net (pathPartition (.beta i) V) site.closed)),
      right.map (plugEnd _ _).invFun=exterior.map Sum.inl ∧oldRight=exterior.map site.outsideEnd) :
    left=right ↔oldLeft=oldRight := by
  obtain ⟨l,lRaw,lOld⟩ := first
  obtain ⟨r,rRaw,rOld⟩ := second
  constructor
  · intro same
    have raw := congrArg (fun xs : List (Endpoint site.reduce)=>xs.map (plugEnd _ _).invFun) same
    dsimp only at raw
    rw [lRaw,rRaw] at raw
    have equal := exterior_map_injective (fun _ _ same=>Sum.inl.inj same) raw
    rw [lOld,rOld,equal]
  · intro same
    rw [lOld,rOld] at same
    have equal := exterior_map_injective site.outsideEnd_injective same
    have raw : left.map (plugEnd _ _).invFun=right.map (plugEnd _ _).invFun := by rw [lRaw,rRaw,equal]
    have literal := congrArg (fun xs=>xs.map (plugEnd _ _)) raw
    simpa only [List.map_map,Function.comp_def,(plugEnd _ _).right_inv,List.map_id_fun'] using literal
theorem PathSite.beta_marker_free_occurrence_pair
    (closed : Closed source.erase) (matching : Matches site.net root source.erase)
    (inputs : RootInputs site.net root)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {heights : B → Int} (balance : IndexedLevelBalance site.net heights) (rootDepth : heights root=0)
    (transparency : Transparency site.net root)
    (relative : Marked.RelativeHistory ps (Marked.mark (site.betaSyntaxFiber root source.erase) source.erase) marked)
    (normal : Marked.Normal marked) (history : History ps source target)
    (old : Marked.RelativeOldHistory F ps m n) (aligned : DegreeAligned d m source)
    (selected : ∀ path∈F,d path=some degree)
    (sourceSelection : OccurrenceFragmentSelection source site.net root)
    {leftPosition rightPosition : Path}
    (left : OccurrenceFragment target site.reduce root leftPosition)
    (right : OccurrenceFragment target site.reduce root rightPosition)
    (leftSafe : left.term.label.OuterBarsSafe (fun payload=>payload≠degree))
    (rightSafe : right.term.label.OuterBarsSafe (fun payload=>payload≠degree)) :
    ∃ leftOld rightOld,∃ (leftNode rightNode : LTerm),
      ∃ (leftLookup : source.subterm leftOld=some leftNode)
        (rightLookup : source.subterm rightOld=some rightNode),
        BetaNodeHistoryPreimage history leftPosition leftOld ∧
        BetaNodeHistoryPreimage history rightPosition rightOld ∧
        (left.fragment.segments=right.fragment.segments ↔
          (sourceSelection ⟨leftOld,by rw [←LTerm.erase_subterm,leftLookup];rfl⟩).fragment.segments=
          (sourceSelection ⟨rightOld,by rw [←LTerm.erase_subterm,rightLookup];rfl⟩).fragment.segments) := by
  have images := site.beta_marker_free_occurrence_images closed matching inputs flow positive balance rootDepth
    transparency relative normal history old aligned selected
  obtain ⟨leftOld,leftNode,leftLookup,leftTrace,leftImage⟩ := images leftPosition left leftSafe
  obtain ⟨rightOld,rightNode,rightLookup,rightTrace,rightImage⟩ := images rightPosition right rightSafe
  exact ⟨leftOld,rightOld,leftNode,rightNode,leftLookup,rightLookup,leftTrace,rightTrace,
    site.beta_exterior_occurrence_equality
      (leftImage (sourceSelection ⟨leftOld,by rw [←LTerm.erase_subterm,leftLookup];rfl⟩))
      (rightImage (sourceSelection ⟨rightOld,by rw [←LTerm.erase_subterm,rightLookup];rfl⟩))⟩
end
end Lamping.AG
