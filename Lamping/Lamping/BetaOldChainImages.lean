import Lamping.Lamping.BetaUncreatedFragmentResiduals
import Lamping.Lamping.UniformOldChainIncidencePreimages
import Lamping.Lamping.FamilyRepresentation

namespace Lamping.Lambda.Labelled
/-- A reading is always a genuine child occurrence; root lambda arrival
does not become a successful reading merely by being eligible. -/
theorem PrerequisiteChain.reading_ne_nil (chain : PrerequisiteChain target start edges)
    (member : edge∈edges) : edge≠[] := by
  induction chain with
  | redex_app | redex_lam =>
    have same := List.mem_singleton.mp member
    subst edge
    simp
  | app _ _ _ ih | lam _ _ _ ih =>
    rcases List.mem_cons.mp member with rfl | below
    · simp
    · exact ih below
  | var _ _ _ _ _ ih => exact ih member
end Lamping.Lambda.Labelled

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

/-- Ordered actual atomic path residuals. These are auxiliary proof data
on two existing block lists, not fields of graphs or graph reductions. -/
inductive BetaAtomicBlockResiduals
    {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
    {kept : K → Graph.Label signature} {i : Nat}
    (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V)) (edge : BetaEdge site.net) :
    List (List (Endpoint site.reduce)) →List (List (Endpoint site.net)) →Prop where
  | nil : BetaAtomicBlockResiduals site edge [] []
  | cons {target old targets olds}
      (head : BetaPathResidual site edge (target.map (plugEnd _ _).invFun) old)
      (emptyWord : accessWord site.net old=[])
      (tail : BetaAtomicBlockResiduals site edge targets olds) :
      BetaAtomicBlockResiduals site edge (target::targets) (old::olds)

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))

/-- Equality of the actual target block lists is equivalent to equality of
their old lists. No flattening or direction reversal is performed. -/
theorem BetaAtomicBlockResiduals.equality_iff {edge : BetaEdge site.net}
    (geometry : SiteBetaGeometry site edge) {left right oldLeft oldRight}
    (first : BetaAtomicBlockResiduals site edge left oldLeft)
    (second : BetaAtomicBlockResiduals site edge right oldRight) :
    left=right ↔oldLeft=oldRight := by
  induction first generalizing right oldRight with
  | nil => cases second <;> simp
  | cons head empty tail ih =>
    cases second with
    | nil => simp
    | cons other otherEmpty rest =>
      have front := head.atomic_plugged_equality_iff site geometry other empty otherEmpty
      have heads := by
        simpa only [List.map_map,Function.comp_def,(plugEnd _ _).right_inv,List.map_id_fun',id_eq] using front
      simp only [List.cons.injEq,heads,ih rest]

private theorem block_residuals_of_origins
    {source target : LTerm} {ps : List Path} {labels : History ps source target}
    {edge : BetaEdge site.net} {root : B}
    (sourceSelection : OccurrenceFragmentSelection source site.net root)
    (targetSelection : OccurrenceFragmentSelection target site.reduce root)
    {edges oldEdges : List Path} (origins : BetaEdgeHistoryPreimages labels edges oldEdges) :
    ∀ (targetValid : ∀ p∈edges,(subtermAt target.erase p).isSome)
      (sourceValid : ∀ p∈oldEdges,(subtermAt source.erase p).isSome),
      (∀ p (inside : p∈edges) q (oldInside : q∈oldEdges),BetaNodeHistoryPreimage labels p q →
        BetaPathResidual site edge
          ((targetSelection ⟨p,targetValid p inside⟩).fragment.segments.map (plugEnd _ _).invFun)
          (sourceSelection ⟨q,sourceValid q oldInside⟩).fragment.segments) →
      BetaAtomicBlockResiduals site edge
        (edges.attach.map (fun p=>(targetSelection ⟨p.val,targetValid p.val p.property⟩).fragment.segments))
        (oldEdges.attach.map (fun p=>(sourceSelection ⟨p.val,sourceValid p.val p.property⟩).fragment.segments)) := by
  induction origins with
  | nil => intro _ _ _;exact .nil
  | @cons p q edges oldEdges origin tail ih =>
    intro targetValid sourceValid compare
    simp only [List.attach_cons,List.map_cons,List.map_map,Function.comp_def]
    apply BetaAtomicBlockResiduals.cons
      (compare p List.mem_cons_self q List.mem_cons_self origin)
      (sourceSelection ⟨q,sourceValid q List.mem_cons_self⟩).fragment.emptyWord
    exact ih
      (fun p inside=>targetValid p (List.mem_cons_of_mem _ inside))
      (fun q inside=>sourceValid q (List.mem_cons_of_mem _ inside))
      (fun p inside q oldInside trace=>compare p (List.mem_cons_of_mem _ inside)
        q (List.mem_cons_of_mem _ oldInside) trace)

private theorem reading_valid {target : LTerm} (chain : PrerequisiteChain target start edges)
    (inside : p∈edges) : (subtermAt target.erase p).isSome := by
  rcases chain.eligible inside with ⟨parent,stamp,fn,arg,equal,lookup⟩ | ⟨stamp,body,lookup⟩
  · have actual : target.subterm p=some fn := by
      rw [equal,LTerm.subterm_append,lookup];cases fn <;> rfl
    rw [←LTerm.erase_subterm,actual];rfl
  · rw [←LTerm.erase_subterm,lookup];rfl

/-- The SAME source chain carries both its incidence isomorphism and its
ordered actual physical residual blocks. This is the marker-free chain
case; no assertion about newly-created readings is made. -/
theorem PathSite.beta_marker_free_chain_images
    {root : B} {source target : LTerm} {ps F : List Path} {marked m n : Marked}
    {d : Path →Option Labelled.Label} {degree : Labelled.Label}
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
    (targetSelection : OccurrenceFragmentSelection target site.reduce root) :
    ∃ edge : BetaEdge site.net,SiteBetaGeometry site edge ∧
      ∀ {start edges} (chain : PrerequisiteChain target start edges),
        (∀ p∈edges,∀ node,target.subterm p=some node →
          node.label.OuterBarsSafe (fun payload=>payload≠degree)) →
        ∃ oldStart oldEdges,∃ oldChain : PrerequisiteChain source oldStart oldEdges,
          BetaNodeHistoryPreimage history start oldStart ∧
          BetaEdgeHistoryPreimages history edges oldEdges ∧
          ChainIncidenceIsomorphic (chainSyntaxIncidence target (history.closed closed) edges)
            (chainSyntaxIncidence source closed oldEdges) ∧
          BetaAtomicBlockResiduals site edge (canonicalChainImage targetSelection chain)
            (canonicalChainImage sourceSelection oldChain) := by
  obtain ⟨edge,geometry,allChildren⟩ := site.beta_uncreated_child_residuals closed matching inputs flow positive
    balance rootDepth transparency relative normal history old aligned selected
  refine ⟨edge,geometry,?_⟩
  intro start edges chain safe
  obtain ⟨oldStart,oldEdges,oldChain,startTrace,edgeTraces,_labels,_length,incidence⟩ :=
    old.marker_free_chain_incidence_preimages closed (history.closed closed) aligned history selected chain safe
  have targetValid : ∀ p∈edges,(subtermAt target.erase p).isSome := fun _ inside=>reading_valid chain inside
  have sourceValid : ∀ p∈oldEdges,(subtermAt source.erase p).isSome := fun _ inside=>reading_valid oldChain inside
  have compare : ∀ p (inside : p∈edges) q (oldInside : q∈oldEdges),
      BetaNodeHistoryPreimage history p q →
      BetaPathResidual site edge
        ((targetSelection ⟨p,targetValid p inside⟩).fragment.segments.map (plugEnd _ _).invFun)
        (sourceSelection ⟨q,sourceValid q oldInside⟩).fragment.segments := by
    intro p inside q oldInside desiredOrigin
    let child := targetSelection ⟨p,targetValid p inside⟩
    have markerFree := safe p inside child.term child.occurrence.lookup
    rcases child.occurrence.last_departure with ⟨empty,_external⟩ |
      ⟨parent,step,parentTerm,split,atParent,role⟩
    · exact False.elim (chain.reading_ne_nil inside empty)
    · have departure : SourceDeparture parentTerm step
          (sourceEdge child.environment child.context child.term).fromPort := by
        cases child.term <;> exact role
      change p=parent++[step] at split
      subst p
      obtain ⟨oldPosition,_oldNode,_oldLookup,origin,residual⟩ :=
        allChildren parent step parentTerm atParent child departure markerFree
      have same := origin.unique desiredOrigin
      subst oldPosition
      exact residual (sourceSelection ⟨q,sourceValid q oldInside⟩)
  have blocks := block_residuals_of_origins site sourceSelection targetSelection edgeTraces targetValid sourceValid compare
  exact ⟨oldStart,oldEdges,oldChain,startTrace,edgeTraces,incidence,blocks⟩

/-- REP's actual marker-free pair case. The two incidence isomorphisms
refer to the SAME old chains as the actual ordered physical block proofs. -/
theorem PathSite.beta_marker_free_rep
    {root : B} {source target : LTerm} {ps F : List Path} {marked m n : Marked}
    {d : Path →Option Labelled.Label} {degree : Labelled.Label}
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
    (targetSelection : OccurrenceFragmentSelection target site.reduce root)
    (sourceREP : ChainRepresentationInvariant closed sourceSelection)
    {p q left right} (first : PrerequisiteChain target p left) (second : PrerequisiteChain target q right)
    (leftSafe : ∀ e∈left,∀ node,target.subterm e=some node →
      node.label.OuterBarsSafe (fun payload=>payload≠degree))
    (rightSafe : ∀ e∈right,∀ node,target.subterm e=some node →
      node.label.OuterBarsSafe (fun payload=>payload≠degree)) :
    SameChainRepresentation targetSelection first second ↔
      ChainIncidenceIsomorphic (chainSyntaxIncidence target (history.closed closed) left)
        (chainSyntaxIncidence target (history.closed closed) right) := by
  obtain ⟨edge,geometry,images⟩ := site.beta_marker_free_chain_images closed matching inputs flow positive balance rootDepth
    transparency relative normal history old aligned selected sourceSelection targetSelection
  obtain ⟨_oldStart,leftEdges,leftChain,_leftStart,_leftOrigins,⟨leftIso⟩,leftBlocks⟩ := images first leftSafe
  obtain ⟨_oldOther,rightEdges,rightChain,_rightStart,_rightOrigins,⟨rightIso⟩,rightBlocks⟩ := images second rightSafe
  have sameBlocks : SameChainRepresentation targetSelection first second ↔
      SameChainRepresentation sourceSelection leftChain rightChain :=
    leftBlocks.equality_iff site geometry rightBlocks
  constructor
  · intro same
    obtain ⟨oldIso⟩ := (sourceREP leftChain rightChain).mp (sameBlocks.mp same)
    exact ⟨(leftIso.trans oldIso).trans rightIso.symm⟩
  · rintro ⟨targetIso⟩
    have oldSame := (sourceREP leftChain rightChain).mpr ⟨(leftIso.symm.trans targetIso).trans rightIso⟩
    exact sameBlocks.mpr oldSame
end
end Lamping.AG
