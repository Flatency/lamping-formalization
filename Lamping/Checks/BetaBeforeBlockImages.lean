import Lamping.Lamping.BetaBeforeBlockImages
import Lamping.Checks.FunctionWrappedReachable
namespace Lamping.Checks.BetaBeforeBlockImagesChecks
open AG Graph Lambda Lambda.Labelled
abbrev source : LTerm := WrappedSuccessfulChains.original
abbrev target : LTerm := WrappedSuccessfulChains.current
noncomputable abbrev site := FunctionWrappedReachable.concrete.site
abbrev functionTerm : LTerm := .lam WrappedSuccessfulChains.functionLabel
  (.app (.atom 5) (.var (.atom 6) 0) (.lam (.atom 7) (.var (.atom 8) 0)))
def targetChain : PrerequisiteChain target [.arg] [[.arg],[.fn]] :=
  .lam (parent:=[]) (step:=.arg) rfl (by decide) (.redex_app rfl)
def sourceChain : PrerequisiteChain source [.arg] [[.arg],[.fn],[.fn,.fn]] :=
  .lam (parent:=[]) (step:=.arg) rfl (by decide)
    (.app rfl (by intro l b same;cases same) (.redex_app rfl))
def old : Marked.RelativeOldHistory [[.fn]] [[.fn]] (Marked.mark [[.fn]] source.erase)
    FunctionWrappedReachable.endpoint :=
  .cons (.appL (.redRoot _ _ _)) (by decide) (.nil _)
theorem selected (name : Path) (inside : name∈([[.fn]] : List Path)) :
    source.degreeAt name=some (.atom 2) := by
  have same := List.mem_singleton.mp inside
  subst name;rfl
theorem marked : ¬functionTerm.label.OuterBarsSafe (fun x=>x≠Label.atom 2) := by
  obtain ⟨beta,body,argument,redex⟩ := LTerm.degreeAt_redex
    (by rfl : source.degreeAt [.fn]=some (.atom 2))
  exact WrappedSuccessfulChains.actualStep.created_label_not_safe redex
    (by rfl : target.subterm [.fn]=some functionTerm) (Or.inl rfl)
theorem beforeSafe : ∀p∈([[.arg]] : List Path),∀node,target.subterm p=some node →
    node.label.OuterBarsSafe (fun x=>x≠Label.atom 2) := by
  intro p member node lookup
  have same := List.mem_singleton.mp member
  subst p
  have same : node=.lam (.atom 9) (.var (.atom 10) 0) := Option.some.inj lookup.symm
  subst node;trivial

theorem actual_nonempty_before_images
    (sourceSelection : OccurrenceFragmentSelection source site.net (.inl ()))
    (targetSelection : OccurrenceFragmentSelection target site.reduce (.inl ())) :
    ∃edge : BetaEdge site.net,SiteBetaGeometry site edge ∧
      BetaNodeHistoryPreimage WrappedSuccessfulChains.actualHistory [.arg] [.arg] ∧
      BetaEdgeHistoryPreimages WrappedSuccessfulChains.actualHistory [[.arg]] [[.arg]] ∧
      BetaAtomicBlockResiduals site edge
        ((canonicalChainImage targetSelection targetChain).take 1)
        ((canonicalChainImage sourceSelection sourceChain).take 1) ∧
      ((canonicalChainImage targetSelection targetChain).take 1).length=1 := by
  have matching := FunctionWrappedReachable.concrete.sourceIso.matches
    (encode_closed_matches FunctionWrappedReachable.term FunctionWrappedReachable.closed 0)
  have inputs := FunctionWrappedReachable.concrete.sourceIso.rootInputs
    (encode_closed_independence FunctionWrappedReachable.term FunctionWrappedReachable.closed 0).rootInputs
  obtain ⟨originalFlow⟩ := encode_flowBalance FunctionWrappedReachable.term 0
  have flow := FunctionWrappedReachable.concrete.sourceIso.flowBalance originalFlow
  obtain ⟨originalBalance⟩ := encode_indexed_balance FunctionWrappedReachable.term 0
  have balance := FunctionWrappedReachable.concrete.sourceIso.indexed_balance originalBalance
  have transparency := FunctionWrappedReachable.concrete.sourceIso.transparency
    (encode_closed_transparency FunctionWrappedReachable.term FunctionWrappedReachable.closed 0)
  obtain ⟨edge,geometry,s,sb,r,f,name,node,marker,rest,forward,_chosen,_atNode,_safe,
    oldChain,_prefix,_reads,_labels,_marker,_word,startTrace,origins,images⟩ :=
    site.beta_before_block_images WrappedSuccessfulChains.sourceClosed matching inputs flow rfl balance rfl
      transparency FunctionWrappedReachable.relative
      (by simp [FunctionWrappedReachable.endpoint,Marked.Normal]) WrappedSuccessfulChains.actualHistory
      old selected (WrappedSuccessfulChains.initial.outerBarsSafe _) sourceSelection targetSelection
      targetChain (before:=[[.arg]]) (chosen:=[.fn]) (after:=[]) rfl
      (by rfl : target.subterm [.fn]=some functionTerm) marked beforeSafe
  have untouched : BetaNodeHistoryPreimage WrappedSuccessfulChains.actualHistory [.arg] [.arg] :=
    .one (step:=WrappedSuccessfulChains.actualStep) (by rfl)
      (.context (by rintro ⟨suffix,same⟩;cases same)) (.nil _ _)
  have sameStart := startTrace.unique untouched
  subst s
  cases origins with
  | cons edgeTrace tail =>
    cases tail
    have sameSlot := edgeTrace.unique untouched
    subst_vars
    have nameEq : name=[.fn] := List.mem_singleton.mp _chosen
    subst name
    have sameEdges := oldChain.unique sourceChain
    have firstEq : f=[.fn] := by
      have atFirst := congrArg (fun xs : List Path=>xs[1]?) sameEdges
      exact Option.some.inj atFirst
    subst f
    have sameImages := canonicalChainImage_same_edges sourceSelection oldChain sourceChain
    rw [sameImages] at images
    refine ⟨edge,geometry,startTrace,.cons edgeTrace .nil,images,?_⟩
    simp only [List.length_take,canonicalChainImage_length]
    rfl
/-- Actual matching supplies both selectors; no target-selector or successful
image witness is an oracle at this closed instance. -/
theorem actual_nonempty_instance :
    ∃sourceSelection : OccurrenceFragmentSelection source site.net (.inl ()),
      ∃targetSelection : OccurrenceFragmentSelection target site.reduce (.inl ()),
        ∃edge : BetaEdge site.net,SiteBetaGeometry site edge ∧
          BetaAtomicBlockResiduals site edge
            ((canonicalChainImage targetSelection targetChain).take 1)
            ((canonicalChainImage sourceSelection sourceChain).take 1) ∧
          ((canonicalChainImage targetSelection targetChain).take 1).length=1 := by
  have matching := FunctionWrappedReachable.concrete.sourceIso.matches
    (encode_closed_matches FunctionWrappedReachable.term FunctionWrappedReachable.closed 0)
  obtain ⟨sourceSelection⟩ := matching.occurrence_fragment_selection WrappedSuccessfulChains.sourceClosed
  obtain ⟨targetSelection⟩ := FunctionWrappedReachable.beta_matches.occurrence_fragment_selection
    WrappedSuccessfulChains.targetClosed
  obtain ⟨edge,geometry,_start,_slots,images,nonempty⟩ :=
    actual_nonempty_before_images sourceSelection targetSelection
  exact ⟨sourceSelection,targetSelection,edge,geometry,images,nonempty⟩

#print axioms targetChain
#print axioms sourceChain
#print axioms actual_nonempty_before_images
#print axioms actual_nonempty_instance
end Lamping.Checks.BetaBeforeBlockImagesChecks
