import Lamping.Lamping.BetaOriginalRootFold
import Lamping.Lamping.AdministrativeOriginalWordAccess
import Lamping.Lamping.LabelledProjectionSemantics
import Lamping.Lamping.ActualChainLabelConverse
import Lamping.Lamping.BetaChainEvaluatedResiduals

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Graph.Label signature}

private theorem administrative_fold_step
    (site : PathSite s kept (B:=B) (W:=W) (V:=V)) (notBeta : ∀i,s≠.beta i)
    {root : B} {source : LTerm} {directions : B→Bool}
    (flow : FlowBalance site.net directions) (positive : directions root=true)
    (sourceMatches : Matches site.net root source.erase) (targetMatches : Matches site.reduce root source.erase)
    (weights : Endpoint site.net→EdgeWord) (reverseLaw : OriginalWordReversal weights)
    (oldFold : OriginalRootFold site.net root source weights) :
    ∃next : Endpoint site.reduce→EdgeWord,OriginalWordReversal next ∧OriginalRootFold site.reduce root source next := by
  have sourceAt (target : RootAccess site.reduce root) :
      ∃old : RootAccess site.net root,accessWord site.net old.val=accessWord site.reduce target.val := by
    obtain ⟨f,corresponds,_⟩ := targetMatches
    obtain ⟨old,word,_⟩ := Matches.observation site.net sourceMatches (f target)
    exact ⟨old,word.trans (corresponds target).1.symm⟩
  have actionCase (action : IsAction s) :
      ∃next : Endpoint site.reduce→EdgeWord,OriginalWordReversal next ∧OriginalRootFold site.reduce root source next := by
    obtain ⟨principal⟩ := site.actionPrincipal_exists
    refine ⟨site.actionOriginalWordWeights action principal weights,
      site.action_original_word_reversal action principal weights reverseLaw,?_⟩
    intro target
    obtain ⟨old,word⟩ := sourceAt target
    obtain ⟨a,b,whole⟩ := target.property.1.1
    have physical := site.action_original_word_root_access action flow root positive sourceMatches principal
      old target word whole weights reverseLaw
    rw [←word]
    exact (oldFold old).trans (congrArg some physical.symm)
  have cancelCase (cancel : IsCancellation s) :
      ∃next : Endpoint site.reduce→EdgeWord,OriginalWordReversal next ∧OriginalRootFold site.reduce root source next := by
    obtain ⟨principal,all⟩ := site.cancellation_original_word_root_access cancel flow root positive targetMatches weights reverseLaw
    refine ⟨site.cancellationOriginalWordWeights principal weights,
      site.cancellation_original_word_reversal cancel principal weights reverseLaw,?_⟩
    intro target
    obtain ⟨old,word⟩ := sourceAt target
    have physical := all old target word
    rw [←word]
    exact (oldFold old).trans (congrArg some physical.symm)
  cases s with
  | beta i => exact False.elim (notBeta i rfl)
  | fanCancel i => exact cancelCase (.fan i)
  | croCancel i => exact cancelCase (.cro i)
  | braCancel i => exact cancelCase (.bra i)
  | fanAction f i j lt => exact actionCase (.fan f i j lt)
  | croAction f i j lt => exact actionCase (.cro f i j lt)
  | braAction f i j lt => exact actionCase (.bra f i j lt)
end

theorem LabelledGraphEvent.original_word_step
    {B : Type} [FiniteNames B] {s : Schema} {g h : ActualNet B} {root : B}
    {original source target : LTerm} {prior : List Path}
    {raw : ParallelHistory source.erase target.erase}
    (event : LabelledGraphEvent s g h root source target raw)
    (initial : INIT original) (prefixHistory : History prior original source)
    (closed : Closed source.erase)
    {directions : B→Bool} {heights : B→Int}
    (flow : FlowBalance g.net directions) (positive : directions root=true)
    (balance : IndexedLevelBalance g.net heights) (rootDepth : heights root=0)
    (inputs : RootInputs g.net root) (transparent : Transparency g.net root)
    (matching : Matches g.net root source.erase)
    (weights : Endpoint g.net→EdgeWord) (reverseLaw : OriginalWordReversal weights)
    (oldFold : OriginalRootFold g.net root source weights) :
    ∃ next : Endpoint h.net→EdgeWord,
      OriginalWordReversal next ∧ OriginalRootFold h.net root target next := by

  have targetMatching := event.target_matches flow positive balance rootDepth inputs transparent matching closed
  cases event with
  | auxiliary step notBeta =>
    cases step with
    | atSite kept site before after =>
      let localWeights := fun e=>weights (before.symm.ends e)
      have localReverse := before.original_word_reversal weights reverseLaw
      have localFold := before.original_root_fold weights oldFold
      obtain ⟨next,nextReverse,nextFold⟩ := administrative_fold_step site notBeta (before.flowBalance flow)
        positive (before.matches matching) (after.symm.matches targetMatching) localWeights localReverse localFold
      exact ⟨fun e=>next (after.symm.ends e),after.original_word_reversal next nextReverse,
        after.original_root_fold next nextFold⟩
  | beta kept site before after complete labels erased =>
    let localWeights := fun e=>weights (before.symm.ends e)
    have localReverse := before.original_word_reversal weights reverseLaw
    have localFold := before.original_root_fold weights oldFold
    have developed := (Marked.completeOld_iff _ _).mp complete
    obtain ⟨_localTarget,_localHistory,_sameErase,edge,_selection,_geometry,nextReverse,nextFold⟩ :=
      site.beta_original_word_root_access initial prefixHistory closed (before.matches matching)
        (before.rootInputs inputs) (before.flowBalance flow) positive (before.indexed_balance balance)
        rootDepth (before.transparency transparent) developed.1 developed.2 labels localWeights localReverse localFold
    let next := site.betaOriginalWordWeights edge localWeights
    exact ⟨fun e=>next (after.symm.ends e),after.original_word_reversal next nextReverse,
      after.original_root_fold next nextFold⟩

theorem LabelledGraphProjection.original_word_worker
    {B : Type} [FiniteNames B] {g h : ActualNet B} {root : B}
    {schemas : List Schema} {original source target : LTerm} {prior : List Path}
    {raw : ParallelHistory source.erase target.erase}
    (actual : LabelledGraphProjection g h root schemas source target raw)
    (initial : INIT original) (prefixHistory : History prior original source)
    (closed : Closed source.erase)
    {directions : B→Bool} {heights : B→Int}
    (flow : FlowBalance g.net directions) (positive : directions root=true)
    (balance : IndexedLevelBalance g.net heights) (rootDepth : heights root=0)
    (inputs : RootInputs g.net root) (transparent : Transparency g.net root)
    (matching : Matches g.net root source.erase)
    (weights : Endpoint g.net→EdgeWord) (reverseLaw : OriginalWordReversal weights)
    (oldFold : OriginalRootFold g.net root source weights) :
    ∃ next : Endpoint h.net→EdgeWord,
      OriginalWordReversal next ∧ OriginalRootFold h.net root target next := by

  induction actual generalizing original prior with
  | iso same => exact ⟨fun e=>weights (same.symm.ends e),same.original_word_reversal weights reverseLaw,
      same.original_root_fold weights oldFold⟩
  | cons event tail ih =>
    have step := event.graph_step
    have nextMatching := event.target_matches flow positive balance rootDepth inputs transparent matching closed
    have nextInputs := step.rootInputs flow positive balance rootDepth inputs transparent matching
    obtain ⟨nextFlow⟩ := step.flowBalance flow
    obtain ⟨nextBalance⟩ := step.indexed_balance balance
    have nextTransparent := step.transparency_indexed flow positive balance rootDepth transparent
    obtain ⟨next,nextReverse,nextFold⟩ := event.original_word_step initial prefixHistory closed flow positive balance
      rootDepth inputs transparent matching weights reverseLaw oldFold
    exact ih initial (prefixHistory.append event.label_history) (event.label_history.closed closed)
      nextFlow positive nextBalance rootDepth nextInputs nextTransparent nextMatching next nextReverse nextFold

theorem LabelledGraphProjection.original_word_weights
    {original current : LTerm} (initial : INIT original) (closed : Closed original.erase)
    {graph : ActualNet (Boundary original.erase)} {schemas : List Schema}
    {raw : ParallelHistory original.erase current.erase}
    (actual : LabelledGraphProjection (ActualNet.initial original.erase)
      graph (.inl ()) schemas original current raw) :
    ∃ weights : Endpoint graph.net→EdgeWord,
      OriginalWordReversal weights ∧ OriginalRootFold graph.net (.inl ()) current weights := by

  obtain ⟨addr⟩ := encode_addressing original.erase 0
  obtain ⟨flow⟩ := encode_flowBalance original.erase 0
  obtain ⟨balance⟩ := encode_indexed_balance original.erase 0
  exact actual.original_word_worker initial (.nil original) closed flow rfl balance rfl
    (encode_closed_independence original.erase closed 0).rootInputs
    (encode_closed_transparency original.erase closed 0) (encode_closed_matches original.erase closed 0)
    (initialOriginalWeights original 0 addr)
    (symmetrizedOriginalWord_reversal _ (initialOriginalEntry original 0 addr))
    (initial_original_root_fold original closed 0 addr)

theorem OriginalRootFold.fragment_label_eq
    {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {net : Net signature N B W} {root : B}
    {original current : LTerm} {prior : List Path}
    (initial : INIT original) (labels : History prior original current)
    (matching : Matches net root current.erase)
    (weights : Endpoint net→EdgeWord)
    (constructed : OriginalRootFold net root current weights)
    {p q : Path} (left : OccurrenceFragment current net root p)
    (right : OccurrenceFragment current net root q)
    (physical : left.fragment.segments=right.fragment.segments) :
    left.term.label=right.term.label := by

  have leftFold := left.original_word_of_root_fold matching weights constructed
  have rightFold := right.original_word_of_root_fold matching weights constructed
  have words := leftFold.symm.trans ((congrArg (physicalOriginalWord weights) physical).trans rightFold)
  exact labels.generated_label_path_injective labels initial
    (LTerm.label_mem_of_subterm left.occurrence.lookup) (LTerm.label_mem_of_subterm right.occurrence.lookup) words

theorem OriginalRootFold.chain_label_vector
    {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {net : Net signature N B W} {root : B}
    {original current : LTerm} {prior : List Path}
    (initial : INIT original) (labels : History prior original current)
    (matching : Matches net root current.erase)
    (weights : Endpoint net→EdgeWord)
    (constructed : OriginalRootFold net root current weights)
    (selection : OccurrenceFragmentSelection current net root)
    {p q : Path} {es fs : List Path}
    (first : PrerequisiteChain current p es) (second : PrerequisiteChain current q fs)
    (physical : SameChainRepresentation selection first second) :
    es.map current.labelAt=fs.map current.labelAt := by

  have lengths := congrArg List.length physical
  change (canonicalChainImage selection first).length=(canonicalChainImage selection second).length at lengths
  rw [canonicalChainImage_length,canonicalChainImage_length] at lengths
  apply List.ext_getElem (by simpa only [List.length_map] using lengths)
  intro n leftBound rightBound
  have lb : n<es.length := by simpa only [List.length_map] using leftBound
  have rb : n<fs.length := by simpa only [List.length_map] using rightBound
  let lm : {p : Path //p∈es} := ⟨es[n],List.mem_iff_getElem.mpr ⟨n,lb,rfl⟩⟩
  let rm : {p : Path //p∈fs} := ⟨fs[n],List.mem_iff_getElem.mpr ⟨n,rb,rfl⟩⟩
  let lp := actualChainPosition first lm
  let rp := actualChainPosition second rm
  have ls : es[n]?=some lp.val := by rw [List.getElem?_eq_getElem lb];rfl
  have rs : fs[n]?=some rp.val := by rw [List.getElem?_eq_getElem rb];rfl
  have pieces := same_chain_representation_slot selection first second physical lp rp ls rs
  have stamps := OriginalRootFold.fragment_label_eq initial labels matching weights constructed
    (selection lp) (selection rp) pieces
  simp only [List.getElem_map]
  change current.labelAt lp.val=current.labelAt rp.val
  simp only [LTerm.labelAt,(selection lp).occurrence.lookup,(selection rp).occurrence.lookup,Option.map_some,stamps]

theorem OriginalRootFold.chain_representation_inverse
    {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {net : Net signature N B W} {root : B}
    {original current : LTerm} {prior : List Path}
    (initial : INIT original) (labels : History prior original current)
    (closed : Closed current.erase) (matching : Matches net root current.erase)
    (weights : Endpoint net→EdgeWord)
    (constructed : OriginalRootFold net root current weights)
    (selection : OccurrenceFragmentSelection current net root)
    {p q : Path} {es fs : List Path}
    (first : PrerequisiteChain current p es) (second : PrerequisiteChain current q fs)
    (physical : SameChainRepresentation selection first second) :
    ChainIncidenceIsomorphic (chainSyntaxIncidence current closed es)
      (chainSyntaxIncidence current closed fs) := by

  exact actual_chain_iso_of_labels labels initial closed first second
    (OriginalRootFold.chain_label_vector initial labels matching weights constructed selection first second physical)

theorem LabelledGraphProjection.actual_fragment_label_reflection
    {original current : LTerm} (initial : INIT original) (closed : Closed original.erase)
    {graph : ActualNet (Boundary original.erase)} {schemas : List Schema}
    {raw : ParallelHistory original.erase current.erase}
    (actual : LabelledGraphProjection (ActualNet.initial original.erase)
      graph (.inl ()) schemas original current raw)
    {p q : Path} (left : OccurrenceFragment current graph.net (.inl ()) p)
    (right : OccurrenceFragment current graph.net (.inl ()) q)
    (physical : left.fragment.segments=right.fragment.segments) :
    left.term.label=right.term.label := by

  obtain ⟨weights,_reverse,fold⟩ := actual.original_word_weights initial closed
  obtain ⟨flow⟩ := encode_flowBalance original.erase 0
  obtain ⟨balance⟩ := encode_indexed_balance original.erase 0
  have matching := (actual.target_matches flow rfl balance rfl
    (encode_closed_independence original.erase closed 0).rootInputs
    (encode_closed_transparency original.erase closed 0) (encode_closed_matches original.erase closed 0) closed).2
  exact OriginalRootFold.fragment_label_eq initial actual.label_history matching weights fold left right physical

theorem LabelledGraphProjection.actual_chain_representation_inverse
    {original current : LTerm} (initial : INIT original) (closed : Closed original.erase)
    {graph : ActualNet (Boundary original.erase)} {schemas : List Schema}
    {raw : ParallelHistory original.erase current.erase}
    (actual : LabelledGraphProjection (ActualNet.initial original.erase)
      graph (.inl ()) schemas original current raw)
    (selection : OccurrenceFragmentSelection current graph.net (.inl ()))
    {p q : Path} {es fs : List Path}
    (first : PrerequisiteChain current p es) (second : PrerequisiteChain current q fs)
    (physical : SameChainRepresentation selection first second) :
    ChainIncidenceIsomorphic
      (chainSyntaxIncidence current (actual.label_history.closed closed) es)
      (chainSyntaxIncidence current (actual.label_history.closed closed) fs) := by

  obtain ⟨weights,_reverse,fold⟩ := actual.original_word_weights initial closed
  obtain ⟨flow⟩ := encode_flowBalance original.erase 0
  obtain ⟨balance⟩ := encode_indexed_balance original.erase 0
  have matching := (actual.target_matches flow rfl balance rfl
    (encode_closed_independence original.erase closed 0).rootInputs
    (encode_closed_transparency original.erase closed 0) (encode_closed_matches original.erase closed 0) closed).2
  exact OriginalRootFold.chain_representation_inverse initial actual.label_history (actual.label_history.closed closed)
    matching weights fold selection first second physical

theorem GraphTrace.original_weighted_projection
    {original : LTerm} (initial : INIT original) (closed : Closed original.erase)
    {graph : ActualNet (Boundary original.erase)} {schemas : List Schema}
    (trace : GraphTrace (ActualNet.initial original.erase) graph schemas) :
    ∃ current,∃ raw : ParallelHistory original.erase current.erase,
      ∃ _actual : LabelledGraphProjection (ActualNet.initial original.erase)
        graph (.inl ()) schemas original current raw,
      ∃ weights : Endpoint graph.net→EdgeWord,
        OriginalWordReversal weights ∧ OriginalRootFold graph.net (.inl ()) current weights := by

  obtain ⟨current,raw,actual,_labels,_inputs,_matching⟩ := initial_labelled_trace_projection original closed graph schemas trace
  obtain ⟨weights,reverse,fold⟩ := actual.original_word_weights initial closed
  exact ⟨current,raw,actual,weights,reverse,fold⟩

#print axioms LabelledGraphEvent.original_word_step
#print axioms LabelledGraphProjection.original_word_worker
#print axioms LabelledGraphProjection.original_word_weights
#print axioms OriginalRootFold.fragment_label_eq
#print axioms OriginalRootFold.chain_label_vector
#print axioms OriginalRootFold.chain_representation_inverse
#print axioms LabelledGraphProjection.actual_fragment_label_reflection
#print axioms LabelledGraphProjection.actual_chain_representation_inverse
#print axioms GraphTrace.original_weighted_projection
end Lamping.AG
