import Lamping.Lamping.GenericOriginalWordTrace
import Lamping.Lamping.NonBetaJointRepresentation
import Lamping.Lamping.LabelledBetaEventAuxiliary
import Lamping.Lamping.WholeChainForward
import Lamping.Lamping.ConditionalFamilyTraceProjection
import Lamping.Lamping.InitialJointRepresentation
import Lamping.Lamping.ObservableFamilyEvent

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

theorem PathSite.beta_empty_chain_representation_preserve
    {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
    {kept : K→Graph.Label signature} {i : Nat}
    (site : PathSite (.beta i) kept (B := B) (W := W) (V := V))
    {root : B} {source target : LTerm} {ps : List Path} {marked : Marked}
    (closed : Closed source.erase) (matching : Matches site.net root source.erase)
    (inputs : RootInputs site.net root)
    {directions : B→Bool} (flow : FlowBalance site.net directions) (positive : directions root=true)
    {heights : B→Int} (balance : IndexedLevelBalance site.net heights) (rootDepth : heights root=0)
    (transparent : Transparency site.net root)
    (relative : Marked.RelativeHistory ps
      (Marked.mark (site.betaSyntaxFiber root source.erase) source.erase) marked)
    (normal : Marked.Normal marked) (labels : History ps source target)
    (sourceSelection : OccurrenceFragmentSelection source site.net root)
    (targetSelection : OccurrenceFragmentSelection target site.reduce root)
    (sourceREP : ChainRepresentationInvariant closed sourceSelection)
    (empty : site.betaSyntaxFiber root source.erase=[]) :
    ChainRepresentationInvariant (labels.closed closed) targetSelection := by

  have complete := (Marked.completeOld_iff (site.betaSyntaxFiber root source.erase) source.erase).mpr ⟨relative,normal⟩
  have noSteps := (physicalBetaFiber_complete_empty complete empty).1
  cases noSteps
  cases labels
  obtain ⟨localTarget,localHistory,_erase,_targetMatching,physical,localSelection,geometry,all⟩ :=
    site.beta_evaluated_child_residuals closed matching inputs flow positive balance rootDepth transparent
      relative normal (.nil source)
  cases localHistory
  have localMatching : Matches site.net root (initLabels source.erase).erase := by
    simpa only [erase_initLabels] using matching
  have evaluated {start : Path} {edges : List Path} (chain : PrerequisiteChain source start edges)
      (member : {p : Path //p∈edges}) :
      BetaPathResidual site physical
        ((targetSelection (actualChainPosition chain member)).fragment.segments.map (plugEnd _ _).invFun)
        (sourceSelection (actualChainPosition chain member)).fragment.segments := by
    rcases member with ⟨path,inside⟩
    let position := actualChainPosition chain ⟨path,inside⟩
    let fragment := targetSelection position
    rcases fragment.occurrence.last_departure with ⟨rootAt,_⟩ |
      ⟨parent,step,parentTerm,split,atParent,role⟩
    · exact False.elim (chain.reading_ne_nil inside rootAt)
    · change path=parent++[step] at split
      subst path
      have departure : SourceDeparture parentTerm step
          (sourceEdge fragment.environment fragment.context fragment.term).fromPort := by
        cases fragment.term <;> exact role
      obtain ⟨localNode,lookup,_sameErase,_nonempty,residual⟩ := all parent step parentTerm atParent fragment departure
      obtain ⟨env,ctx,occurrence⟩ := SourceSubterm.of_lookup (initLabels source.erase) lookup [] .external
      have equation := localSelection.evalLabel_occurrence_segments (init_is_INIT source.erase)
        localMatching matching occurrence (sourceSelection position) physical
      rw [equation] at residual
      exact residual
  have blocks {start : Path} {edges : List Path} (chain : PrerequisiteChain source start edges) :
      BetaAtomicBlockResiduals site physical (canonicalChainImage targetSelection chain)
        (canonicalChainImage sourceSelection chain) := by
    have go (members : List {p : Path //p∈edges}) :
        BetaAtomicBlockResiduals site physical
          (members.map (fun m=>(targetSelection (actualChainPosition chain m)).fragment.segments))
          (members.map (fun m=>(sourceSelection (actualChainPosition chain m)).fragment.segments)) := by
      induction members with
      | nil => exact .nil
      | cons member rest ih =>
        exact .cons (evaluated chain member) (sourceSelection (actualChainPosition chain member)).fragment.emptyWord ih
    exact go edges.attach
  intro p q es fs first second
  have compared := (blocks first).equality_iff site geometry (blocks second)
  exact compared.trans (sourceREP first second)

private theorem event_joint_from_constructed_target_fold
    {B : Type} [FiniteNames B] {s : Schema} {g h : ActualNet B} {root : B}
    {original source target : LTerm} {raw : ParallelHistory source.erase target.erase}
    (event : LabelledGraphEvent s g h root source target raw)
    (initial : INIT original) (closed : Closed source.erase)
    (prior : ParallelHistory original.erase source.erase)
    (prefixHistory : History prior.derivation.paths original source) (completePrior : CompleteDerivation prior)
    {directions : B→Bool} {heights : B→Int}
    (flow : FlowBalance g.net directions) (positive : directions root=true)
    (balance : IndexedLevelBalance g.net heights) (rootDepth : heights root=0)
    (inputs : RootInputs g.net root) (transparent : Transparency g.net root)
    (matching : Matches g.net root source.erase)
    (sourceSelection : OccurrenceFragmentSelection source g.net root)
    (sourceJoint : JointRepresentation closed sourceSelection)
    (targetSelection : OccurrenceFragmentSelection target h.net root)
    (targetMatching : Matches h.net root target.erase)
    (targetWeights : Endpoint h.net→EdgeWord) (targetFold : OriginalRootFold h.net root target targetWeights) :
    JointRepresentation (event.label_history.closed closed) targetSelection := by
  cases event with
  | auxiliary step notBeta =>
    exact step.nonbeta_joint_representation_preserve notBeta flow root positive balance rootDepth
      inputs transparent closed matching sourceSelection targetSelection sourceJoint
  | beta kept site before after complete labels erased =>
    let betaEvent := LabelledGraphEvent.beta kept site before after complete labels erased
    have auxiliary := betaEvent.beta_auxiliary_preserve initial prior completePrior prefixHistory closed
      flow positive balance rootDepth inputs transparent matching sourceSelection targetSelection sourceJoint
    have localMatching := before.matches matching
    have localTargetMatching := after.symm.matches targetMatching
    obtain ⟨localSource⟩ := localMatching.occurrence_fragment_selection closed
    obtain ⟨localTarget⟩ := localTargetMatching.occurrence_fragment_selection (labels.closed closed)
    have localJoint := (before.joint_representation matching closed sourceSelection localSource).mpr sourceJoint
    obtain ⟨relative,normal⟩ := (Marked.completeOld_iff _ _).mp complete
    refine ⟨?_,auxiliary⟩
    intro p q es fs first second
    constructor
    · intro physical
      exact OriginalRootFold.chain_representation_inverse initial (prefixHistory.append labels)
        (labels.closed closed) targetMatching targetWeights targetFold targetSelection first second physical
    · rintro ⟨iso⟩
      apply (after.chain_representation localTargetMatching localTarget targetSelection first second).mpr
      by_cases empty : site.betaSyntaxFiber root source.erase=[]
      · exact (site.beta_empty_chain_representation_preserve closed localMatching (before.rootInputs inputs)
          (before.flowBalance flow) positive (before.indexed_balance balance) rootDepth
          (before.transparency transparent) relative normal labels localSource localTarget localJoint.1 empty
          first second).mpr ⟨iso⟩
      · have existsMember : ∃name,name∈site.betaSyntaxFiber root source.erase := by
          cases eq : site.betaSyntaxFiber root source.erase with
          | nil => exact False.elim (empty eq)
          | cons name rest => exact ⟨name,List.mem_cons_self⟩
        obtain ⟨name,member⟩ := existsMember
        obtain ⟨representative,_access,same,_app,_lam⟩ :=
          (mem_physicalBetaFiberPaths site.net root source.erase (.inr (.inl ())) (.inr (.inr ())) name).mp member
        have chosen : representative.val∈site.betaSyntaxFiber root source.erase := same.symm ▸ member
        obtain ⟨degree,atDegree⟩ := degreeAt_exists source representative
        have selected (other : Path) (inside : other∈site.betaSyntaxFiber root source.erase) :
            source.degreeAt other=some degree := by
          obtain ⟨candidate,_candidateAccess,candidateSame,_atApp,_atLam⟩ :=
            (mem_physicalBetaFiberPaths site.net root source.erase (.inr (.inl ())) (.inr (.inr ())) other).mp inside
          have candidateChosen : candidate.val∈site.betaSyntaxFiber root source.erase := candidateSame.symm ▸ inside
          have degreeEq := (site.beta_fiber_iff_degree closed localMatching localSource localJoint.1
            representative chosen candidate).mp candidateChosen
          rw [candidateSame] at degreeEq
          exact degreeEq.trans atDegree
        have safe := complete_prefix_outer_bars_fresh initial prior completePrior prefixHistory representative atDegree
        have old := (Marked.relativeOld_iff_relative
          (Marked.selected_mark (site.betaSyntaxFiber root source.erase) source.erase)).mpr relative
        exact site.beta_chain_forward closed localMatching (before.rootInputs inputs) (before.flowBalance flow)
          positive (before.indexed_balance balance) rootDepth (before.transparency transparent)
          relative normal labels initial prefixHistory old selected safe localSource localJoint localTarget first second iso

theorem LabelledGraphProjection.joint_source_rep_worker
    {B : Type} [FiniteNames B] {g h : ActualNet B} {root : B} {schemas : List Schema}
    {original source target : LTerm} {raw : ParallelHistory source.erase target.erase}
    (actual : LabelledGraphProjection g h root schemas source target raw)
    (initial : INIT original) (closed : Closed source.erase)
    (prior : ParallelHistory original.erase source.erase)
    (prefixHistory : History prior.derivation.paths original source)
    (completePrior : CompleteDerivation prior)
    {directions : B→Bool} {heights : B→Int}
    (flow : FlowBalance g.net directions) (positive : directions root=true)
    (balance : IndexedLevelBalance g.net heights) (rootDepth : heights root=0)
    (inputs : RootInputs g.net root) (transparent : Transparency g.net root)
    (matching : Matches g.net root source.erase)
    (weights : Endpoint g.net→EdgeWord) (reverseLaw : OriginalWordReversal weights)
    (oldFold : OriginalRootFold g.net root source weights)
    (selection : OccurrenceFragmentSelection source g.net root)
    (sourceJoint : JointRepresentation closed selection) :
    (∃ finalSelection : OccurrenceFragmentSelection target h.net root,
      JointRepresentation (actual.label_history.closed closed) finalSelection) ∧
      actual.SourceChainREP := by

  induction actual generalizing original with
  | iso same =>
    obtain ⟨finalSelection⟩ := (same.matches matching).occurrence_fragment_selection closed
    exact ⟨⟨finalSelection,(same.joint_representation matching closed selection finalSelection).mpr sourceJoint⟩,.iso same⟩
  | cons event tail ih =>
    have step := event.graph_step
    have nextClosed := event.label_history.closed closed
    have nextMatching := event.target_matches flow positive balance rootDepth inputs transparent matching closed
    have nextInputs := step.rootInputs flow positive balance rootDepth inputs transparent matching
    obtain ⟨nextFlow⟩ := step.flowBalance flow
    obtain ⟨nextBalance⟩ := step.indexed_balance balance
    have nextTransparent := step.transparency_indexed flow positive balance rootDepth transparent
    obtain ⟨nextWeights,nextReverse,nextFold⟩ := event.original_word_step initial prefixHistory closed flow positive
      balance rootDepth inputs transparent matching weights reverseLaw oldFold
    obtain ⟨nextSelection⟩ := nextMatching.occurrence_fragment_selection nextClosed
    have nextJoint := event_joint_from_constructed_target_fold event initial closed prior prefixHistory completePrior
      flow positive balance rootDepth inputs transparent matching selection sourceJoint nextSelection nextMatching nextWeights nextFold
    obtain ⟨observed,_observable,sameDerivation,_permutation,nextComplete⟩ :=
      event.observable_complete_extension initial closed prior prefixHistory completePrior matching selection sourceJoint.1
    have observedLabels := event.label_history
    rw [sameDerivation] at observedLabels
    have nextHistory := prefixHistory.append observedLabels
    obtain ⟨finalJoint,tailREP⟩ := ih initial nextClosed (prior.append observed)
      (by simpa only [ParallelHistory.derivation_append,Derivation.append] using nextHistory) nextComplete
      nextFlow positive nextBalance rootDepth nextInputs nextTransparent nextMatching nextWeights nextReverse nextFold nextSelection nextJoint
    exact ⟨finalJoint,.cons (event := event) closed selection sourceJoint.1 tailREP⟩

private theorem initial_joint_worker
    {original current : LTerm} (initial : INIT original) (closed : Closed original.erase)
    {graph : ActualNet (Boundary original.erase)} {schemas : List Schema}
    {raw : ParallelHistory original.erase current.erase}
    (actual : LabelledGraphProjection (ActualNet.initial original.erase) graph (.inl ()) schemas original current raw) :
    (∃selection : OccurrenceFragmentSelection current graph.net (.inl ()),
      JointRepresentation (actual.label_history.closed closed) selection) ∧actual.SourceChainREP := by
  obtain ⟨addr⟩ := encode_addressing original.erase 0
  obtain ⟨flow⟩ := encode_flowBalance original.erase 0
  obtain ⟨balance⟩ := encode_indexed_balance original.erase 0
  have matching := encode_closed_matches original.erase closed 0
  obtain ⟨selection⟩ := matching.occurrence_fragment_selection closed
  exact actual.joint_source_rep_worker initial closed (.nil original.erase) (.nil original) (.nil original.erase)
    flow rfl balance rfl (encode_closed_independence original.erase closed 0).rootInputs
    (encode_closed_transparency original.erase closed 0) matching (initialOriginalWeights original 0 addr)
    (symmetrizedOriginalWord_reversal _ (initialOriginalEntry original 0 addr))
    (initial_original_root_fold original closed 0 addr) selection
    (encode_initial_joint_representation original closed initial 0 selection)

theorem LabelledGraphProjection.initial_joint_representation
    {original current : LTerm} (initial : INIT original) (closed : Closed original.erase)
    {graph : ActualNet (Boundary original.erase)} {schemas : List Schema}
    {raw : ParallelHistory original.erase current.erase}
    (actual : LabelledGraphProjection (ActualNet.initial original.erase)
      graph (.inl ()) schemas original current raw)
    (selection : OccurrenceFragmentSelection current graph.net (.inl ())) :
    JointRepresentation (actual.label_history.closed closed) selection := by
  obtain ⟨⟨finalSelection,finalJoint⟩,_sourceREP⟩ := initial_joint_worker initial closed actual
  obtain ⟨flow⟩ := encode_flowBalance original.erase 0
  obtain ⟨balance⟩ := encode_indexed_balance original.erase 0
  have matching := (actual.target_matches flow rfl balance rfl
    (encode_closed_independence original.erase closed 0).rootInputs
    (encode_closed_transparency original.erase closed 0) (encode_closed_matches original.erase closed 0) closed).2
  exact (JointRepresentation.choice_independent matching (actual.label_history.closed closed) finalSelection selection).mp finalJoint

theorem LabelledGraphProjection.initial_source_chain_rep
    {original current : LTerm} (initial : INIT original) (closed : Closed original.erase)
    {graph : ActualNet (Boundary original.erase)} {schemas : List Schema}
    {raw : ParallelHistory original.erase current.erase}
    (actual : LabelledGraphProjection (ActualNet.initial original.erase)
      graph (.inl ()) schemas original current raw) : actual.SourceChainREP := by
  exact (initial_joint_worker initial closed actual).2

theorem LabelledGraphProjection.complete_family_projection
    {original current : LTerm} (initial : INIT original) (closed : Closed original.erase)
    {graph : ActualNet (Boundary original.erase)} {schemas : List Schema}
    {raw : ParallelHistory original.erase current.erase}
    (actual : LabelledGraphProjection (ActualNet.initial original.erase)
      graph (.inl ()) schemas original current raw) :
    ∃ observed : ParallelHistory original.erase current.erase,
      ParallelHistory.Observable observed ∧ raw.derivation=observed.derivation ∧
      PermEq raw observed ∧ History observed.derivation.paths original current ∧
      CompleteDerivation observed ∧ RootInputs graph.net (.inl ()) ∧
      Matches graph.net (.inl ()) current.erase := by
  have represented := actual.initial_source_chain_rep initial closed
  obtain ⟨flow⟩ := encode_flowBalance original.erase 0
  obtain ⟨balance⟩ := encode_indexed_balance original.erase 0
  have result := actual.conditional_complete_projection represented initial (.nil original.erase)
    (.nil original) (.nil original.erase) flow rfl balance rfl
    (encode_closed_independence original.erase closed 0).rootInputs
    (encode_closed_transparency original.erase closed 0) (encode_closed_matches original.erase closed 0) closed
  exact result

#print axioms PathSite.beta_empty_chain_representation_preserve
#print axioms LabelledGraphProjection.joint_source_rep_worker
#print axioms LabelledGraphProjection.initial_joint_representation
#print axioms LabelledGraphProjection.initial_source_chain_rep
#print axioms LabelledGraphProjection.complete_family_projection
end Lamping.AG
