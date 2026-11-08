import Lamping.Lamping.LabelledProjectionSemantics
import Lamping.Lamping.ObservableFamilyEvent
import Lamping.Lambda.ObservableFamilyHistory

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

section
variable {B : Type} [FiniteNames B]

/-- An explicit CONDITIONAL premise, separate from raw graph alignment.
Only actual event sources require chain REP, with their actual labels/root.
No future Matches, observed history or completeness certificate is stored.
An isomorphism-only tail has no event source to certify. Reachable joint REP
must independently establish this premise; this definition does not do so. -/
inductive LabelledGraphProjection.SourceChainREP :
    {g h : ActualNet B} → {root : B} → {schemas : List Schema} → {source target : LTerm} →
    {raw : ParallelHistory source.erase target.erase} →
    LabelledGraphProjection g h root schemas source target raw → Prop where
  | iso {g h : ActualNet B} {root : B} {source : LTerm} (same : NetIso g.net h.net) :
      SourceChainREP (LabelledGraphProjection.iso (root:=root) (source:=source) same)
  | cons {g h k : ActualNet B} {root : B} {s : Schema} {ss : List Schema}
      {source middle target : LTerm}
      {first : ParallelHistory source.erase middle.erase}
      {rest : ParallelHistory middle.erase target.erase}
      {event : LabelledGraphEvent s g h root source middle first}
      {tail : LabelledGraphProjection h k root ss middle target rest}
      (closed : Closed source.erase)
      (selection : OccurrenceFragmentSelection source g.net root)
      (representation : ChainRepresentationInvariant closed selection)
      (remaining : SourceChainREP tail) : SourceChainREP (.cons event tail)

private theorem append_family_steps {m t u v : Term}
    {prior : ParallelHistory m t} {first : ParallelHistory t u} {last : ParallelHistory u v}
    (head : FamilyStepsOrSilent prior first)
    (tail : FamilyStepsOrSilent (prior.append first) last) :
    FamilyStepsOrSilent prior (first.append last) := by
  induction head with
  | nil => simpa only [ParallelHistory.append_nil,ParallelHistory.append] using tail
  | cons whole rest ih =>
    apply FamilyStepsOrSilent.cons whole
    apply ih
    simpa only [ParallelHistory.append_assoc,ParallelHistory.single,ParallelHistory.append] using tail

private theorem event_family_steps
    {s : Schema} {g h : ActualNet B} {root : B} {original source target : LTerm}
    {raw : ParallelHistory source.erase target.erase}
    (event : LabelledGraphEvent s g h root source target raw)
    (initial : INIT original) (closed : Closed source.erase)
    (prior : ParallelHistory original.erase source.erase)
    (history : History prior.derivation.paths original source)
    (matching : Matches g.net root source.erase)
    (selection : OccurrenceFragmentSelection source g.net root)
    (representation : ChainRepresentationInvariant closed selection) :
    FamilyStepsOrSilent prior raw := by
  cases event with
  | auxiliary _ _ => exact .nil _
  | beta kept site before after complete labels erased =>
    let step : ParallelStep (site.betaSyntaxFiber root source.erase) source.erase target.erase :=
      ⟨_,_,complete,erased⟩
    by_cases empty : site.betaSyntaxFiber root source.erase=[]
    · exact .cons (.inl empty) (.nil _)
    · have siteMatching := before.matches matching
      obtain ⟨siteSelection⟩ := siteMatching.occurrence_fragment_selection closed
      have siteRepresentation : ChainRepresentationInvariant closed siteSelection := by
        intro p q left right first second
        exact (before.chain_representation matching selection siteSelection first second).trans
          (representation first second)
      exact .cons (.inr (site.beta_complete_family_step initial closed prior history
        siteMatching siteSelection siteRepresentation empty step)) (.nil _)

private theorem closed_after_history {source target : LTerm} {ps : List Path}
    (history : History ps source target) (closed : Closed source.erase) : Closed target.erase := by
  revert closed
  induction history with
  | nil => exact id
  | cons turn _ ih => exact fun closed=>ih (turn.betaAt.beta.scoped closed)

/-- CONDITIONAL on chain REP at every actual event source, all nonempty
raw boundaries contract whole historical families. The induction updates
the SAME original history by actual raw prefixes, never by reinitialization
or an independently chosen complete-development schedule. -/
theorem LabelledGraphProjection.family_steps_of_source_rep
    {g h : ActualNet B} {root : B} {schemas : List Schema} {source target : LTerm}
    {raw : ParallelHistory source.erase target.erase}
    (projection : LabelledGraphProjection g h root schemas source target raw)
    (represented : projection.SourceChainREP)
    {original : LTerm} (initial : INIT original)
    (prior : ParallelHistory original.erase source.erase)
    (history : History prior.derivation.paths original source)
    {directions : B → Bool} {heights : B → Int}
    (flow : FlowBalance g.net directions) (positive : directions root=true)
    (balance : IndexedLevelBalance g.net heights) (rootDepth : heights root=0)
    (inputs : RootInputs g.net root) (transparent : Transparency g.net root)
    (matching : Matches g.net root source.erase) (closed : Closed source.erase) :
    FamilyStepsOrSilent prior raw := by
  induction represented with
  | iso _ => exact .nil _
  | @cons g middle last root schema schemas source next target first rest event tail _sourceClosed selection representation representedTail ih =>
    have head := event_family_steps event initial closed prior history matching selection representation
    have nextHistory : History (prior.append first).derivation.paths original next := by
      simpa only [ParallelHistory.derivation_append,Derivation.append] using
        history.append event.label_history
    have step := event.graph_step
    have nextMatching := event.target_matches flow positive balance rootDepth inputs transparent matching closed
    have nextInputs := step.rootInputs flow positive balance rootDepth inputs transparent matching
    obtain ⟨nextFlow⟩ := step.flowBalance flow
    obtain ⟨nextBalance⟩ := step.indexed_balance balance
    have nextTransparent := step.transparency_indexed flow positive balance rootDepth transparent
    have remaining := ih (prior.append first) nextHistory nextFlow positive
      nextBalance rootDepth nextInputs nextTransparent nextMatching
      (closed_after_history event.label_history closed)
    exact append_family_steps head remaining

/-- CONDITIONAL full finite-history assembly. SourceChainREP is an explicit
unproved input until the seven-rule reachable REP theorem is supplied.
Given that premise, empty boundaries are deleted, literal contraction paths
and existing labels are preserved, and an already complete prefix extends
to a complete observable history on the actual fixed target graph. -/
theorem LabelledGraphProjection.conditional_complete_projection
    {g h : ActualNet B} {root : B} {schemas : List Schema} {source target : LTerm}
    {raw : ParallelHistory source.erase target.erase}
    (projection : LabelledGraphProjection g h root schemas source target raw)
    (represented : projection.SourceChainREP)
    {original : LTerm} (initial : INIT original)
    (prior : ParallelHistory original.erase source.erase)
    (history : History prior.derivation.paths original source)
    (completePrior : CompleteDerivation prior)
    {directions : B → Bool} {heights : B → Int}
    (flow : FlowBalance g.net directions) (positive : directions root=true)
    (balance : IndexedLevelBalance g.net heights) (rootDepth : heights root=0)
    (inputs : RootInputs g.net root) (transparent : Transparency g.net root)
    (matching : Matches g.net root source.erase) (closed : Closed source.erase) :
    ∃ observed : ParallelHistory source.erase target.erase,
      ParallelHistory.Observable observed ∧raw.derivation=observed.derivation ∧
      PermEq raw observed ∧History observed.derivation.paths source target ∧
      CompleteDerivation (prior.append observed) ∧
      RootInputs h.net root ∧Matches h.net root target.erase := by
  have certified := projection.family_steps_of_source_rep represented initial prior history
    flow positive balance rootDepth inputs transparent matching closed
  obtain ⟨observed,observable,same,permutation,complete⟩ := certified.observable_complete completePrior
  exact ⟨observed,observable,same,permutation,same ▸ projection.label_history,complete,
    projection.target_matches flow positive balance rootDepth inputs transparent matching closed⟩

end
end Lamping.AG
