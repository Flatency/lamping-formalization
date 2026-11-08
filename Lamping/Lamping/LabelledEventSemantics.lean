import Lamping.Lamping.LabelledGraphEvents

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

section
variable {B : Type} [FiniteNames B]
variable {s : Schema} {g h : ActualNet B} {root : B} {source target : LTerm}
  {projection : ParallelHistory source.erase target.erase}

theorem LabelledGraphEvent.graph_step
    (event : LabelledGraphEvent s g h root source target projection) : GraphStep s g h := by
  cases event with
  | auxiliary step _ => exact step
  | beta kept site before after _ _ _ => exact .atSite kept site before after

theorem LabelledGraphEvent.label_history
    (event : LabelledGraphEvent s g h root source target projection) :
    History projection.derivation.paths source target := by
  cases event with
  | auxiliary _ _ => exact .nil _
  | beta _ _ _ _ _ labels _ =>
    simpa only [ParallelHistory.single,ParallelHistory.derivation,Derivation.append,Derivation.nil,
      ParallelStep.derivation,List.append_nil] using labels

/-- Any OLD schedule carried by this actual event matches its own specified
target graph. Beta endpoint uniqueness is used on the SAME physical fiber;
the supplied target is not replaced by an arbitrary existential reduct. -/
theorem LabelledGraphEvent.target_matches
    (event : LabelledGraphEvent s g h root source target projection)
    {directions : B → Bool} {heights : B → Int}
    (flow : FlowBalance g.net directions) (positive : directions root=true)
    (balance : IndexedLevelBalance g.net heights) (rootDepth : heights root=0)
    (inputs : RootInputs g.net root) (transparent : Transparency g.net root)
    (matching : Matches g.net root source.erase) (closed : Closed source.erase) :
    Matches h.net root target.erase := by
  cases event with
  | auxiliary step notBeta =>
    cases s with
    | beta i => exact False.elim (notBeta i rfl)
    | fanCancel i => exact step.cancellation_matches_rootInputs (.fan i) flow positive inputs balance rootDepth transparent matching
    | croCancel i => exact step.cancellation_matches_rootInputs (.cro i) flow positive inputs balance rootDepth transparent matching
    | braCancel i => exact step.cancellation_matches_rootInputs (.bra i) flow positive inputs balance rootDepth transparent matching
    | fanAction f i j lt => exact step.action_matches_rootInputs (.fan f i j lt) flow positive balance rootDepth inputs transparent matching
    | croAction f i j lt => exact step.action_matches_rootInputs (.cro f i j lt) flow positive balance rootDepth inputs transparent matching
    | braAction f i j lt => exact step.action_matches_rootInputs (.bra f i j lt) flow positive balance rootDepth inputs transparent matching
  | beta kept site before after complete labels erased =>
    obtain ⟨ps,marked,other,developed,_labels,otherErased,otherMatching⟩ :=
      site.beta_labelled_projection closed (before.matches matching) (before.rootInputs inputs)
        (before.flowBalance flow) positive (before.indexed_balance balance) rootDepth
        (before.transparency transparent)
    have same : target.erase=other.erase :=
      (ParallelStep.endpoint
        (⟨_,_,complete,erased⟩ : ParallelStep (site.betaSyntaxFiber root source.erase) source.erase target.erase)
        (⟨ps,marked,developed,otherErased.symm⟩ : ParallelStep (site.betaSyntaxFiber root source.erase) source.erase other.erase))
    rw [same]
    exact after.matches otherMatching

end
end Lamping.AG
