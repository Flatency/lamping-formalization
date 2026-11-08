import Lamping.Lamping.BetaLabelledProjection
import Lamping.Lambda.Permutation

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

section
variable {B : Type} [FiniteNames B]

/-- A raw physical event. A beta carries one real complete OLD development,
not a whole historical family assertion. Auxiliary rules do not change the
labelled syntax. Neither Matches nor REP is a field of this relation. -/
inductive LabelledGraphEvent : Schema → ActualNet B → ActualNet B → B →
    (source target : LTerm) → ParallelHistory source.erase target.erase → Prop where
  | auxiliary {s g h root source} (step : GraphStep s g h)
      (notBeta : ∀ i,s≠.beta i) :
      LabelledGraphEvent s g h root source source (.nil source.erase)
  | beta {K W V : Type} [FiniteNames K] [FiniteNames W] [FiniteNames V]
      {i : Nat} {g h : ActualNet B} {root : B} {source target : LTerm}
      {ps : List Path} {marked : Marked} (kept : K → Graph.Label signature)
      (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
      (before : NetIso g.net site.net) (after : NetIso site.reduce h.net)
      (complete : Marked.CompleteOldDevelopment (site.betaSyntaxFiber root source.erase)
        source.erase ps marked)
      (labels : History ps source target) (erased : marked.erase=target.erase) :
      LabelledGraphEvent (.beta i) g h root source target
        (.single ⟨ps,marked,complete,erased⟩)

/-- Every actual step has a raw parallel event from the existing labels.
All correctness witnesses are derived here, not supplied on the event. The
result deliberately still allows an empty beta selection. -/
theorem GraphStep.labelled_event {s : Schema} {g h : ActualNet B}
    (step : GraphStep s g h)
    {directions : B → Bool} {heights : B → Int} {root : B}
    (flow : FlowBalance g.net directions) (positive : directions root=true)
    (balance : IndexedLevelBalance g.net heights) (rootDepth : heights root=0)
    (inputs : RootInputs g.net root) (oldT : Transparency g.net root)
    {source : LTerm} (matching : Matches g.net root source.erase) (closed : Closed source.erase) :
    ∃ (target : LTerm) (projection : ParallelHistory source.erase target.erase),
      LabelledGraphEvent s g h root source target projection ∧
      History projection.derivation.paths source target ∧ Matches h.net root target.erase := by
  have auxiliary (nonBeta : ∀ i,s≠.beta i) (next : Matches h.net root source.erase) :
      ∃ (target : LTerm) (projection : ParallelHistory source.erase target.erase),
        LabelledGraphEvent s g h root source target projection ∧
        History projection.derivation.paths source target ∧ Matches h.net root target.erase :=
    ⟨source,.nil _,.auxiliary step nonBeta,.nil _,next⟩
  cases s with
  | beta i =>
    cases step with
    | atSite kept site before after =>
      obtain ⟨ps,marked,target,complete,labels,erased,next⟩ := site.beta_labelled_projection closed
        (before.matches matching) (before.rootInputs inputs) (before.flowBalance flow) positive
        (before.indexed_balance balance) rootDepth (before.transparency oldT)
      let parallel : ParallelStep (site.betaSyntaxFiber root source.erase) source.erase target.erase :=
        ⟨ps,marked,complete,erased.symm⟩
      refine ⟨target,.single parallel,.beta kept site before after complete labels erased.symm,?_,
        after.matches next⟩
      simpa only [ParallelHistory.single,ParallelHistory.derivation,Derivation.append,Derivation.nil,
        ParallelStep.derivation,List.append_nil] using labels
  | fanCancel i =>
    exact auxiliary (by intro j bad; cases bad)
      (step.cancellation_matches_rootInputs (.fan i) flow positive inputs balance rootDepth oldT matching)
  | croCancel i =>
    exact auxiliary (by intro j bad; cases bad)
      (step.cancellation_matches_rootInputs (.cro i) flow positive inputs balance rootDepth oldT matching)
  | braCancel i =>
    exact auxiliary (by intro j bad; cases bad)
      (step.cancellation_matches_rootInputs (.bra i) flow positive inputs balance rootDepth oldT matching)
  | fanAction f i j lt =>
    exact auxiliary (by intro n bad; cases bad)
      (step.action_matches_rootInputs (.fan f i j lt) flow positive balance rootDepth inputs oldT matching)
  | croAction f i j lt =>
    exact auxiliary (by intro n bad; cases bad)
      (step.action_matches_rootInputs (.cro f i j lt) flow positive balance rootDepth inputs oldT matching)
  | braAction f i j lt =>
    exact auxiliary (by intro n bad; cases bad)
      (step.action_matches_rootInputs (.bra f i j lt) flow positive balance rootDepth inputs oldT matching)

end
end Lamping.AG
