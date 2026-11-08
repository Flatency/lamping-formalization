import Lamping.Lamping.CancellationBindingSuffix
import Lamping.Lamping.CancellationInvariantPreservation
import Lamping.Lamping.ForwardAccessDeterminism
import Lamping.Lamping.MatchingInitial
namespace Lamping.AG
open Graph Lambda
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))

/-- Actual cancellation preserves the full variable observation, including the
unique binder index, on any old/new accesses with the same word and kind. -/
theorem PathSite.cancellation_observes (cancel : IsCancellation s)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary)
    (root : B) (positive : boundary root=true) (old : OrdinaryPathInvariants site.net root)
    (source : RootAccess site.net root) (target : RootAccess site.reduce root)
    (word : accessWord site.reduce target.val=accessWord site.net source.val)
    (kind : accessKind site.reduce target.val=accessKind site.net source.val)
    (shape : AccessShape) (observed : Observes site.net source.val shape) :
    Observes site.reduce target.val shape := by
  have preserved := site.cancellation_ordinary_invariants cancel flow root positive old
  refine ⟨kind.trans observed.1,?_⟩
  cases shape with
  | app => trivial
  | lam => trivial
  | var index =>
    obtain ⟨reduced,reducedWord,_reducedKind,suffix⟩ :=
      site.cancellation_binding_suffix cancel flow root positive source observed.2.1
    have same : reduced=target := preserved.independence.accessWord_injective
      (reducedWord.trans word.symm)
    rw [same] at suffix
    exact ⟨suffix,fun j other => preserved.binding_suffix_unique target other suffix⟩

/-- Each of the actual standard cancellations preserves Def3.5.13 Matches.
Both visibility and coverage are transported on actual rooted accesses;
ordinary invariants prove word injectivity and binder-occurrence uniqueness. -/
theorem PathSite.cancellation_matches (cancel : IsCancellation s)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary)
    (root : B) (positive : boundary root=true) (old : OrdinaryPathInvariants site.net root)
    {t : Term} (matching : Matches site.net root t) : Matches site.reduce root t := by
  obtain ⟨f,corresponds,_prefix⟩ := matching
  have preserved := site.cancellation_ordinary_invariants cancel flow root positive old
  apply matches_of_access_classification site.reduce root t
  · intro target
    obtain ⟨source,word,kind⟩ := site.cancellation_root_access_backward cancel flow root positive target
    obtain ⟨sourceWord,u,subterm,observation⟩ := corresponds source
    refine ⟨u,?_,?_⟩
    · rw [←word,sourceWord]; exact subterm
    · exact site.cancellation_observes cancel flow root positive old source target word.symm kind.symm _ observation
  · intro position
    let source := f.invFun position
    have actual := corresponds source
    have same : f source=position := f.right_inv position
    rw [same] at actual
    obtain ⟨target,word,_kind⟩ := site.cancellation_root_access_forward cancel flow root positive source
    exact ⟨target,word.trans actual.1⟩
  · exact fun es fs word => preserved.independence.accessWord_injective word
end

section
variable {B : Type} [FiniteNames B] {boundary : B → Bool} {root : B}

theorem GraphStep.cancellation_matches {s : Schema} {g h : ActualNet B}
    (step : GraphStep s g h) (cancel : IsCancellation s)
    (flow : FlowBalance g.net boundary) (positive : boundary root=true)
    (old : OrdinaryPathInvariants g.net root) {t : Term} (matching : Matches g.net root t) :
    Matches h.net root t := by
  cases step with
  | atSite kept site sourceIso targetIso =>
    exact targetIso.matches (site.cancellation_matches cancel (sourceIso.flowBalance flow) root positive
      (sourceIso.ordinaryInvariants old) (sourceIso.matches matching))

/-- Only cancellation traces are covered; beta/action matching and all-schema
SND remain separate obligations. -/
theorem GraphTrace.cancellation_matches {g h : ActualNet B} {schemas : List Schema}
    (trace : GraphTrace g h schemas) (cancels : ∀ s∈schemas,IsCancellation s)
    (flow : FlowBalance g.net boundary) (positive : boundary root=true)
    (old : OrdinaryPathInvariants g.net root) {t : Term} (matching : Matches g.net root t) :
    Matches h.net root t := by
  induction trace with
  | iso same => exact same.matches matching
  | cons step tail ih =>
    obtain ⟨changedFlow⟩ := step.flowBalance flow
    exact ih (fun s mem => cancels s (List.mem_cons_of_mem _ mem)) changedFlow
      (step.cancellation_ordinary_invariants (cancels _ (by simp)) flow positive old)
      (step.cancellation_matches (cancels _ (by simp)) flow positive old matching)
end

/-- The actual closed initial graph retains its original matching term along
any explicitly cancellation-only finite trace, including carrier renamings. -/
theorem initial_cancellation_trace_matches (t : Term) (closed : Closed t)
    (target : ActualNet (Boundary t)) (schemas : List Schema)
    (trace : GraphTrace (ActualNet.initial t) target schemas)
    (cancels : ∀ s∈schemas,IsCancellation s) : Matches target.net (.inl ()) t := by
  obtain ⟨flow⟩ := encode_flowBalance t 0
  exact trace.cancellation_matches cancels flow rfl
    (encode_closed_ordinary_invariants t closed 0) (encode_closed_matches t closed 0)
end Lamping.AG
