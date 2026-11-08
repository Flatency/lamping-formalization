import Lamping.Lamping.RootCancellationInputs
import Lamping.Lamping.RootBindingSuffixUniqueness
import Lamping.Lamping.RootInputAccessGeometry
import Lamping.Lamping.CancellationMatching
import Lamping.Lamping.ReachableTransparency
import Lamping.Lamping.ReachableNesting
namespace Lamping.AG
open Graph Lambda
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))

private theorem observes_root (cancel : IsCancellation s)
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true)
    (newInputs : RootInputs site.reduce root) (newN : Nesting site.reduce root)
    (newT : Transparency site.reduce root)
    (source : RootAccess site.net root) (target : RootAccess site.reduce root)
    (word : accessWord site.reduce target.val=accessWord site.net source.val)
    (kind : accessKind site.reduce target.val=accessKind site.net source.val)
    (shape : AccessShape) (observed : Observes site.net source.val shape) :
    Observes site.reduce target.val shape := by
  refine ⟨kind.trans observed.1,?_⟩
  cases shape with
  | app => trivial
  | lam => trivial
  | var index =>
    obtain ⟨reduced,reducedWord,_reducedKind,suffix⟩ :=
      site.cancellation_binding_suffix cancel flow root positive source observed.2.1
    have same : reduced=target := newInputs.accessWord_injective (reducedWord.trans word.symm)
    rw [same] at suffix
    exact ⟨suffix,fun j other => newInputs.binding_suffix_unique newN newT target other suffix⟩

/-- Actual cancellation preserves full Matches from weak source root inputs,
structural balance and ordinary T. Every target property used in the proof
is constructed from the actual rewrite, rather than assumed by the caller. -/
theorem PathSite.cancellation_matches_rootInputs (cancel : IsCancellation s)
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true)
    (inputs : RootInputs site.net root) {depths : B → Int}
    (balance : IndexedLevelBalance site.net depths) (rootDepth : depths root=0)
    (oldT : Transparency site.net root) {t : Term} (matching : Matches site.net root t) :
    Matches site.reduce root t := by
  have newInputs := site.cancellation_rootInputs cancel flow root positive inputs
  obtain ⟨newBalance⟩ := site.reduce_indexed_balance balance
  have newN := newBalance.nesting root rootDepth
  have newT := site.cancellation_transparency cancel flow root positive oldT
  obtain ⟨f,corresponds,_prefix⟩ := matching
  apply matches_of_access_classification site.reduce root t
  · intro target
    obtain ⟨source,word,kind⟩ := site.cancellation_root_access_backward cancel flow root positive target
    obtain ⟨sourceWord,u,subterm,observation⟩ := corresponds source
    refine ⟨u,?_,?_⟩
    · rw [←word,sourceWord]; exact subterm
    · exact observes_root site cancel flow root positive newInputs newN newT source target
        word.symm kind.symm _ observation
  · intro position
    let source := f.invFun position
    have actual := corresponds source
    have same : f source=position := f.right_inv position
    rw [same] at actual
    obtain ⟨target,word,_kind⟩ := site.cancellation_root_access_forward cancel flow root positive source
    exact ⟨target,word.trans actual.1⟩
  · exact fun es fs word => newInputs.accessWord_injective word
end

section
variable {B : Type} [FiniteNames B] {directions : B → Bool} {depths : B → Int} {root : B}

theorem GraphStep.cancellation_matches_rootInputs {s : Schema} {g h : ActualNet B}
    (step : GraphStep s g h) (cancel : IsCancellation s)
    (flow : FlowBalance g.net directions) (positive : directions root=true)
    (inputs : RootInputs g.net root) (balance : IndexedLevelBalance g.net depths)
    (rootDepth : depths root=0) (oldT : Transparency g.net root)
    {t : Term} (matching : Matches g.net root t) : Matches h.net root t := by
  cases step with
  | atSite kept site sourceIso targetIso =>
    exact targetIso.matches (site.cancellation_matches_rootInputs cancel (sourceIso.flowBalance flow)
      root positive (sourceIso.rootInputs inputs) (sourceIso.indexed_balance balance) rootDepth
      (sourceIso.transparency oldT) (sourceIso.matches matching))

/-- Explicit cancellation-only traces, with all intermediate weak inputs,
structural balance and T derived from the actual successive steps. -/
theorem GraphTrace.cancellation_matches_rootInputs {g h : ActualNet B} {schemas : List Schema}
    (trace : GraphTrace g h schemas) (cancels : ∀ s∈schemas,IsCancellation s)
    (flow : FlowBalance g.net directions) (positive : directions root=true)
    (inputs : RootInputs g.net root) (balance : IndexedLevelBalance g.net depths)
    (rootDepth : depths root=0) (oldT : Transparency g.net root)
    {t : Term} (matching : Matches g.net root t) : Matches h.net root t := by
  induction trace with
  | iso same => exact same.matches matching
  | cons step tail ih =>
    have cancel := cancels _ List.mem_cons_self
    obtain ⟨newFlow⟩ := step.flowBalance flow
    obtain ⟨newBalance⟩ := step.indexed_balance balance
    exact ih (fun s member => cancels s (List.mem_cons_of_mem _ member)) newFlow
      (step.cancellation_rootInputs cancel flow positive inputs) newBalance
      (step.transparency_indexed flow positive balance rootDepth oldT)
      (step.cancellation_matches_rootInputs cancel flow positive inputs balance rootDepth oldT matching)
end
end Lamping.AG
