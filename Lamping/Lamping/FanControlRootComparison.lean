import Lamping.Lamping.FanControlOccurrenceComparison
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {current : LTerm} {g : Net signature N B W} {root : B}

private theorem SourcePortRealizes.external_endpoint_iff
    (realizes : SourcePortRealizes current g root source endpoint) :
    endpoint=.inr (.inl root) ↔source=.external := by
  cases realizes with
  | external => exact ⟨fun _=>rfl,fun _=>rfl⟩
  | departure _ role _ _ _ _ =>
    constructor
    · intro same;cases same
    · intro same;rw [same] at role;cases role
  | appContext | lamContext | binding => constructor <;> intro same <;> cases same

theorem OccurrenceFragment.head_root_iff
    (fragment : OccurrenceFragment current g root position) :
    fragment.fragment.segments.head?=some (.inr (.inl root)) ↔position=[] := by
  rcases fragment with ⟨sub,env,ctx,occurrence,fragment⟩
  have sourceFrom : (sourceEdge env ctx sub).fromPort=ctx := by cases sub <;> rfl
  have endpoint : fragment.fromEndpoint=.inr (.inl root) ↔ctx=.external := by
    simpa only [sourceFrom] using fragment.fromRealizes.external_endpoint_iff
  have context : ctx=.external ↔position=[] := by
    constructor
    · intro external
      rcases occurrence.last_departure with ⟨empty,_⟩ |⟨_,_,_,_,_,role⟩
      · exact empty
      · rw [external] at role;cases role
    · intro empty
      subst position
      cases occurrence
      rfl
  change fragment.segments.head?=some (.inr (.inl root)) ↔position=[]
  rw [fragment.start,Option.some.injEq]
  exact endpoint.trans context

theorem OccurrenceFragment.ne_of_root_nonroot
    (first : OccurrenceFragment current g root [])
    (second : OccurrenceFragment current g root position) (nonroot : position≠[]) :
    first.fragment.segments≠second.fragment.segments := by
  intro same
  have head := congrArg List.head? same
  have rootHead := first.head_root_iff.mpr rfl
  have otherHead := head.symm.trans rootHead
  exact nonroot (second.head_root_iff.mp otherHead)
end
section
variable {op : Op} {i j : Nat} {lt : i<j}
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature}
variable (site : PathSite (Schema.fanAction op i j lt) kept (B:=B) (W:=W) (V:=V))

/-- Boundary and node departures remain distinct on both sides. Thus the
control-fan comparison also covers root occurrences, without completing paths. -/
theorem PathSite.fan_control_occurrence_equality
    (control : op=.fan ∨ op=.cro ∨ op=.bra)
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase)
    (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site) {p q : Path}
    (sourceFirst : OccurrenceFragment current site.net root p)
    (targetFirst : OccurrenceFragment current site.reduce root p)
    (sourceSecond : OccurrenceFragment current site.net root q)
    (targetSecond : OccurrenceFragment current site.reduce root q) :
    targetFirst.fragment.segments=targetSecond.fragment.segments ↔
      sourceFirst.fragment.segments=sourceSecond.fragment.segments := by
  by_cases leftRoot : p=[]
  · subst p
    by_cases rightRoot : q=[]
    · subst q
      exact ⟨fun _=>sourceFirst.segments_unique sourceMatches sourceSecond,
        fun _=>targetFirst.segments_unique targetMatches targetSecond⟩
    · exact ⟨fun same=>(targetFirst.ne_of_root_nonroot targetSecond rightRoot same).elim,
        fun same=>(sourceFirst.ne_of_root_nonroot sourceSecond rightRoot same).elim⟩
  · by_cases rightRoot : q=[]
    · subst q
      exact ⟨fun same=>(targetSecond.ne_of_root_nonroot targetFirst leftRoot same.symm).elim,
        fun same=>(sourceSecond.ne_of_root_nonroot sourceFirst leftRoot same.symm).elim⟩
    · exact site.fan_control_nonroot_occurrence_equality control flow root positive
        sourceMatches targetMatches principal leftRoot rightRoot
        sourceFirst targetFirst sourceSecond targetSecond
end
end Lamping.AG
