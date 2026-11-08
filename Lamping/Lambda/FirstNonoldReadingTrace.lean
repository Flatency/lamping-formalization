import Lamping.Lambda.UniformReadingCreationTrace
namespace Lamping.Lambda.Labelled
private theorem first_false_split {P : Path →Prop} [DecidablePred P]
    (has : ∃ e∈edges,¬P e) :
    ∃ before e after,edges=before++(e::after) ∧(∀ x∈before,P x) ∧¬P e := by
  induction edges with
  | nil => obtain ⟨e,mem,_⟩ := has;cases mem
  | cons head tail ih =>
    by_cases good : P head
    · have rest : ∃ e∈tail,¬P e := by
        obtain ⟨e,mem,bad⟩ := has
        rcases List.mem_cons.mp mem with equal | inside
        · exact False.elim (bad (equal ▸ good))
        · exact ⟨e,inside,bad⟩
      obtain ⟨before,e,after,split,all,bad⟩ := ih rest
      refine ⟨head::before,e,after,?_,?_,bad⟩
      · rw [split];rfl
      · intro x mem
        rcases List.mem_cons.mp mem with equal | inside
        · exact equal ▸ good
        · exact all x inside
    · refine ⟨[],head,tail,rfl,?_,good⟩
      intro x mem;cases mem
end Lamping.Lambda.Labelled
namespace Lamping.Lambda
open Labelled
/-- Selects an actual FIRST final nonold reading, then traces its precise
literal label to an actual uniform OLD event. Not a first-marker theorem. -/
theorem ParallelStep.first_nonold_reading_creation
    {source target : LTerm} {F : List Path} {degree : Label}
    (program : ParallelStep F source.erase target.erase)
    (labels : History program.paths source target)
    (selected : ∀ p∈F,source.degreeAt p=some degree)
    (sourceSafe : source.OuterBarsSafe (fun x=>x≠degree))
    (chain : PrerequisiteChain target start edges)
    (fresh : ∃ edge∈edges,∃ current,target.subterm edge=some current ∧current.label∉source.labels) :
    ∃ before edge after middle current,
      edges=before++(edge::after) ∧PrerequisitePrefix target start before middle ∧
      PrerequisiteReads target middle edge ∧
      (∀ e∈before,∃ old,target.labelAt e=some old ∧old∈source.labels) ∧
      target.subterm edge=some current ∧current.label∉source.labels ∧
      CreatedReadingEvent F program.paths (Marked.mark F source.erase) program.markedTarget
        source target degree (before.map target.labelAt) (target.labelAt edge) := by
  classical
  let P : Path →Prop := fun e=>∃ old,target.labelAt e=some old ∧old∈source.labels
  have bad : ∃ e∈edges,¬P e := by
    obtain ⟨e,inside,current,lookup,new⟩ := fresh
    refine ⟨e,inside,?_⟩
    rintro ⟨old,equal,oldMem⟩
    have labelEq : current.label=old := by
      simpa only [LTerm.labelAt,lookup,Option.map_some,Option.some.injEq] using equal
    exact new (labelEq ▸ oldMem)
  obtain ⟨before,edge,after,split,beforeOld,new⟩ := first_false_split bad
  have member : edge∈edges := by rw [split];exact List.mem_append_right _ List.mem_cons_self
  obtain ⟨bs,as,mid,otherSplit,segment,remaining,reads⟩ := chain.split_at_member member
  have unique := chain.first_created_split_unique split otherSplit
  obtain ⟨bsEq,asEq⟩ := unique
  subst bs;subst as
  have lookup : ∃ current,target.subterm edge=some current := by
    rcases chain.eligible member with ⟨p,a,f,b,equal,atParent⟩ | ⟨a,b,atLambda⟩
    · refine ⟨f,?_⟩;rw [equal,LTerm.subterm_append,atParent];cases f <;> rfl
    · exact ⟨_,atLambda⟩
  obtain ⟨current,atCurrent⟩ := lookup
  have currentFresh : current.label∉source.labels := by
    intro mem
    exact new ⟨current.label,by simp only [LTerm.labelAt,atCurrent,Option.map_some],mem⟩
  have safe : ∀ e∈before,∀ node,target.subterm e=some node →
      node.label.OuterBarsSafe (fun x=>x≠degree) := by
    intro e inside node atNode
    obtain ⟨old,equal,oldMem⟩ := beforeOld e inside
    have labelEq : node.label=old := by
      simpa only [LTerm.labelAt,atNode,Option.map_some,Option.some.injEq] using equal
    rw [labelEq];exact (LTerm.outerBarsSafe_iff _ _).mp sourceSafe old oldMem
  exact ⟨before,edge,after,mid,current,split,segment,reads,beforeOld,atCurrent,currentFresh,
    program.complete.1.created_reading_event_of_fresh (DegreeAligned.initial source F)
      labels selected segment reads safe atCurrent currentFresh⟩
end Lamping.Lambda
