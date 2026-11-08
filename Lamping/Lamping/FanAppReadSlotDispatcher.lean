import Lamping.Lamping.FanAppArgumentLambdaTransport
namespace Lamping.Lambda.Labelled
/-- Membership in the supplied actual APP read list, rather than starting
at an APP, constructs its next FUNCTION read at the actual next ordinal. -/
theorem PrerequisiteChain.app_read_next_function_slot {n : Nat}
    (chain : PrerequisiteChain current start edges)
    (slot : edges[n]?=some leaf)
    (atApp : current.subterm leaf=some (.app stamp fn arg)) :
    ∃more,PrerequisiteChain current leaf more ∧edges[n+1]?=some (leaf++[.fn]) := by
  obtain ⟨before,after,middle,split,_segment,remainder,reads⟩ :=
    chain.split_at_member (List.mem_of_getElem? slot)
  have atSplit : edges[before.length]?=some leaf := by
    rw [split,List.getElem?_append_right (Nat.le_refl _)];simp
  obtain ⟨bound,_⟩ := List.getElem?_eq_some_iff.mp slot
  have ordinal : n=before.length := List.getElem?_inj bound chain.nodup (slot.trans atSplit.symm)
  have childChain : PrerequisiteChain current leaf after := by
    rcases reads with ⟨a,f,x,lookup,edgeEq⟩|⟨l,body,lookup,edgeEq⟩
    · rcases remainder.app_cases lookup with ⟨l,b,same,one⟩|⟨_,tail,equal,child⟩
      · have leafLookup : current.subterm leaf=some (.lam l b) := by
          rw [edgeEq,LTerm.subterm_append,lookup,same];rfl
        cases Option.some.inj (atApp.symm.trans leafLookup)
      · have tailEq : after=tail := (List.cons.inj equal).2
        rw [←edgeEq,←tailEq] at child
        exact child
    · rw [←edgeEq] at lookup
      cases Option.some.inj (atApp.symm.trans lookup)
  have head : after.head?=some (leaf++[.fn]) := by
    rcases childChain.app_cases atApp with ⟨_,_,_,equal⟩|⟨_,_,equal,_⟩ <;> rw [equal] <;> rfl
  refine ⟨after,childChain,?_⟩
  rw [ordinal,split,List.getElem?_append_right (by omega)]
  simpa only [Nat.add_sub_cancel_left,List.getElem?_cons_succ,←List.head?_eq_getElem?] using head
end Lamping.Lambda.Labelled
#print axioms Lamping.Lambda.Labelled.PrerequisiteChain.app_read_next_function_slot
