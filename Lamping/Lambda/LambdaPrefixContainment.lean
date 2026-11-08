import Lamping.Lambda.PrerequisitePrefixes
namespace Lamping.Lambda.Labelled
/-- A real dependency prefix can enter a lambda only from its own syntax
subtree. A function application whose child is already lambda stops instead. -/
theorem PrerequisitePrefix.lambda_finish_contains_start
    (segment : PrerequisitePrefix t start before finish)
    (atFinish : t.subterm finish=some (.lam origin body)) :
    ∃ relative,start=finish++relative := by
  induction segment with
  | refl => exact ⟨[],by simp⟩
  | @app p stamp fn arg es endpoint lookup notLambda tail ih =>
    obtain ⟨relative,inside⟩ := ih atFinish
    rcases List.append_eq_append_iff.mp inside with ⟨extra,finishEq,lastEq⟩ | ⟨extra,parentEq,_⟩
    · cases extra with
      | nil => exact ⟨[],by simpa only [List.append_nil] using finishEq.symm⟩
      | cons child rest =>
        have parts := List.cons.inj lastEq
        have emptyRest : rest=[] := (List.append_eq_nil_iff.mp parts.2.symm).1
        have finishAtChild : endpoint=p++[Step.fn] := by
          simpa only [emptyRest,←parts.1] using finishEq
        have childLookup : t.subterm (p++[Step.fn])=some fn := by
          rw [LTerm.subterm_append,lookup]; cases fn <;> rfl
        rw [finishAtChild] at atFinish
        exact False.elim (notLambda origin body (Option.some.inj (childLookup.symm.trans atFinish)))
    · exact ⟨extra,parentEq⟩
  | @lam parent child stamp inner es endpoint lookup notFunction tail ih =>
    obtain ⟨relative,parentEq⟩ := ih atFinish
    exact ⟨relative++[child],by rw [parentEq,List.append_assoc]⟩
  | @var leaf stamp index parent binderStamp inner rest es endpoint lookup binder split depth tail ih =>
    obtain ⟨relative,parentEq⟩ := ih atFinish
    exact ⟨relative++(.body::rest),by rw [split,parentEq,List.append_assoc]⟩
end Lamping.Lambda.Labelled
