import Lamping.Lambda.PrerequisitePrefixes
namespace Lamping.Lambda.Labelled
/-- To end within a literal subtree, an actual finite dependency prefix
must either start there or actually read that subtree's incoming edge. -/
theorem PrerequisitePrefix.subtree_entry
    (segment : PrerequisitePrefix t start before finish)
    (finishInside : finish=head++relative) :
    (∃ inside,start=head++inside) ∨head∈before := by
  induction segment generalizing relative with
  | refl => exact Or.inl ⟨relative,finishInside⟩
  | @app p stamp fn arg es endpoint lookup notLambda tail ih =>
    rcases ih finishInside with ⟨inside,childInside⟩ | headRead
    · rcases List.append_eq_append_iff.mp childInside with ⟨extra,headEq,lastEq⟩ | ⟨extra,parentEq,_⟩
      · cases extra with
        | nil => exact Or.inl ⟨[],by simpa only [List.append_nil] using headEq.symm⟩
        | cons child rest =>
          have parts := List.cons.inj lastEq
          have emptyRest : rest=[] := (List.append_eq_nil_iff.mp parts.2.symm).1
          have entry : head=p++[Step.fn] := by simpa only [emptyRest,←parts.1] using headEq
          exact Or.inr (List.mem_cons.mpr (Or.inl entry))
      · exact Or.inl ⟨extra,parentEq⟩
    · exact Or.inr (List.mem_cons_of_mem _ headRead)
  | @lam parent child stamp body es endpoint lookup notFunction tail ih =>
    rcases ih finishInside with ⟨inside,parentInside⟩ | headRead
    · exact Or.inl ⟨inside++[child],by rw [parentInside,List.append_assoc]⟩
    · exact Or.inr (List.mem_cons_of_mem _ headRead)
  | @var leaf stamp index parent origin body rest es endpoint lookup binder split depth tail ih =>
    rcases ih finishInside with ⟨inside,parentInside⟩ | headRead
    · exact Or.inl ⟨inside++(.body::rest),by rw [split,parentInside,List.append_assoc]⟩
    · exact Or.inr headRead

/-- An unread incoming edge excludes entry from outside; its start
coordinate is then obtained from the actual finite prefix itself. -/
theorem PrerequisitePrefix.start_inside_of_unread
    (segment : PrerequisitePrefix t start before finish)
    (finishInside : finish=head++relative) (unread : head∉before) :
    ∃ inside,start=head++inside := by
  rcases segment.subtree_entry finishInside with inside | read
  · exact inside
  · exact False.elim (unread read)
end Lamping.Lambda.Labelled
