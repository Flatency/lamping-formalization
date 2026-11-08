import Lamping.Lamping.CorridorOccurrenceSeams
namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

/-- Select the last actual turn at its literal ordinal, retaining the entire
labelled prefix. Physical endpoints may occur at earlier ordinals too. -/
theorem Labelling.last_turn {before : List (Endpoint g)} {last : Endpoint g} {a b : Context}
    (labels : Labelling g (before++[last]) a b) (nonempty : before≠[]) :
    ∃ initial previous middle,before=initial++[previous] ∧
      Labelling g (initial++[previous]) a middle ∧
      LabelledTurn g (g.wire previous) last middle b := by
  induction before generalizing a with
  | nil => exact False.elim (nonempty rfl)
  | cons x before ih =>
    cases before with
    | nil =>
      cases labels with
      | cons turn rest =>
        cases rest
        exact ⟨[],x,a,rfl,.single _ _,turn⟩
    | cons y before =>
      cases labels with
      | cons turn rest =>
        obtain ⟨initial,previous,middle,split,pref,final⟩ := ih rest (by simp)
        have actualPrefix : Labelling g ((x::initial)++[previous]) a middle := by
          rw [←split] at pref
          simpa only [List.cons_append,←split] using Labelling.cons turn pref
        exact ⟨x::initial,previous,middle,congrArg (List.cons x) split,actualPrefix,final⟩

/-- Exact boundary cases of this occurrence of a transparent corridor. Both
real turns use one common context from the original whole assignment. Empty
sides mean the original input/output, rather than invented boundary turns. -/
theorem Labelling.corridor_boundary_turns (route : TransparentCorridor g)
    (before after : List (Endpoint g)) {a b : Context}
    (labels : Labelling g ((before++route.edges)++after) a b) :
    ∃ middle,
      (before=[] ∧a=middle ∨∃ initial previous input,
        before=initial++[previous] ∧Labelling g (initial++[previous]) a input ∧
        LabelledTurn g (g.wire previous) (.inl route.first) input middle) ∧
      (after=[] ∧middle=b ∨∃ next remaining output,
        after=next::remaining ∧LabelledTurn g (.inl route.last) next middle output ∧
        Labelling g (next::remaining) output b) := by
  obtain ⟨middle,pref,suff⟩ := labels.corridor_seams route before after
  refine ⟨middle,?_,?_⟩
  · cases before with
    | nil =>
      cases pref
      exact Or.inl ⟨rfl,rfl⟩
    | cons e before =>
      obtain ⟨initial,previous,input,split,actual,turn⟩ := pref.last_turn (by simp)
      exact Or.inr ⟨initial,previous,input,split,actual,turn⟩
  · cases after with
    | nil =>
      cases suff
      exact Or.inl ⟨rfl,rfl⟩
    | cons next remaining =>
      cases suff with
      | cons turn rest =>
        rw [Pairing.involutive] at turn
        exact Or.inr ⟨next,remaining,_,rfl,turn,rest⟩
end
end Lamping.AG
