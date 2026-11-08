import Lamping.Lamping.LabelledControlCorridors
import Lamping.Lamping.ExpandedIndependence
namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

/-- Retain the last segment of a supplied transparent occurrence list and
the original continuation, with the original context unchanged. -/
theorem Labelling.transparent_suffix (route after : List (Endpoint g))
    (terminal : Endpoint g) {a b : Context}
    (labels : Labelling g (route++after) a b)
    (finish : route.getLast?=some terminal)
    (transparent : ∀ e f,(e,f)∈route.zip route.tail →
      ∃ w d,g.wire e=.inr (.inr (w,d)) ∧f=.inr (.inr (w,!d))) :
    Labelling g (terminal::after) a b := by
  induction route generalizing a with
  | nil => cases finish
  | cons e route ih =>
    cases route with
    | nil =>
      have equal : e=terminal := Option.some.inj finish
      subst e
      exact labels
    | cons f route =>
      obtain ⟨w,d,arrives,leaves⟩ := transparent e f (by simp)
      cases labels with
      | cons turn rest =>
        rw [arrives,leaves] at turn
        cases turn
        exact ih rest (by simpa only [List.getLast?_cons_cons] using finish)
          (by intro x y pair; exact transparent x y (List.mem_cons_of_mem _ pair))

/-- The two boundaries of this literal corridor occurrence share the same
actual context. Prefix and suffix belong to the supplied whole assignment,
including repeated occurrences of the same physical edge. -/
theorem Labelling.corridor_seams (route : TransparentCorridor g)
    (before after : List (Endpoint g)) {a b : Context}
    (labels : Labelling g ((before++route.edges)++after) a b) :
    ∃ middle,Labelling g (before++[.inl route.first]) a middle ∧
      Labelling g ((g.wire (.inl route.last))::after) middle b := by
  cases shape : route.edges with
  | nil => have impossible := route.start; rw [shape] at impossible; cases impossible
  | cons head rest =>
    have equal : head=.inl route.first := Option.some.inj (by simpa only [shape] using route.start)
    have whole : Labelling g (before++(.inl route.first)::(rest++after)) a b := by
      simpa only [shape,equal,List.append_assoc,List.cons_append] using labels
    obtain ⟨middle,pref,suff⟩ := whole.split_segment
    have segment : Labelling g (route.edges++after) middle b := by
      simpa only [shape,equal,List.cons_append] using suff
    exact ⟨middle,pref,segment.transparent_suffix route.edges after _ route.finish route.transparent⟩

/-- When the supplied occurrence starts the whole path, its shared seam is
the original input; this does not treat a later visit as the first visit. -/
theorem Labelling.corridor_initial_seam (route : TransparentCorridor g)
    (after : List (Endpoint g)) {a b : Context}
    (labels : Labelling g (route.edges++after) a b) :
    Labelling g ((g.wire (.inl route.last))::after) a b :=
  labels.transparent_suffix route.edges after _ route.finish route.transparent
end
end Lamping.AG
