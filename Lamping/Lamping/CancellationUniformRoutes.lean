import Lamping.Lamping.CancellationRoutes
import Lamping.Lamping.PathLabelDeterminism
namespace Lamping.AG
open Graph
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature}

theorem PathSite.fan_cancel_uniform_route {i : Nat}
    (site : PathSite (.fanCancel i) kept (B:=B) (W:=W) (V:=V)) (branch : Bool) :
    ∃ route : List (Endpoint site.net),
      route.head?=some (site.net.wire (.inl ⟨.inr (.inl ()),.inr branch⟩)) ∧
      route.getLast?=some (.inl ⟨.inr (.inr ()),.inr branch⟩) ∧
      ∀ a,Labelling site.net route a a := by
  obtain ⟨principal,first,last,turns⟩ := site.principal_route
  refine ⟨site.net.wire (.inl ⟨.inr (.inl ()),.inr branch⟩)::
    (principal++[.inl ⟨.inr (.inr ()),.inr branch⟩]),rfl,?_,?_⟩
  · simp only [List.getLast?_cons,List.getLast?_append,List.getLast?_nil,Option.some_or,Option.getD_none,Option.getD_some]
  · intro a
    have rule := InitialOffsets.Event.apply_rel (.fan i branch) a
    exact principal_crossing_labels site.net (.inr (.inl ())) (.inr (.inr ())) (.inr branch) (.inl ()) (.inl ()) (.inr branch)
      principal first last turns (.direct rule) (.inverse rule)

theorem PathSite.cro_cancel_uniform_route {i : Nat}
    (site : PathSite (.croCancel i) kept (B:=B) (W:=W) (V:=V)) :
    ∃ route : List (Endpoint site.net),
      route.head?=some (site.net.wire (.inl ⟨.inr (.inl ()),.inr ()⟩)) ∧
      route.getLast?=some (.inl ⟨.inr (.inr ()),.inr ()⟩) ∧
      ∀ a,Labelling site.net route a a := by
  obtain ⟨principal,first,last,turns⟩ := site.principal_route
  refine ⟨site.net.wire (.inl ⟨.inr (.inl ()),.inr ()⟩)::
    (principal++[.inl ⟨.inr (.inr ()),.inr ()⟩]),rfl,?_,?_⟩
  · simp only [List.getLast?_cons,List.getLast?_append,List.getLast?_nil,Option.some_or,Option.getD_none,Option.getD_some]
  · intro a
    have rule := InitialOffsets.Event.apply_rel (.cro i) a
    exact principal_crossing_labels site.net (.inr (.inl ())) (.inr (.inr ())) (.inr ()) (.inl ()) (.inl ()) (.inr ())
      principal first last turns (.direct rule) (.inverse rule)

theorem PathSite.bra_cancel_uniform_route {i : Nat}
    (site : PathSite (.braCancel i) kept (B:=B) (W:=W) (V:=V)) :
    ∃ route : List (Endpoint site.net),
      route.head?=some (site.net.wire (.inl ⟨.inr (.inl ()),.inr ()⟩)) ∧
      route.getLast?=some (.inl ⟨.inr (.inr ()),.inr ()⟩) ∧
      ∀ a,Labelling site.net route a a := by
  obtain ⟨principal,first,last,turns⟩ := site.principal_route
  refine ⟨site.net.wire (.inl ⟨.inr (.inl ()),.inr ()⟩)::
    (principal++[.inl ⟨.inr (.inr ()),.inr ()⟩]),rfl,?_,?_⟩
  · simp only [List.getLast?_cons,List.getLast?_append,List.getLast?_nil,Option.some_or,Option.getD_none,Option.getD_some]
  · intro a
    have rule := InitialOffsets.Event.apply_rel (.bra i) a
    exact principal_crossing_labels site.net (.inr (.inl ())) (.inr (.inr ())) (.inr ()) (.inl ()) (.inl ()) (.inr ())
      principal first last turns (.direct rule) (.inverse rule)

private theorem reverse_uniform {N D U : Type} [FiniteNames N] [FiniteNames D] [FiniteNames U]
    (g : Net signature N D U) (x y : Endpoint g)
    (given : ∃ route : List (Endpoint g),route.head?=some (g.wire x) ∧
      route.getLast?=some y ∧∀ a,Labelling g route a a) :
    ∃ route : List (Endpoint g),route.head?=some (g.wire y) ∧
      route.getLast?=some x ∧∀ a,Labelling g route a a := by
  obtain ⟨route,first,last,labels⟩ := given
  refine ⟨reverseEdges route,?_,?_,fun a => (labels a).reverse⟩
  · simp only [reverseEdges,List.head?_map,List.head?_reverse,last,Option.map_some]
  · simp only [reverseEdges,List.getLast?_map,List.getLast?_reverse,first,Option.map_some,Pairing.involutive]

/-- One physical cancellation route is selected before any context is given.
Both frontier directions and every actual principal subdivision are retained. -/
theorem PathSite.cancellation_uniform_route {s : Schema} (cancel : IsCancellation s)
    (site : PathSite s kept (B:=B) (W:=W) (V:=V)) (f : s.Frontier) :
    ∃ route : List (Endpoint site.net),
      route.head?=some (site.net.wire (site.outsideEnd (.inr (.inl (.inr f))))) ∧
      route.getLast?=some (site.outsideEnd (.inr (.inl (.inr (cancellationMate s f))))) ∧
      ∀ a,Labelling site.net route a a := by
  cases cancel with
  | fan i =>
    cases f with
    | inl branch => exact site.fan_cancel_uniform_route branch
    | inr branch => exact reverse_uniform site.net _ _ (site.fan_cancel_uniform_route branch)
  | cro i =>
    cases f with
    | inl u => cases u; exact site.cro_cancel_uniform_route
    | inr u => cases u; exact reverse_uniform site.net _ _ site.cro_cancel_uniform_route
  | bra i =>
    cases f with
    | inl u => cases u; exact site.bra_cancel_uniform_route
    | inr u => cases u; exact reverse_uniform site.net _ _ site.bra_cancel_uniform_route

/-- Exact same-context semantics of one fixed actual cancellation block.
This does not assert replay for an arbitrary old WireBlockResidual front. -/
theorem PathSite.cancellation_uniform_replay {s : Schema} (cancel : IsCancellation s)
    (site : PathSite s kept (B:=B) (W:=W) (V:=V)) (f : s.Frontier) :
    ∃ route : List (Endpoint site.net),
      route.head?=some (site.net.wire (site.outsideEnd (.inr (.inl (.inr f))))) ∧
      route.getLast?=some (site.outsideEnd (.inr (.inl (.inr (cancellationMate s f))))) ∧
      ([.inr (.inl f)] : List (Endpoint s.right.net)).getLast?=
        some (s.right.net.wire (.inr (.inl (cancellationMate s f)))) ∧
      ∀ a b,Labelling site.net route a b ↔ Labelling s.right.net [.inr (.inl f)] a b := by
  obtain ⟨route,first,last,uniform⟩ := site.cancellation_uniform_route cancel f
  refine ⟨route,first,last,?_,?_⟩
  · cases cancel <;> cases f <;> rfl
  · intro a b
    constructor
    · intro labels
      have same := labels.output_unique (uniform a)
      subst b
      exact .single _ _
    · intro labels
      cases labels
      exact uniform a
end
end Lamping.AG

