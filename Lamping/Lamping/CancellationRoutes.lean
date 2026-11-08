import Lamping.Lamping.PrincipalCrossings
import Lamping.Lamping.InitialOffsets
import Lamping.Lamping.PathSiteBetaAncestor
namespace Lamping.AG
open Graph

/-- Exactly the three standard equal-index control cancellations. -/
inductive IsCancellation : Schema → Prop
  | fan (i : Nat) : IsCancellation (.fanCancel i)
  | cro (i : Nat) : IsCancellation (.croCancel i)
  | bra (i : Nat) : IsCancellation (.braCancel i)

def cancellationMate : (s : Schema) → s.Frontier → s.Frontier
  | .fanCancel _,f => f.swap
  | .croCancel _,f => f.swap
  | .braCancel _,f => f.swap
  | _,f => f

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature}

theorem PathSite.fan_cancel_route {i : Nat}
    (site : PathSite (.fanCancel i) kept (B:=B) (W:=W) (V:=V)) (branch : Bool) (a : Context) :
    ∃ es : List (Endpoint site.net),
      es.head?=some (site.net.wire (.inl ⟨.inr (.inl ()),.inr branch⟩)) ∧
      es.getLast?=some (.inl ⟨.inr (.inr ()),.inr branch⟩) ∧Labelling site.net es a a := by
  obtain ⟨route,start,finish,transparent⟩ := site.principal_route
  have rule := InitialOffsets.Event.apply_rel (.fan i branch) a
  obtain ⟨labels,_⟩ := principal_crossing site.net (.inr (.inl ())) (.inr (.inr ()))
    (.inr branch) (.inl ()) (.inl ()) (.inr branch) route start finish transparent
    (.direct rule) (.inverse rule) True.intro True.intro
  refine ⟨_,rfl,?_,labels⟩
  simp only [List.getLast?_append,List.getLast?_cons,List.getLast?_nil,Option.some_or]
  rfl

theorem PathSite.cro_cancel_route {i : Nat}
    (site : PathSite (.croCancel i) kept (B:=B) (W:=W) (V:=V)) (a : Context) :
    ∃ es : List (Endpoint site.net),
      es.head?=some (site.net.wire (.inl ⟨.inr (.inl ()),.inr ()⟩)) ∧
      es.getLast?=some (.inl ⟨.inr (.inr ()),.inr ()⟩) ∧Labelling site.net es a a := by
  obtain ⟨route,start,finish,transparent⟩ := site.principal_route
  have rule := InitialOffsets.Event.apply_rel (.cro i) a
  obtain ⟨labels,_⟩ := principal_crossing site.net (.inr (.inl ())) (.inr (.inr ()))
    (.inr ()) (.inl ()) (.inl ()) (.inr ()) route start finish transparent
    (.direct rule) (.inverse rule) True.intro True.intro
  refine ⟨_,rfl,?_,labels⟩
  simp only [List.getLast?_append,List.getLast?_cons,List.getLast?_nil,Option.some_or]
  rfl

theorem PathSite.bra_cancel_route {i : Nat}
    (site : PathSite (.braCancel i) kept (B:=B) (W:=W) (V:=V)) (a : Context) :
    ∃ es : List (Endpoint site.net),
      es.head?=some (site.net.wire (.inl ⟨.inr (.inl ()),.inr ()⟩)) ∧
      es.getLast?=some (.inl ⟨.inr (.inr ()),.inr ()⟩) ∧Labelling site.net es a a := by
  obtain ⟨route,start,finish,transparent⟩ := site.principal_route
  have rule := InitialOffsets.Event.apply_rel (.bra i) a
  obtain ⟨labels,_⟩ := principal_crossing site.net (.inr (.inl ())) (.inr (.inr ()))
    (.inr ()) (.inl ()) (.inl ()) (.inr ()) route start finish transparent
    (.direct rule) (.inverse rule) True.intro True.intro
  refine ⟨_,rfl,?_,labels⟩
  simp only [List.getLast?_append,List.getLast?_cons,List.getLast?_nil,Option.some_or]
  rfl

private theorem reverse_route {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    (g : Net signature N B W) (x y : Endpoint g) (a : Context)
    (path : ∃ es : List (Endpoint g),es.head?=some (g.wire x) ∧
      es.getLast?=some y ∧Labelling g es a a) :
    ∃ es : List (Endpoint g),es.head?=some (g.wire y) ∧
      es.getLast?=some x ∧Labelling g es a a := by
  obtain ⟨es,start,finish,labels⟩ := path
  refine ⟨reverseEdges es,?_,?_,labels.reverse⟩
  · simp only [reverseEdges,List.head?_map,List.head?_reverse,finish,Option.map_some]
  · simp only [reverseEdges,List.getLast?_map,List.getLast?_reverse,start,Option.map_some,Pairing.involutive]

/-- Both frontier directions of every actual cancellation have a source
route for every supplied context, retaining every principal subdivision. -/
theorem PathSite.cancellation_route {s : Schema} (cancel : IsCancellation s)
    (site : PathSite s kept (B:=B) (W:=W) (V:=V)) (f : s.Frontier) (a : Context) :
    ∃ es : List (Endpoint site.net),
      es.head?=some (site.net.wire (site.outsideEnd (.inr (.inl (.inr f))))) ∧
      es.getLast?=some (site.outsideEnd (.inr (.inl (.inr (cancellationMate s f))))) ∧
      Labelling site.net es a a := by
  cases cancel with
  | fan i =>
    cases f with
    | inl branch => exact site.fan_cancel_route branch a
    | inr branch => exact reverse_route site.net _ _ a (site.fan_cancel_route branch a)
  | cro i =>
    cases f with
    | inl u => cases u; exact site.cro_cancel_route a
    | inr u => cases u; exact reverse_route site.net _ _ a (site.cro_cancel_route a)
  | bra i =>
    cases f with
    | inl u => cases u; exact site.bra_cancel_route a
    | inr u => cases u; exact reverse_route site.net _ _ a (site.bra_cancel_route a)
end
end Lamping.AG


