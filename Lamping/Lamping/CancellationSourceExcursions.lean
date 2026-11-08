import Lamping.Lamping.CancellationReverseBlocks
import Lamping.Lamping.CancellationUniformRoutes
namespace Lamping.AG
open Graph
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))

/-- Every actual proper-ended old path entering a cancellation frontier has
an already present, strictly shorter suffix at the paired frontier. Its
context is exactly the original entry context. This is finite decomposition. -/
theorem PathSite.cancellation_typed_exit (cancel : IsCancellation s) (f : s.Frontier)
    {es : List (Endpoint site.net)} {a b : Context}
    (labels : Labelling site.net es a b) (typed : ∃ k,accessKind site.net es=some k)
    (first : es.head?=some (site.net.wire (site.outsideEnd (.inr (.inl (.inr f)))))) :
    ∃ (front rest : List (Endpoint site.net)),
      es=front++(site.outsideEnd (.inr (.inl (.inr (cancellationMate s f)))))::rest ∧
      front≠[] ∧
      Labelling site.net ((site.outsideEnd (.inr (.inl (.inr (cancellationMate s f)))))::rest) a b := by
  cases cancel with
  | fan i =>
    cases f with
    | inl branch =>
      obtain ⟨pre,rest,split,tail⟩ := site.fan_cancel_typed_block branch labels typed first
      refine ⟨site.net.wire (.inl ⟨.inr (.inl ()),.inr branch⟩)::
        (pre++[site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)]),rest,?_,by simp,tail⟩
      simpa only [List.cons_append,List.append_assoc,List.singleton_append] using split
    | inr branch =>
      obtain ⟨pre,rest,split,tail⟩ := site.fan_cancel_reverse_typed_block branch labels typed first
      refine ⟨site.net.wire (.inl ⟨.inr (.inr ()),.inr branch⟩)::
        (pre++[site.net.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)]),rest,?_,by simp,tail⟩
      simpa only [List.cons_append,List.append_assoc,List.singleton_append] using split
  | cro i =>
    cases f with
    | inl branch =>
      obtain ⟨pre,rest,split,tail⟩ := site.cro_cancel_typed_block branch labels typed first
      refine ⟨site.net.wire (.inl ⟨.inr (.inl ()),.inr branch⟩)::
        (pre++[site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)]),rest,?_,by simp,tail⟩
      simpa only [List.cons_append,List.append_assoc,List.singleton_append] using split
    | inr branch =>
      obtain ⟨pre,rest,split,tail⟩ := site.cro_cancel_reverse_typed_block branch labels typed first
      refine ⟨site.net.wire (.inl ⟨.inr (.inr ()),.inr branch⟩)::
        (pre++[site.net.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)]),rest,?_,by simp,tail⟩
      simpa only [List.cons_append,List.append_assoc,List.singleton_append] using split
  | bra i =>
    cases f with
    | inl branch =>
      obtain ⟨pre,rest,split,tail⟩ := site.bra_cancel_typed_block branch labels typed first
      refine ⟨site.net.wire (.inl ⟨.inr (.inl ()),.inr branch⟩)::
        (pre++[site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)]),rest,?_,by simp,tail⟩
      simpa only [List.cons_append,List.append_assoc,List.singleton_append] using split
    | inr branch =>
      obtain ⟨pre,rest,split,tail⟩ := site.bra_cancel_reverse_typed_block branch labels typed first
      refine ⟨site.net.wire (.inl ⟨.inr (.inr ()),.inr branch⟩)::
        (pre++[site.net.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)]),rest,?_,by simp,tail⟩
      simpa only [List.cons_append,List.append_assoc,List.singleton_append] using split
end
end Lamping.AG
