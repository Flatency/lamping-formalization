import Lamping.Lamping.OutsideControlWriterSuffix
namespace Lamping.AG
open Graph
section
variable {s : Schema} {K B W V : Type}
variable [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))

/-- The literal final writer of an already supplied rooted path to the passive
principal. It uses the caller's selected finite principal route and the SAME
input, seam and final assignment. No partial path is completed. -/
theorem PathSite.rooted_control_writer_suffix
    (principal : SiteActionPrincipal site)
    {old : List (Endpoint site.net)} {a b : Context}
    (labels : Labelling site.net old a b) (root : B)
    (first : old.head?=some (.inr (.inl root)))
    (finish : old.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩))) :
    ∃ (pre : List (Endpoint site.net)) (q : Aux s.active) (middle : Context),
      old=pre++principal.edges ∧
      pre.head?=some (.inr (.inl root)) ∧
      pre.getLast?=some (site.net.wire (.inl ⟨.inr (.inl ()),.inr q⟩)) ∧
      Labelling site.net pre a middle ∧
      Traversal s.low (.op s.active) (.inr q) (.inl ()) middle b := by
  exact site.outside_control_writer_suffix principal labels
    (.inr (.inl (.inl root))) first finish
end
end Lamping.AG
