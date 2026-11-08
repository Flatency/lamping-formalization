import Lamping.Lamping.CancellationCanonicalResidual
import Lamping.Lamping.ActionPrincipalInternal

namespace Lamping.AG
open Graph
section
variable {s : Schema} {K B W V : Type}
variable [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed

private theorem outside_injective : Function.Injective site.outsideEnd := by
  intro e f same
  let split := fragmentEnd (B:=B) (W:=W) site.net.label (pathPartition s V)
  have mapped := congrArg split same
  change split (split.invFun (.inl e))=split (split.invFun (.inl f)) at mapped
  simp only [split.right_inv] at mapped
  exact Sum.inl.inj mapped

def cancellationFrontRoute (principal : SiteActionPrincipal site) (f : s.Frontier) : List (Endpoint site.net) :=
  match f with
  | .inl _ => principal.edges
  | .inr _ => reverseEdges principal.edges

private theorem restore_last {α : Type} {xs : List α} {last : α} (ending : xs.getLast?=some last) :
    xs.dropLast++[last]=xs := by
  obtain ⟨before,split⟩ := List.getLast?_eq_some_iff.mp ending
  rw [split,List.dropLast_concat]

theorem cancellation_fronts_literal (principal : SiteActionPrincipal site) (f : s.Frontier) :
    site.cancellation_canonical_fronts principal.edges f=
      site.outsideEnd ((cut).wire (.inr (.inl (.inr f))))::cancellationFrontRoute site principal f := by
  rw [←site.outsideEnd_wire]
  cases f with
  | inl branch =>
    change _::(principal.edges.dropLast++[_])=_::principal.edges
    rw [restore_last principal.last]
    congr 1
  | inr branch =>
    change _::((reverseEdges principal.edges).dropLast++[_])=_::reverseEdges principal.edges
    apply congrArg (List.cons _)
    apply restore_last
    simp only [reverseEdges,List.getLast?_map,List.getLast?_reverse,principal.first,Option.map_some]

theorem cancellation_front_route_nonempty (principal : SiteActionPrincipal site) (f : s.Frontier) :
    cancellationFrontRoute site principal f≠[] := by
  cases f with
  | inl branch =>
    intro empty
    have first := principal.first
    change principal.edges=[] at empty
    rw [empty] at first
    cases first
  | inr branch =>
    intro empty
    have first : (reverseEdges principal.edges).head?=some (.inl ⟨.inr (.inr ()),.inl ()⟩) := by
      simp only [reverseEdges,List.head?_map,List.head?_reverse,principal.last,Option.map_some,Pairing.involutive]
    change reverseEdges principal.edges=[] at empty
    rw [empty] at first
    cases first

theorem cancellation_front_route_internal (principal : SiteActionPrincipal site) (f : s.Frontier) :
    ∀ e∈cancellationFrontRoute site principal f,∃ i,e=site.internalEnd i := by
  cases f with
  | inl branch => exact principal.internal_segments site
  | inr branch => exact principal.reverse_internal_segments site

theorem cancellation_front_tail_internal (principal : SiteActionPrincipal site) (f : s.Frontier) :
    ∀ e∈(site.cancellation_canonical_fronts principal.edges f).tail,∃ i,e=site.internalEnd i := by
  rw [cancellation_fronts_literal]
  exact cancellation_front_route_internal site principal f

theorem cancellation_front_tail_outside_disjoint (principal : SiteActionPrincipal site) (f : s.Frontier)
    (e : Endpoint site.net) (member : e∈(site.cancellation_canonical_fronts principal.edges f).tail)
    (outside : Endpoint cut) : e≠site.outsideEnd outside := by
  obtain ⟨i,inside⟩ := cancellation_front_tail_internal site principal f e member
  exact fun same=>site.internal_outside_ne i outside (inside.symm.trans same)

theorem cancellation_front_heads_injective (principal : SiteActionPrincipal site) {f g : s.Frontier}
    (same : (site.cancellation_canonical_fronts principal.edges f).head?=
      (site.cancellation_canonical_fronts principal.edges g).head?) : f=g := by
  rw [cancellation_fronts_literal,cancellation_fronts_literal] at same
  have outside := outside_injective site (Option.some.inj same)
  have frontiers := congrArg (cut).wire outside
  simp only [Pairing.involutive] at frontiers
  exact Sum.inr.inj (Sum.inl.inj (Sum.inr.inj frontiers))

/-- The entry is an actual outside endpoint, and the next old segment is
internal. This literal delimiter is derived from the supplied route. -/
theorem cancellation_front_internal_delimiter (principal : SiteActionPrincipal site) (f : s.Frontier) :
    ∃ inside tail,site.cancellation_canonical_fronts principal.edges f=
      site.outsideEnd ((cut).wire (.inr (.inl (.inr f))))::inside::tail ∧
      ∀ outside : Endpoint cut,inside≠site.outsideEnd outside := by
  cases shape : cancellationFrontRoute site principal f with
  | nil => exact False.elim (cancellation_front_route_nonempty site principal f shape)
  | cons inside tail =>
    refine ⟨inside,tail,?_,?_⟩
    · rw [cancellation_fronts_literal,shape]
    · obtain ⟨i,internal⟩ := cancellation_front_route_internal site principal f inside
        (by rw [shape]; simp)
      intro outside same
      exact site.internal_outside_ne i outside (internal.symm.trans same)

private theorem internal_word_empty (cancel : IsCancellation s) (i : Bool⊕(V×Bool)) :
    arrivalWord site.net (site.internalEnd i)=[] := by
  rcases i with b|⟨v,d⟩
  · cases cancel <;> cases b <;> rfl
  · rfl

/-- Only the internal tail emits no syntax tokens. The entry itself may be
a genuine proper departure, so no all-front token erasure is asserted. -/
theorem cancellation_front_tail_tokens_empty (cancel : IsCancellation s)
    (principal : SiteActionPrincipal site) (f : s.Frontier) :
    ∀ e∈(site.cancellation_canonical_fronts principal.edges f).tail,arrivalWord site.net e=[] := by
  intro e member
  obtain ⟨i,internal⟩ := cancellation_front_tail_internal site principal f e member
  rw [internal]
  exact internal_word_empty site cancel i

private theorem internal_single_untyped (cancel : IsCancellation s) (i : Bool⊕(V×Bool)) :
    accessKind site.net [site.internalEnd i]=none := by
  simp only [accessKind,List.getLast?_singleton,Option.bind_some]
  rw [site.internalEnd_wire]
  rcases site.internal i with b|⟨v,d⟩
  · cases cancel <;> cases b <;> rfl
  · rfl

private theorem frontier_entry_untyped (cancel : IsCancellation s) (f : s.Frontier) :
    accessKind site.net [site.outsideEnd ((cut).wire (.inr (.inl (.inr f))))]=none := by
  rw [←site.outsideEnd_wire]
  simp only [accessKind,List.getLast?_singleton,Option.bind_some]
  rw [Pairing.involutive]
  cases cancel <;> cases f <;> rfl

theorem cancellation_front_segments_untyped (cancel : IsCancellation s)
    (principal : SiteActionPrincipal site) (f : s.Frontier) :
    ∀ e∈site.cancellation_canonical_fronts principal.edges f,accessKind site.net [e]=none := by
  rw [cancellation_fronts_literal]
  intro e member
  rcases List.mem_cons.mp member with equal | member
  · subst e
    exact frontier_entry_untyped site cancel f
  · obtain ⟨i,inside⟩ := cancellation_front_route_internal site principal f e member
    rw [inside]
    exact internal_single_untyped site cancel i
end
end Lamping.AG
