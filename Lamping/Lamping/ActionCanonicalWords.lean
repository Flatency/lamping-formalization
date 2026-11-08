import Lamping.Lamping.ActionCanonicalResidual
import Lamping.Lamping.CorridorReverse
import Lamping.Lamping.InitialAccessWords
namespace Lamping.AG
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

/-- All departures after the first in a supplied transparent route are W
ends. Its full token list is precisely that first departure's tokens. -/
theorem transparent_access_tokens (es : List (Endpoint g)) (first : Endpoint g)
    (head : es.head?=some first)
    (transparent : ∀ e f,(e,f)∈es.zip es.tail →
      ∃ w d,g.wire e=.inr (.inr (w,d)) ∧f=.inr (.inr (w,!d))) :
    accessTokens g es=arrivalWord g first := by
  induction es generalizing first with
  | nil => cases head
  | cons e tail ih =>
    have same : e=first := Option.some.inj head
    subst first
    cases tail with
    | nil => simp only [accessTokens,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    | cons f tail =>
      obtain ⟨w,d,_arrives,leaves⟩ := transparent e f (by simp)
      have remaining := ih f rfl (by
        intro x y pair; exact transparent x y (List.mem_cons_of_mem _ pair))
      change arrivalWord g e++accessTokens g (f::tail)=_
      rw [remaining,leaves]
      exact List.append_nil _
end

section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))

theorem SiteActionPrincipal.tokens_empty (principal : SiteActionPrincipal site) (action : IsAction s) :
    accessTokens site.net principal.edges=[] := by
  rw [transparent_access_tokens principal.edges _ principal.first principal.transparent]
  cases action <;> rfl

/-- The initial outside departure is skipped; only the passive auxiliary
departure emits a syntax token on this actual canonical crossing. -/
theorem SiteActionPrincipal.crossing_word (principal : SiteActionPrincipal site)
    (action : IsAction s) (p : Aux s.active) (q : Aux s.passive) :
    accessWord site.net (principal.crossing site p q)=
      arrivalWord site.net (.inl ⟨.inr (.inr ()),.inr q⟩) := by
  change (principal.edges++[(.inl ⟨.inr (.inr ()),.inr q⟩ : Endpoint site.net)]).flatMap (arrivalWord site.net)=_
  rw [List.flatMap_append]
  have empty := principal.tokens_empty site action
  change principal.edges.flatMap (arrivalWord site.net)=[] at empty
  simp only [empty,List.nil_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]

theorem PathSite.passiveCanonical_word (p q : Aux s.passive) :
    accessWord site.net (site.passiveCanonical p q)=
      arrivalWord site.net (.inl ⟨.inr (.inr ()),.inr q⟩) := by
  simp only [PathSite.passiveCanonical,accessWord,List.flatMap_cons,List.flatMap_nil,List.append_nil]

/-- Reverse crossing emits the passive principal's token. It does not erase
that token by mistakenly treating every principal departure as transparent. -/
theorem SiteActionPrincipal.reverse_crossing_word (principal : SiteActionPrincipal site)
    (action : IsAction s) (p : Aux s.active) (q : Aux s.passive) :
    accessWord site.net (reverseEdges (principal.crossing site p q))=
      arrivalWord site.net (.inl ⟨.inr (.inr ()),.inl ()⟩) := by
  have split : reverseEdges (principal.crossing site p q)=
      site.net.wire (.inl ⟨.inr (.inr ()),.inr q⟩)::
      (reverseEdges principal.edges++[.inl ⟨.inr (.inl ()),.inr p⟩]) := by
    simp only [SiteActionPrincipal.crossing,reverseEdges,List.reverse_cons,List.reverse_append,
      List.reverse_nil,List.map_append,List.map_cons,List.map_nil,Pairing.involutive,
      List.nil_append,List.cons_append]
  have head : (reverseEdges principal.edges).head?=
      some (.inl ⟨.inr (.inr ()),.inl ()⟩) := by
    simp only [reverseEdges,List.head?_map,List.head?_reverse,principal.last,Option.map_some,Pairing.involutive]
  have reversed := transparent_access_tokens (reverseEdges principal.edges) _ head
    (transparent_reverse_turns principal.edges principal.transparent)
  have activeEmpty : arrivalWord site.net (.inl ⟨.inr (.inl ()),.inr p⟩)=[] := by
    cases action <;> rfl
  rw [split]
  change (reverseEdges principal.edges++[(.inl ⟨.inr (.inl ()),.inr p⟩ : Endpoint site.net)]).flatMap (arrivalWord site.net)=_
  rw [List.flatMap_append]
  change accessTokens site.net (reverseEdges principal.edges)++_=_
  simp only [reversed,List.flatMap_cons,List.flatMap_nil,List.append_nil,activeEmpty]
end
end Lamping.AG
