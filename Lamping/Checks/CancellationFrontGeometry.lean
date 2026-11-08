import Lamping.Lamping.CancellationFrontGeometry
import Lamping.Checks.FamilyRepresentation

namespace Lamping.Checks.CancellationFrontGeometry
open AG Graph
private abbrev site := CancellationPrefixFixture.geometrySite
private abbrev principal := CancellationPrefixFixture.geometryPrincipal
private abbrev cut := cutFragment site.net (pathPartition (.fanCancel 1) Empty) site.closed

/-- The real fan cancellation has one supplied principal route. Every
frontier is separated from its nonempty internal continuation. -/
theorem actual_fixed_front_delimiters :
    ∀ f : (Schema.fanCancel 1).Frontier,
      ∃ inside tail,site.cancellation_canonical_fronts principal.edges f=
        site.outsideEnd (cut.wire (.inr (.inl (.inr f))))::inside::tail ∧
        ∀ outside : Endpoint cut,inside≠site.outsideEnd outside :=
  cancellation_front_internal_delimiter site principal

theorem actual_frontier_head_reflection (left right : (Schema.fanCancel 1).Frontier)
    (same : (site.cancellation_canonical_fronts principal.edges left).head?=
      (site.cancellation_canonical_fronts principal.edges right).head?) : left=right :=
  cancellation_front_heads_injective site principal same

/-- Both frontier directions are covered, including the side wired to the
kept lambda context. None of the prefix segments is a proper terminal. -/
theorem actual_all_fronts_untyped :
    ∀ (f : (Schema.fanCancel 1).Frontier) e,
      e∈site.cancellation_canonical_fronts principal.edges f →accessKind site.net [e]=none :=
  cancellation_front_segments_untyped site (.fan 1) principal

theorem actual_internal_tail_has_no_syntax_tokens :
    ∀ (f : (Schema.fanCancel 1).Frontier) e,
      e∈(site.cancellation_canonical_fronts principal.edges f).tail →arrivalWord site.net e=[] :=
  cancellation_front_tail_tokens_empty site (.fan 1) principal

/-- The principal has not been reselected by the geometry lemmas. -/
theorem actual_given_principal_is_singleton : principal.edges.length=1 := rfl

#print axioms cancellation_fronts_literal
#print axioms cancellation_front_internal_delimiter
#print axioms cancellation_front_heads_injective
#print axioms cancellation_front_segments_untyped
#print axioms cancellation_front_tail_tokens_empty
#print axioms actual_fixed_front_delimiters
#print axioms actual_all_fronts_untyped
end Lamping.Checks.CancellationFrontGeometry
