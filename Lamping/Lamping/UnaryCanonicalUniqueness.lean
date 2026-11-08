import Lamping.Lamping.ActionCanonicalUniqueness
namespace Lamping.AG
open Graph
section
variable {s : Schema} {k : Nat}
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V)) (single : Bij Unit (Aux s.active))
/-- For the same actual principal component, a unary canonical old local
route fixes the RHS route. This does not assert whole-block injectivity. -/
theorem UnaryCanonicalLocal.fixed_target_unique
    {principal : SiteActionPrincipal site} {first second old other}
    (left : UnaryCanonicalLocal site single (k:=k) principal first old)
    (right : UnaryCanonicalLocal site single (k:=k) principal second other) (same : old=other) : first=second := by
  have nonempty : principal.edges≠[] := by intro empty; have h:=principal.first; rw [empty] at h; cases h
  have wireEq (e f : Endpoint site.net) : site.net.wire e=site.net.wire f ↔e=f := by
    constructor
    · intro same
      have actual := congrArg site.net.wire.mate same
      simpa only [Pairing.involutive] using actual
    · exact congrArg site.net.wire.mate
  cases left <;> cases right <;>
    simp_all [SiteActionPrincipal.crossing,PathSite.passiveCanonical,reverseEdges,
      unaryCrossEdges,unaryPassiveEdges]
  case backward.backward =>
    have qs := Sum.inr.inj same
    cases qs
    rfl
  case backward.passive =>
    have lengths := congrArg List.length same.2
    simp only [List.length_append,List.length_reverse,List.length_map,List.length_cons,List.length_nil] at lengths
    exact nonempty (List.length_eq_zero_iff.mp (by omega))
  case passive.backward =>
    have lengths := congrArg List.length same.2
    simp only [List.length_append,List.length_reverse,List.length_map,List.length_cons,List.length_nil] at lengths
    exact nonempty (List.length_eq_zero_iff.mp (by omega))
end
end Lamping.AG