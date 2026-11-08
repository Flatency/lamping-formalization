import Lamping.Lamping.SourcePathSiteLift
import Lamping.Lamping.ExpandedIndependence
namespace Lamping.AG
open Graph
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))

/-- Only the actual ordered principal component and its transparent physical
turns. There are no labels, replay conclusions, or soundness fields. -/
structure SiteActionPrincipal where
  edges : List (Endpoint site.net)
  first : edges.head?=some (.inl ⟨.inr (.inl ()),.inl ()⟩)
  last : edges.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩))
  transparent : ∀ e f,(e,f)∈edges.zip edges.tail →
    ∃ w d,site.net.wire e=.inr (.inr (w,d)) ∧f=.inr (.inr (w,!d))

theorem PathSite.actionPrincipal_exists : Nonempty (SiteActionPrincipal site) := by
  obtain ⟨edges,first,last,transparent⟩ := site.principal_route
  exact ⟨⟨edges,first,last,transparent⟩⟩

def SiteActionPrincipal.crossing (principal : SiteActionPrincipal site) (p : Aux s.active) (q : Aux s.passive) :
    List (Endpoint site.net) :=
  site.net.wire (.inl ⟨.inr (.inl ()),.inr p⟩)::(principal.edges++[.inl ⟨.inr (.inr ()),.inr q⟩])

def PathSite.passiveCanonical (p q : Aux s.passive) : List (Endpoint site.net) :=
  [site.net.wire (.inl ⟨.inr (.inr ()),.inr p⟩),.inl ⟨.inr (.inr ()),.inr q⟩]

private theorem node_rule {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} {node : N} {p q : Port (g.label node).sort} {a b : Context}
    (turn : LabelledTurn g (.inl ⟨node,p⟩) (.inl ⟨node,q⟩) a b) :
    Traversal (g.label node).index (g.label node).sort p q a b := by
  cases turn with | node node p q rule => exact rule

/-- All assignments on this same physical crossing correspond to exactly
the two primitive LHS passages; transparent subdivisions carry no change. -/
theorem SiteActionPrincipal.crossing_labels_iff (principal : SiteActionPrincipal site)
    (p : Aux s.active) (q : Aux s.passive) (a b : Context) :
    Labelling site.net (principal.crossing site p q) a b ↔
      Labelling s.left (leftRoute s.active s.passive s.low s.high p q) a b := by
  constructor
  · intro labels
    have nonempty : principal.edges≠[] := by
      intro empty
      have first := principal.first
      rw [empty] at first
      cases first
    obtain ⟨routeTail,routeSplit⟩ := List.head?_eq_some_iff.mp principal.first
    change Labelling site.net (site.net.wire (.inl ⟨.inr (.inl ()),.inr p⟩)::
      (principal.edges++[.inl ⟨.inr (.inr ()),.inr q⟩])) a b at labels
    rw [routeSplit,List.cons_append] at labels
    cases labels with
    | @cons _ _ _ _ middle _ first after =>
      rw [Pairing.involutive] at first
      have active := node_rule first
      have after' : Labelling site.net (principal.edges++[.inl ⟨.inr (.inr ()),.inr q⟩]) middle b := by
        rw [routeSplit]; exact after
      obtain ⟨routePre,routeEnd⟩ := List.getLast?_eq_some_iff.mp principal.last
      rw [routeEnd,List.append_assoc] at after'
      obtain ⟨seam,routeLabels,passiveLabels⟩ := after'.split_segment
      have constant := transparent_route_labelling site.net principal.edges nonempty principal.transparent middle
      rw [routeEnd] at constant
      have seamEq := routeLabels.output_unique constant
      rw [seamEq] at passiveLabels
      cases passiveLabels with
      | cons passive finish =>
        rw [Pairing.involutive] at passive
        cases finish
        exact (leftRoute_labeling_iff s.active s.passive s.low s.high p q a b).mpr
          ⟨middle,active,node_rule passive⟩
  · intro labels
    obtain ⟨middle,first,second⟩ := (leftRoute_labeling_iff s.active s.passive s.low s.high p q a b).mp labels
    exact principal_crossing_labels site.net (.inr (.inl ())) (.inr (.inr ()))
      (.inr p) (.inl ()) (.inl ()) (.inr q) principal.edges principal.first principal.last principal.transparent first second

theorem PathSite.passiveCanonical_labels_iff (p q : Aux s.passive) (a b : Context) :
    Labelling site.net (site.passiveCanonical p q) a b ↔
      Labelling s.left [.inr (.inl (.inr p)),.inl ⟨.inr (),.inr q⟩] a b := by
  constructor
  · intro labels
    cases labels with
    | cons first finish =>
      rw [Pairing.involutive] at first
      cases finish
      have rule := node_rule (g:=site.net) first
      exact .cons (LabelledTurn.node (g:=s.left) (.inr ()) (.inr p) (.inr q) rule) (.single _ _)
  · intro labels
    cases labels with
    | cons first finish =>
      cases finish
      have actual := node_rule first
      apply Labelling.cons
      · rw [Pairing.involutive]
        exact LabelledTurn.node (g:=site.net) (.inr (.inr ())) (.inr p) (.inr q) actual
      · exact .single _ _

theorem reverseEdges_involutive {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} (es : List (Endpoint g)) : reverseEdges (reverseEdges es)=es := by
  simp [reverseEdges,List.map_reverse,List.map_map,Function.comp_def,Pairing.involutive]

theorem SiteActionPrincipal.reverse_crossing_labels_iff (principal : SiteActionPrincipal site)
    (p : Aux s.active) (q : Aux s.passive) (a b : Context) :
    Labelling site.net (reverseEdges (principal.crossing site p q)) a b ↔
      Labelling s.left (reverseEdges (leftRoute s.active s.passive s.low s.high p q)) a b := by
  constructor
  · intro labels
    have actual := labels.reverse
    rw [reverseEdges_involutive] at actual
    exact ((principal.crossing_labels_iff site p q b a).mp actual).reverse
  · intro labels
    have localLabels := labels.reverse
    rw [reverseEdges_involutive] at localLabels
    exact ((principal.crossing_labels_iff site p q b a).mpr localLabels).reverse
end
end Lamping.AG


