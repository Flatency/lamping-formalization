import Lamping.Lamping.ControlPrincipalSuffixes
import Lamping.Lamping.ActionPrincipalInternal
namespace Lamping.AG
open Graph
section
variable {s : Schema} {K B W V : Type}
variable [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed

private theorem reverse_append (xs ys : List (Endpoint site.net)) :
    reverseEdges (xs++ys)=reverseEdges ys++reverseEdges xs := by
  simp [reverseEdges,List.reverse_append,List.map_append]

/-- A supplied finite labelled path from a real outside endpoint to the
passive principal already contains its actual last active writer. The proof
reflects the given internal route backwards; it neither extends a path nor
requires a root access, and retains the exact original assignment. -/
theorem PathSite.outside_control_writer_suffix
    (principal : SiteActionPrincipal site)
    {old : List (Endpoint site.net)} {a b : Context}
    (labels : Labelling site.net old a b) (source : Endpoint cut)
    (first : old.head?=some (site.outsideEnd source))
    (finish : old.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩))) :
    ∃ (pre : List (Endpoint site.net)) (q : Aux s.active) (middle : Context),
      old=pre++principal.edges ∧
      pre.head?=some (site.outsideEnd source) ∧
      pre.getLast?=some (site.net.wire (.inl ⟨.inr (.inl ()),.inr q⟩)) ∧
      Labelling site.net pre a middle ∧
      Traversal s.low (.op s.active) (.inr q) (.inl ()) middle b := by
  let route := reverseEdges principal.edges
  have routeHead : route.head?=some (.inl ⟨.inr (.inr ()),.inl ()⟩) := by
    simp only [route,reverseEdges,List.head?_map,List.head?_reverse,principal.last,Option.map_some,Pairing.involutive]
  have routeLast : route.getLast?=some (site.net.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)) := by
    simp only [route,reverseEdges,List.getLast?_map,List.getLast?_reverse,principal.first,Option.map_some]
  have nonempty : route≠[] := by intro empty; rw [empty] at routeHead; cases routeHead
  have reversedHead : (reverseEdges old).head?=route.head? := by
    simp only [reverseEdges,List.head?_map,List.head?_reverse,finish,Option.map_some,Pairing.involutive]
    exact routeHead.symm
  have reversedLast : (reverseEdges old).getLast?=some (site.net.wire (site.outsideEnd source)) := by
    simp only [reverseEdges,List.getLast?_map,List.getLast?_reverse,first,Option.map_some]
  obtain ⟨suffix,split,suffixHead,remaining⟩ := labels.reverse.outside_internal_route_prefix site
    ((cut).wire source) (by simpa only [site.outsideEnd_wire] using reversedLast) route
    nonempty reversedHead (principal.reverse_internal_segments site)
    (transparent_reverse_turns principal.edges principal.transparent)
  have suffixFirst := suffixHead.trans routeLast
  have suffixLast : suffix.getLast?=some (site.net.wire (site.outsideEnd source)) := by
    have same : (reverseEdges old).getLast?=suffix.getLast? := by
      rw [split]
      cases suffix with
      | nil => cases suffixFirst
      | cons e suffix => simp only [List.getLast?_append,List.getLast?_cons,Option.some_or]
    exact same.symm.trans reversedLast
  obtain ⟨tail,suffixEq⟩ := List.head?_eq_some_iff.mp suffixFirst
  rw [suffixEq] at remaining suffixLast split
  cases tail with
  | nil =>
    have equal : site.net.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)=site.net.wire (site.outsideEnd source) := by
      simpa only [List.getLast?_cons,List.getLast?_nil,Option.getD_none] using Option.some.inj suffixLast
    have impossible := congrArg site.net.wire.mate equal
    simp only [Pairing.involutive] at impossible
    exact False.elim (site.internal_outside_ne (.inl false) source impossible)
  | cons next tail =>
    cases remaining with
    | @cons _ _ _ _ middle _ turn after =>
      rw [Pairing.involutive] at turn
      obtain ⟨port,depart,rule⟩ := turn.from_node (.inr (.inl ())) (.inl ()) rfl
      subst next
      cases port with
      | inl u => cases u; exact False.elim (rule.distinct rfl)
      | inr q =>
        let pre : List (Endpoint site.net) := reverseEdges ((.inl ⟨.inr (.inl ()),.inr q⟩)::tail)
        have rebuild : route.dropLast++[site.net.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)]=route := by
          obtain ⟨stem,lastEq⟩ := List.getLast?_eq_some_iff.mp routeLast
          rw [lastEq,List.dropLast_concat]
        have reverseSplit : reverseEdges old=route++(.inl ⟨.inr (.inl ()),.inr q⟩)::tail := by
          rw [←rebuild]
          simpa only [List.append_assoc,List.singleton_append] using split
        have oldSplit : old=pre++principal.edges := by
          have reflected := congrArg (reverseEdges (g:=site.net)) reverseSplit
          rw [reverseEdges_involutive,reverse_append] at reflected
          simpa only [route,reverseEdges_involutive] using reflected
        have tailLast : ((.inl ⟨.inr (.inl ()),.inr q⟩)::tail : List (Endpoint site.net)).getLast?=
            some (site.net.wire (site.outsideEnd source)) := by
          simpa only [List.getLast?_cons_cons] using suffixLast
        refine ⟨pre,q,middle,oldSplit,?_,?_,after.reverse,rule.reverse⟩
        · simp only [pre,reverseEdges,List.head?_map,List.head?_reverse,tailLast,Option.map_some,Pairing.involutive]
        · simp only [pre,reverseEdges,List.getLast?_map,List.getLast?_reverse,List.head?_cons,Option.map_some]
end
end Lamping.AG
