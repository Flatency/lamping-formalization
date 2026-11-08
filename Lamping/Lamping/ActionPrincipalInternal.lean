import Lamping.Lamping.ActionSourceExpansion
namespace Lamping.AG
open Graph
section
variable {s : Schema} {K B W V : Type}
variable [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed

/-- The two carrier images are physically disjoint. -/
theorem PathSite.internal_outside_ne (i : Bool⊕(V×Bool)) (e : Endpoint cut) :
    site.internalEnd i≠site.outsideEnd e := by
  intro same
  let split := fragmentEnd (B:=B) (W:=W) site.net.label (pathPartition s V)
  have mapped := congrArg split same
  change split (split.invFun (.inr i))=split (split.invFun (.inl e)) at mapped
  simp only [split.right_inv] at mapped
  cases mapped

private theorem transparent_internal_next {e f : Endpoint site.net}
    (i : Bool⊕(V×Bool)) (inside : e=site.internalEnd i)
    (step : ∃ w d,site.net.wire e=.inr (.inr (w,d)) ∧f=.inr (.inr (w,!d))) :
    ∃ j,f=site.internalEnd j := by
  subst e
  obtain ⟨w,d,arrives,leaves⟩ := step
  rw [site.internalEnd_wire] at arrives
  cases w with
  | inl w => exact False.elim (site.internal_outside_ne (site.internal i) (.inr (.inr (w,d))) arrives)
  | inr v => exact ⟨.inr (v,!d),leaves⟩

private theorem route_internal (es : List (Endpoint site.net))
    (first : ∃ i,es.head?=some (site.internalEnd i))
    (steps : ∀ e f,(e,f)∈es.zip es.tail →
      ∃ w d,site.net.wire e=.inr (.inr (w,d)) ∧f=.inr (.inr (w,!d))) :
    ∀ e∈es,∃ i,e=site.internalEnd i := by
  induction es with
  | nil => intro e member; cases member
  | cons e es ih =>
    obtain ⟨i,head⟩ := first
    have same : e=site.internalEnd i := Option.some.inj head
    intro x member
    rcases List.mem_cons.mp member with rfl|member
    · exact ⟨i,same⟩
    · cases es with
      | nil => cases member
      | cons f es =>
        obtain ⟨j,atF⟩ := transparent_internal_next site i same (steps e f (by simp))
        exact ih ⟨j,congrArg some atF⟩
          (by intro x y pair; exact steps x y (List.mem_cons_of_mem _ pair)) x member

/-- Every physical segment of the selected principal route is internal,
including repeated W visits. The conclusion is not a simple-path assertion. -/
theorem SiteActionPrincipal.internal_segments (principal : SiteActionPrincipal site) :
    ∀ e∈principal.edges,∃ i,e=site.internalEnd i :=
  route_internal site principal.edges ⟨.inl false,principal.first⟩ principal.transparent

theorem SiteActionPrincipal.reverse_internal_segments (principal : SiteActionPrincipal site) :
    ∀ e∈reverseEdges principal.edges,∃ i,e=site.internalEnd i := by
  intro e member
  obtain ⟨x,member,same⟩ := List.mem_map.mp member
  obtain ⟨i,inside⟩ := principal.internal_segments site x (List.mem_reverse.mp member)
  subst x
  rw [site.internalEnd_wire] at same
  exact ⟨site.internal i,same.symm⟩

/-- Reflect an already present finite internal transparent route. An outside
terminal rules out stopping before its end, even if the given whole path is
control-ended and hence not a typed RootAccess. No path is extended. -/
theorem Labelling.outside_internal_route_prefix
    {es : List (Endpoint site.net)} {a b : Context}
    (labels : Labelling site.net es a b) (last : Endpoint cut)
    (finish : es.getLast?=some (site.outsideEnd last))
    (route : List (Endpoint site.net)) (nonempty : route≠[])
    (first : es.head?=route.head?)
    (inside : ∀ e∈route,∃ i,e=site.internalEnd i)
    (steps : ∀ e f,(e,f)∈route.zip route.tail →
      ∃ w d,site.net.wire e=.inr (.inr (w,d)) ∧f=.inr (.inr (w,!d))) :
    ∃ suffix,es=route.dropLast++suffix ∧suffix.head?=route.getLast? ∧Labelling site.net suffix a b := by
  induction route generalizing es a b with
  | nil => exact False.elim (nonempty rfl)
  | cons e route ih =>
    cases route with
    | nil => exact ⟨es,by simp,by simpa only [List.head?_cons,List.getLast?_cons,List.getLast?_nil] using first,labels⟩
    | cons f route =>
      obtain ⟨w,d,arrives,leaves⟩ := steps e f (by simp)
      obtain ⟨i,atE⟩ := inside e (by simp)
      cases es with
      | nil => cases first
      | cons x es =>
        have same : x=e := Option.some.inj first
        subst x
        cases es with
        | nil =>
          have atLast : e=site.outsideEnd last := by
            simpa only [List.getLast?_cons,List.getLast?_nil,Option.getD_none] using Option.some.inj finish
          exact False.elim (site.internal_outside_ne i last (atE.symm.trans atLast))
        | cons y es =>
          cases labels with
          | @cons _ _ _ _ middle _ turn after =>
            have next : y=f ∧middle=a := by
              rw [arrives] at turn
              cases turn
              exact ⟨leaves.symm,rfl⟩
            obtain ⟨equal,contextEq⟩ := next
            subst y
            subst middle
            have restLast : (f::es).getLast?=some (site.outsideEnd last) := by
              simpa only [List.getLast?_cons_cons] using finish
            obtain ⟨suffix,split,head,remaining⟩ := ih after restLast (by simp) rfl
              (by intro x member; exact inside x (List.mem_cons_of_mem _ member))
              (by intro x y pair; exact steps x y (List.mem_cons_of_mem _ pair))
            exact ⟨suffix,by change e::f::es=e::((f::route).dropLast++suffix); rw [←split],
              by simpa only [List.getLast?_cons_cons] using head,remaining⟩
end
end Lamping.AG

