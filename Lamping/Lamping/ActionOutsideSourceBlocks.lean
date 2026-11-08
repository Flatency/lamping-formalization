import Lamping.Lamping.ActionPrincipalInternal
namespace Lamping.AG
open Graph
section
variable {s : Schema} {K B W V : Type}
variable [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed

private theorem control_aux_output (op : Op) (p : Aux op) (q : Port (.op op))
    (control : op=.fan ∨op=.cro ∨op=.bra)
    (forced : ControlAuxOutput (.op op) (.inr p) q) : q=.inl () := by
  cases op <;> simp_all [ControlAuxOutput]

private theorem outside_route_exit
    {es : List (Endpoint site.net)} {a b : Context}
    (labels : Labelling site.net es a b) (last : Endpoint cut)
    (finish : es.getLast?=some (site.outsideEnd last))
    (route : List (Endpoint site.net)) (nonempty : route≠[])
    (first : es.head?=route.head?)
    (inside : ∀ e∈route,∃ i,e=site.internalEnd i)
    (steps : ∀ e f,(e,f)∈route.zip route.tail →
      ∃ w d,site.net.wire e=.inr (.inr (w,d)) ∧f=.inr (.inr (w,!d)))
    (node : K⊕(Unit⊕Unit)) (p : Port (site.net.label node).sort)
    (routeLast : route.getLast?=some (site.net.wire (.inl ⟨node,p⟩))) :
    ∃ (q : Port (site.net.label node).sort) (rest : List (Endpoint site.net)) (middle : Context),
      es=route.dropLast++site.net.wire (.inl ⟨node,p⟩)::(.inl ⟨node,q⟩)::rest ∧
      Traversal (site.net.label node).index (site.net.label node).sort p q a middle ∧
      Labelling site.net ((.inl ⟨node,q⟩)::rest) middle b := by
  obtain ⟨suffix,split,suffixHead,remaining⟩ := labels.outside_internal_route_prefix site last finish route nonempty first inside steps
  have suffixFirst := suffixHead.trans routeLast
  have suffixLast : suffix.getLast?=some (site.outsideEnd last) := by
    have same : es.getLast?=suffix.getLast? := by
      rw [split]
      cases suffix with
      | nil => cases suffixFirst
      | cons e suffix => simp only [List.getLast?_append,List.getLast?_cons,Option.some_or]
    exact same.symm.trans finish
  obtain ⟨tail,suffixEq⟩ := List.head?_eq_some_iff.mp suffixFirst
  rw [suffixEq] at remaining suffixLast split
  cases tail with
  | nil =>
    obtain ⟨i,atEnd⟩ := inside _ (List.mem_of_getLast? routeLast)
    have same : site.net.wire (.inl ⟨node,p⟩)=site.outsideEnd last := by
      simpa only [List.getLast?_cons,List.getLast?_nil,Option.getD_none] using Option.some.inj suffixLast
    exact False.elim (site.internal_outside_ne i last (atEnd.symm.trans same))
  | cons e tail =>
    cases remaining with
    | cons turn after =>
      rw [Pairing.involutive] at turn
      obtain ⟨q,depart,rule⟩ := turn.from_node node p rfl
      subst e
      exact ⟨q,tail,_,split,rule,after⟩

private theorem active_complete
    (control : s.active=.fan ∨s.active=.cro ∨s.active=.bra)
    (principal : SiteActionPrincipal site) (p : Aux s.active)
    {es : List (Endpoint site.net)} {a b : Context}
    (labels : Labelling site.net es a b) (next : 1<es.length)
    (first : es.head?=some (site.net.wire (.inl ⟨.inr (.inl ()),.inr p⟩)))
    (last : Endpoint cut) (finish : es.getLast?=some (site.outsideEnd last)) :
    ∃ (q : Aux s.passive) (rest : List (Endpoint site.net)) (middle : Context),
      es=principal.crossing site p q++rest ∧
      Labelling site.net (principal.crossing site p q) a middle ∧
      Labelling site.net ((.inl ⟨.inr (.inr ()),.inr q⟩)::rest) middle b := by
  obtain ⟨tail,headEq⟩ := List.head?_eq_some_iff.mp first
  subst es
  cases labels with
  | single => exact False.elim (Nat.lt_irrefl 1 next)
  | @cons _ e tail a seam b turn after =>
    rw [Pairing.involutive] at turn
    obtain ⟨port,depart,active⟩ := turn.from_node (.inr (.inl ())) (.inr p) rfl
    subst e
    have principalPort : port=.inl () := by
      exact control_aux_output s.active p port control active.control_aux
    subst port
    have tailLast : ((.inl ⟨.inr (.inl ()),.inl ()⟩)::tail : List (Endpoint site.net)).getLast?=some (site.outsideEnd last) := by
      simpa only [List.getLast?_cons_cons] using finish
    obtain ⟨port,rest,middle,split,passive,remaining⟩ := outside_route_exit site after last tailLast principal.edges
      (by intro empty; have actual:=principal.first; rw [empty] at actual; cases actual)
      principal.first.symm (principal.internal_segments site) principal.transparent (.inr (.inr ())) (.inl ()) principal.last
    cases port with
    | inl u => cases u; exact False.elim (passive.distinct rfl)
    | inr q =>
      have rebuild : principal.edges.dropLast++[site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)]=principal.edges := by
        obtain ⟨stem,lastEq⟩ := List.getLast?_eq_some_iff.mp principal.last
        rw [lastEq,List.dropLast_concat]
      have decomposition : (site.net.wire (.inl ⟨.inr (.inl ()),.inr p⟩)::
          (.inl ⟨.inr (.inl ()),.inl ()⟩)::tail)=principal.crossing site p q++rest := by
        simp only [SiteActionPrincipal.crossing,List.cons_append,List.append_assoc]
        rw [←rebuild]
        simpa only [List.append_assoc,List.singleton_append] using congrArg (_::·) split
      have frontLabels : Labelling site.net (principal.crossing site p q) a middle :=
        (principal.crossing_labels_iff site p q a middle).mpr
          ((leftRoute_labeling_iff s.active s.passive s.low s.high p q a middle).mpr ⟨seam,active,passive⟩)
      exact ⟨q,rest,middle,decomposition,frontLabels,remaining⟩

/-- An outside-ended labelled source path with an existing next turn has a
complete finite source block at any frontier entry. Its end may be untyped:
all excluded early stops are INTERNAL, while its actual last is OUTSIDE. -/
theorem PathSite.outside_frontier_source_route
    (control : s.active=.fan ∨s.active=.cro ∨s.active=.bra)
    (principal : SiteActionPrincipal site) (entry : s.Frontier)
    {es : List (Endpoint site.net)} {a b : Context}
    (labels : Labelling site.net es a b)
    (first : es.head?=some (site.net.wire (site.outsideEnd (.inr (.inl (.inr entry))))))
    (last : Endpoint cut) (finish : es.getLast?=some (site.outsideEnd last))
    (next : 1<es.length) :
    ∃ (exit : s.Frontier) (front rest : List (Endpoint site.net)) (middle : Context),
      es=front++rest ∧SourceActionRoute site principal entry exit front ∧
      front.getLast?=some (site.outsideEnd (.inr (.inl (.inr exit)))) ∧
      Labelling site.net front a middle ∧
      Labelling site.net ((site.outsideEnd (.inr (.inl (.inr exit))))::rest) middle b := by
  cases entry with
  | inl p =>
    obtain ⟨q,rest,middle,split,frontLabels,tail⟩ := active_complete site control principal p labels next first last finish
    refine ⟨.inr q,_,rest,middle,split,.cross p q,?_,frontLabels,tail⟩
    simp only [SiteActionPrincipal.crossing,List.getLast?_cons,List.getLast?_append,
      List.getLast?_nil,Option.getD_none,Option.some_or,Option.getD_some]
    rfl
  | inr p =>
    obtain ⟨tail,headEq⟩ := List.head?_eq_some_iff.mp first
    subst es
    cases labels with
    | single => exact False.elim (Nat.lt_irrefl 1 next)
    | @cons _ e tail a seam b turn after =>
      rw [Pairing.involutive] at turn
      obtain ⟨port,depart,passive⟩ := turn.from_node (.inr (.inr ())) (.inr p) rfl
      subst e
      cases port with
      | inr q =>
        have frontLabels : Labelling site.net (site.passiveCanonical p q) a seam := by
          apply Labelling.cons
          · rw [Pairing.involutive]; exact .node _ _ _ passive
          · exact .single _ _
        exact ⟨.inr q,_,tail,seam,rfl,.passive p q,rfl,frontLabels,after⟩
      | inl u =>
        cases u
        let route := reverseEdges principal.edges
        have routeHead : route.head?=some (.inl ⟨.inr (.inr ()),.inl ()⟩) := by
          simp only [route,reverseEdges,List.head?_map,List.head?_reverse,principal.last,Option.map_some,Pairing.involutive]
        have routeLast : route.getLast?=some (site.net.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)) := by
          simp only [route,reverseEdges,List.getLast?_map,List.getLast?_reverse,principal.first,Option.map_some]
        have tailLast : ((.inl ⟨.inr (.inr ()),.inl ()⟩)::tail : List (Endpoint site.net)).getLast?=some (site.outsideEnd last) := by
          simpa only [List.getLast?_cons_cons] using finish
        obtain ⟨port,rest,middle,split,active,remaining⟩ := outside_route_exit site after last tailLast route
          (by intro empty; rw [empty] at routeHead; cases routeHead) routeHead.symm
          (principal.reverse_internal_segments site) (transparent_reverse_turns principal.edges principal.transparent)
          (.inr (.inl ())) (.inl ()) routeLast
        cases port with
        | inl u => cases u; exact False.elim (active.distinct rfl)
        | inr q =>
          have rebuild : route.dropLast++[site.net.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)]=route := by
            obtain ⟨stem,lastEq⟩ := List.getLast?_eq_some_iff.mp routeLast
            rw [lastEq,List.dropLast_concat]
          have decomposition : site.net.wire (.inl ⟨.inr (.inr ()),.inr p⟩)::
              (.inl ⟨.inr (.inr ()),.inl ()⟩)::tail =reverseEdges (principal.crossing site q p)++rest := by
            rw [principal.reverse_crossing_edges site q p]
            simp only [List.cons_append,List.append_assoc]
            change _=site.net.wire (.inl ⟨.inr (.inr ()),.inr p⟩)::(route++(.inl ⟨.inr (.inl ()),.inr q⟩)::rest)
            rw [←rebuild]
            simpa only [List.append_assoc,List.singleton_append] using congrArg (_::·) split
          have frontLabels : Labelling site.net (reverseEdges (principal.crossing site q p)) a middle :=
            ((principal.crossing_labels_iff site q p middle a).mpr
              ((leftRoute_labeling_iff s.active s.passive s.low s.high q p middle a).mpr
                ⟨seam,active.reverse,passive.reverse⟩)).reverse
          refine ⟨.inl q,_,rest,middle,decomposition,.backward q p,?_,frontLabels,remaining⟩
          simp only [reverseEdges,List.getLast?_map,List.getLast?_reverse,SiteActionPrincipal.crossing,
            List.head?_cons,Option.map_some,Pairing.involutive]
          rfl
end
end Lamping.AG

