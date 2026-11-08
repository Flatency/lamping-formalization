import Lamping.Lamping.TypedTransparentPrefixes
namespace Lamping.AG
open Graph

private theorem adjacent_snoc {A : Type} {R : A → A → Prop}
    {es : List A} {e f : A}
    (turns : ∀ x y,(x,y)∈es.zip es.tail → R x y)
    (last : es.getLast?=some e) (next : R e f) :
    ∀ x y,(x,y)∈(es++[f]).zip (es++[f]).tail → R x y := by
  induction es with
  | nil => cases last
  | cons x es ih =>
    cases es with
    | nil =>
      have same : x=e := Option.some.inj last
      subst x
      simpa using next
    | cons y es =>
      intro a b member
      simp only [List.cons_append,List.tail_cons,List.zip_cons_cons,List.mem_cons] at member
      rcases member with same | member
      · cases same
        exact turns x y (by simp)
      · exact ih (by intro a b h; exact turns a b (by
          simp only [List.tail_cons,List.zip_cons_cons,List.mem_cons]; exact Or.inr h))
          (by simpa only [List.getLast?_cons_cons] using last) a b member

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

theorem transparent_reverse_turns (es : List (Endpoint g))
    (turns : ∀ e f,(e,f)∈es.zip es.tail →
      ∃ w d,g.wire e=.inr (.inr (w,d)) ∧f=.inr (.inr (w,!d))) :
    ∀ e f,(e,f)∈(reverseEdges es).zip (reverseEdges es).tail →
      ∃ w d,g.wire e=.inr (.inr (w,d)) ∧f=.inr (.inr (w,!d)) := by
  induction es with
  | nil => simp [reverseEdges]
  | cons e es ih =>
    cases es with
    | nil => simp [reverseEdges]
    | cons f es =>
      have tail := ih (by intro x y h; exact turns x y (by
        simp only [List.tail_cons,List.zip_cons_cons,List.mem_cons]; exact Or.inr h))
      obtain ⟨w,d,arrives,leaves⟩ := turns e f (by simp)
      rw [show reverseEdges (e::f::es)=reverseEdges (f::es)++[g.wire e] from by simp [reverseEdges]]
      apply adjacent_snoc tail (e:=g.wire f)
      · simp [reverseEdges]
      · refine ⟨w,!d,?_,?_⟩
        · simpa only [Pairing.involutive] using leaves
        · simpa only [Bool.not_not] using arrives
end

section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))

theorem PathSite.reverse_principal_route :
    ∃ route : List (Endpoint site.net),
      route.head?=some (.inl ⟨.inr (.inr ()),.inl ()⟩) ∧
      route.getLast?=some (site.net.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)) ∧
      (∀ e f,(e,f)∈route.zip route.tail →
        ∃ w d,site.net.wire e=.inr (.inr (w,d)) ∧f=.inr (.inr (w,!d))) := by
  obtain ⟨route,first,last,turns⟩ := site.principal_route
  refine ⟨reverseEdges route,?_,?_,transparent_reverse_turns route turns⟩
  · simp only [reverseEdges,List.head?_map,List.head?_reverse,last,Option.map_some,Pairing.involutive]
  · simp only [reverseEdges,List.getLast?_map,List.getLast?_reverse,first,Option.map_some]

/-- A supplied typed path from the passive principal already crosses the
whole matched principal component and departs the active control. The
contexts at that departure come from this very supplied labelling. -/
theorem PathSite.typed_active_control_prefix
    (control : s.active=.fan ∨s.active=.cro ∨s.active=.bra)
    {es : List (Endpoint site.net)} {a b : Context}
    (labels : Labelling site.net es a b) (typed : ∃ k,accessKind site.net es=some k)
    (first : es.head?=some (.inl ⟨.inr (.inr ()),.inl ()⟩)) :
    ∃ (pre : List (Endpoint site.net)) (q : Aux s.active) (rest : List (Endpoint site.net)) (middle : Context),
      es=pre++(site.net.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)::
        (.inl ⟨.inr (.inl ()),.inr q⟩)::rest) ∧
      Traversal s.low (.op s.active) (.inl ()) (.inr q) a middle ∧
      Labelling site.net ((.inl ⟨.inr (.inl ()),.inr q⟩)::rest) middle b := by
  obtain ⟨route,routeHead,routeLast,turns⟩ := site.reverse_principal_route
  have nonempty : route≠[] := by intro empty; rw [empty] at routeHead; cases routeHead
  obtain ⟨suffix,split,suffixHead,remaining⟩ := labels.typed_transparent_prefix typed route nonempty
    (first.trans routeHead.symm) turns
  rw [routeLast] at suffixHead
  have suffixLast : es.getLast?=suffix.getLast? := by
    rw [split]
    cases suffix with
    | nil => cases suffixHead
    | cons x xs => simp only [List.getLast?_append,List.getLast?_cons,Option.some_or]
  have suffixTyped : ∃ k,accessKind site.net suffix=some k := by
    simpa only [accessKind,suffixLast] using typed
  have nonterminal : portKind (.op s.active) (.inl ())=none := by
    rcases control with same | same | same <;> rw [same] <;> rfl
  obtain ⟨port,rest,middle,depart,rule,tail⟩ := remaining.typed_nonterminal_departure suffixTyped
    (site.net.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)) suffixHead (.inr (.inl ())) (.inl ())
    (site.net.wire.involutive _) nonterminal
  change Traversal s.low (.op s.active) (.inl ()) port a middle at rule
  cases port with
  | inl u => cases u; exact False.elim (rule.distinct rfl)
  | inr q => exact ⟨route.dropLast,q,rest,middle,split.trans (congrArg (List.append route.dropLast) depart),rule,tail⟩

/-- The departure auxiliary is fixed by the given physical path, even when
all its context labels are changed. The reference path is never completed. -/
theorem PathSite.typed_active_control_uniform
    (control : s.active=.fan ∨s.active=.cro ∨s.active=.bra)
    {es : List (Endpoint site.net)} {a b : Context}
    (labels : Labelling site.net es a b) (typed : ∃ k,accessKind site.net es=some k)
    (first : es.head?=some (.inl ⟨.inr (.inr ()),.inl ()⟩)) :
    ∃ q : Aux s.active,∀ input output,Labelling site.net es input output →
      ∃ middle,Traversal s.low (.op s.active) (.inl ()) (.inr q) input middle := by
  obtain ⟨route,routeHead,routeLast,turns⟩ := site.reverse_principal_route
  have nonempty : route≠[] := by intro empty; rw [empty] at routeHead; cases routeHead
  obtain ⟨suffix,split,suffixHead,remaining⟩ := labels.typed_transparent_prefix typed route nonempty
    (first.trans routeHead.symm) turns
  rw [routeLast] at suffixHead
  have suffixLast : es.getLast?=suffix.getLast? := by
    rw [split]
    cases suffix with
    | nil => cases suffixHead
    | cons x xs => simp only [List.getLast?_append,List.getLast?_cons,Option.some_or]
  have suffixTyped : ∃ k,accessKind site.net suffix=some k := by
    simpa only [accessKind,suffixLast] using typed
  have nonterminal : portKind (.op s.active) (.inl ())=none := by
    rcases control with same | same | same <;> rw [same] <;> rfl
  obtain ⟨port,rest,middle,depart,rule,_⟩ := remaining.typed_nonterminal_departure suffixTyped
    (site.net.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)) suffixHead (.inr (.inl ())) (.inl ())
    (site.net.wire.involutive _) nonterminal
  change Traversal s.low (.op s.active) (.inl ()) port a middle at rule
  cases port with
  | inl u => cases u; exact False.elim (rule.distinct rfl)
  | inr q =>
    refine ⟨q,?_⟩
    intro input output changed
    obtain ⟨newSuffix,newSplit,_,newRemaining⟩ := changed.typed_transparent_prefix typed route nonempty
      (first.trans routeHead.symm) turns
    have suffixEq : newSuffix=suffix := (List.append_cancel_left (split.symm.trans newSplit)).symm
    rw [suffixEq,depart] at newRemaining
    cases newRemaining with
    | cons turn tail =>
      rw [Pairing.involutive] at turn
      cases turn with
      | node node p q actual => exact ⟨_,actual⟩
end
end Lamping.AG

