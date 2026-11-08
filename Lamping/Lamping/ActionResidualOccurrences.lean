import Lamping.Lamping.ActionCanonicalAssembly
namespace Lamping.AG
open Graph
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed

private theorem first_or_vertex {es : List (Endpoint site.net)}
    (turns : ∀ e f,(e,f)∈es.zip es.tail →
      ∃ w d,site.net.wire e=.inr (.inr (w,d)) ∧f=.inr (.inr (w,!d)))
    (e : Endpoint site.net) (member : e∈es) : es.head?=some e ∨∃ w d,e=.inr (.inr (w,d)) := by
  induction es with
  | nil => cases member
  | cons x xs ih =>
    rcases List.mem_cons.mp member with rfl |member
    · exact Or.inl rfl
    · cases xs with
      | nil => cases member
      | cons y ys =>
        have remaining : ∀ e f,(e,f)∈(y::ys).zip (y::ys).tail →
            ∃ w d,site.net.wire e=.inr (.inr (w,d)) ∧f=.inr (.inr (w,!d)) := by
          intro e f pair; exact turns e f (List.mem_cons_of_mem _ pair)
        rcases ih remaining member with first |vertex
        · have same : y=e := Option.some.inj first
          obtain ⟨w,d,_,atY⟩ := turns x y (by simp)
          exact Or.inr ⟨w,!d,same.symm.trans atY⟩
        · exact Or.inr vertex

private theorem last_or_vertex {es : List (Endpoint site.net)}
    (turns : ∀ e f,(e,f)∈es.zip es.tail →
      ∃ w d,site.net.wire e=.inr (.inr (w,d)) ∧f=.inr (.inr (w,!d)))
    (e : Endpoint site.net) (member : e∈es) : es.getLast?=some e ∨∃ w d,site.net.wire e=.inr (.inr (w,d)) := by
  induction es with
  | nil => cases member
  | cons x xs ih =>
    cases xs with
    | nil =>
      have same : e=x := List.mem_singleton.mp member
      subst e
      exact Or.inl rfl
    | cons y ys =>
      rcases List.mem_cons.mp member with rfl |member
      · obtain ⟨w,d,arrives,_⟩ := turns e y (by simp)
        exact Or.inr ⟨w,d,arrives⟩
      · have remaining : ∀ e f,(e,f)∈(y::ys).zip (y::ys).tail →
            ∃ w d,site.net.wire e=.inr (.inr (w,d)) ∧f=.inr (.inr (w,!d)) := by
          intro e f pair; exact turns e f (List.mem_cons_of_mem _ pair)
        rcases ih remaining member with last |vertex
        · exact Or.inl (by simpa only [List.getLast?_cons_cons] using last)
        · exact Or.inr vertex

/-- An actual principal component contains only its active node as a node
departure. This follows from transparent turns, allowing repeated vertices. -/
theorem SiteActionPrincipal.kept_not_principal (principal : SiteActionPrincipal site)
    (node : K) (p : Port (kept node).sort) :
    (.inl ⟨.inl node,p⟩ : Endpoint site.net)∉principal.edges := by
  intro member
  rcases first_or_vertex site principal.transparent _ member with first |⟨w,d,impossible⟩
  · have same := Option.some.inj (first.symm.trans principal.first)
    have nodes := congrArg Sigma.fst (Sum.inl.inj same)
    cases nodes
  · cases impossible

theorem SiteActionPrincipal.kept_not_reverse (principal : SiteActionPrincipal site)
    (node : K) (p : Port (kept node).sort) :
    (.inl ⟨.inl node,p⟩ : Endpoint site.net)∉reverseEdges principal.edges := by
  intro member
  obtain ⟨e,inside,arrives⟩ := List.mem_map.mp member
  rcases last_or_vertex site principal.transparent e (List.mem_reverse.mp inside) with last |⟨w,d,vertex⟩
  · have same := Option.some.inj (last.symm.trans principal.last)
    rw [same,Pairing.involutive] at arrives
    have nodes := congrArg Sigma.fst (Sum.inl.inj arrives)
    cases nodes
  · rw [arrives] at vertex
    cases vertex

private theorem crossing_tail_excludes (principal : SiteActionPrincipal site)
    (a : Aux s.active) (b : Aux s.passive) (node : K) (p : Port (kept node).sort) :
    (.inl ⟨.inl node,p⟩ : Endpoint site.net)∉(principal.crossing site a b).tail := by
  intro member
  change (.inl ⟨.inl node,p⟩ : Endpoint site.net)∈principal.edges++[.inl ⟨.inr (.inr ()),.inr b⟩] at member
  rcases List.mem_append.mp member with inside |last
  · exact principal.kept_not_principal site node p inside
  · have same := List.mem_singleton.mp last
    have nodes := congrArg Sigma.fst (Sum.inl.inj same)
    cases nodes

private theorem reverse_crossing_tail_excludes (principal : SiteActionPrincipal site)
    (a : Aux s.active) (b : Aux s.passive) (node : K) (p : Port (kept node).sort) :
    (.inl ⟨.inl node,p⟩ : Endpoint site.net)∉(reverseEdges (principal.crossing site a b)).tail := by
  have shape : reverseEdges (principal.crossing site a b)=
      site.net.wire (.inl ⟨.inr (.inr ()),.inr b⟩)::
      (reverseEdges principal.edges++[.inl ⟨.inr (.inl ()),.inr a⟩]) := by
    simp only [SiteActionPrincipal.crossing,reverseEdges,List.reverse_cons,List.reverse_append,
      List.map_append,List.map_cons,List.map_nil,Pairing.involutive]
    rfl
  rw [shape]
  intro member
  rcases List.mem_append.mp member with inside |last
  · exact principal.kept_not_reverse site node p inside
  · have same := List.mem_singleton.mp last
    have nodes := congrArg Sigma.fst (Sum.inl.inj same)
    cases nodes

private theorem passive_tail_excludes (a b : Aux s.passive) (node : K) (p : Port (kept node).sort) :
    (.inl ⟨.inl node,p⟩ : Endpoint site.net)∉(site.passiveCanonical a b).tail := by
  intro member
  have same := List.mem_singleton.mp member
  have nodes := congrArg Sigma.fst (Sum.inl.inj same)
  cases nodes

/-- The first source segment may lie at a retained node joined to the
frontier. All subsequent source departures of this canonical local block are
active nodes or transparent vertices, and cannot hide a retained occurrence. -/
theorem ActionCanonicalLocal.kept_not_tail {principal : SiteActionPrincipal site} {rhs old}
    (relation : ActionCanonicalLocal site principal rhs old) (node : K) (p : Port (kept node).sort) :
    (.inl ⟨.inl node,p⟩ : Endpoint site.net)∉old.tail := by
  cases relation with
  | @fan f i j lt actual principal rhs old relation => cases relation with
    | cross a b => exact crossing_tail_excludes actual principal a b node p
    | backward a b => exact reverse_crossing_tail_excludes actual principal a b node p
    | passive a b c => exact passive_tail_excludes actual b c node p
  | @cro f i j lt actual principal rhs old relation => cases relation with
    | cross b => exact crossing_tail_excludes actual principal _ b node p
    | backward b => exact reverse_crossing_tail_excludes actual principal _ b node p
    | passive b c => exact passive_tail_excludes actual b c node p
  | @bra f i j lt actual principal rhs old relation => cases relation with
    | cross b => exact crossing_tail_excludes actual principal _ b node p
    | backward b => exact reverse_crossing_tail_excludes actual principal _ b node p
    | passive b c => exact passive_tail_excludes actual b c node p

private theorem outside_injective : Function.Injective site.outsideEnd := by
  intro e f same
  let split := fragmentEnd (B:=B) (W:=W) site.net.label (pathPartition s V)
  change split.invFun (.inl e)=split.invFun (.inl f) at same
  have mapped := congrArg split same
  simpa only [split.right_inv,Sum.inl.injEq] using mapped

/-- Output of cutting one specified retained-node departure of the source
path. Both residuals overlap at exactly that same ordered occurrence. -/
structure ActionResidualOccurrence (principal : SiteActionPrincipal site)
    (raw : List (PlugSegment cut s.right.net)) (old : List (Endpoint site.net))
    (node : K) (p : Port (kept node).sort) (ordinal : Nat) where
  before : List (PlugSegment cut s.right.net)
  after : List (PlugSegment cut s.right.net)
  oldBefore : List (Endpoint site.net)
  oldAfter : List (Endpoint site.net)
  raw_eq : raw=before++ .inl (.inl ⟨node,p⟩)::after
  old_eq : old=oldBefore++(.inl ⟨.inl node,p⟩)::oldAfter
  position : oldBefore.length=ordinal
  prefixResidual : ActionCanonicalBlocks site principal
    (before++[.inl (.inl ⟨node,p⟩)]) (oldBefore++[.inl ⟨.inl node,p⟩])
  suffixResidual : ActionCanonicalBlocks site principal
    (.inl (.inl ⟨node,p⟩)::after) ((.inl ⟨.inl node,p⟩)::oldAfter)

theorem ActionResidualOccurrence.prefix_head {principal : SiteActionPrincipal site} {raw old node p ordinal}
    (cutAt : ActionResidualOccurrence site principal raw old node p ordinal) :
    (cutAt.before++[Sum.inl (.inl ⟨node,p⟩ : Endpoint cut)]).head?=raw.head? := by
  apply Eq.trans _ (congrArg List.head? cutAt.raw_eq).symm
  cases cutAt.before <;> rfl

private theorem occurrence_zero {principal : SiteActionPrincipal site} {raw old node p}
    (relation : ActionCanonicalBlocks site principal raw old)
    (atZero : old[0]?=some (.inl ⟨.inl node,p⟩)) :
    Nonempty (ActionResidualOccurrence site principal raw old node p 0) := by
  have rawHead : ∃ e,raw.head?=some (.inl e) := by cases relation <;> exact ⟨_,rfl⟩
  obtain ⟨e,rawHead⟩ := rawHead
  have oldHead := relation.head site rawHead
  have zeroHead : old.head?=some (site.outsideEnd (.inl ⟨node,p⟩)) := by
    simpa only [List.head?_eq_getElem?] using atZero
  have same := outside_injective site (Option.some.inj (oldHead.symm.trans zeroHead))
  subst e
  obtain ⟨rawTail,rawSplit⟩ := List.head?_eq_some_iff.mp rawHead
  obtain ⟨oldTail,oldSplit⟩ := List.head?_eq_some_iff.mp oldHead
  exact ⟨⟨[],rawTail,[],oldTail,rawSplit,oldSplit,rfl,.single _,
    by simpa only [rawSplit,oldSplit] using relation⟩⟩

/-- The exact ordinal is reflected through finite actual canonical blocks.
No retained node occurs after a local source block's head, so a noninitial
selected occurrence must lie strictly beyond that block's physical prefix. -/
theorem ActionCanonicalBlocks.split_kept_occurrence {principal : SiteActionPrincipal site} {raw old node p ordinal}
    (relation : ActionCanonicalBlocks site principal raw old)
    (atOccurrence : old[ordinal]?=some (.inl ⟨.inl node,p⟩)) :
    Nonempty (ActionResidualOccurrence site principal raw old node p ordinal) := by
  induction relation generalizing ordinal with
  | single e =>
    cases ordinal with
    | zero => exact occurrence_zero site (.single e) atOccurrence
    | succ n => cases atOccurrence
  | @outside e f tail oldTail rest ih =>
    cases ordinal with
    | zero => exact occurrence_zero site (.outside rest) atOccurrence
    | succ n =>
      obtain ⟨cutAt⟩ := ih atOccurrence
      have prefixHead : (cutAt.before++[Sum.inl (.inl ⟨node,p⟩ : Endpoint cut)]).head?=some (.inl f) := cutAt.prefix_head site
      obtain ⟨prefixTail,prefixSplit⟩ := List.head?_eq_some_iff.mp prefixHead
      have before := cutAt.prefixResidual
      rw [prefixSplit] at before
      refine ⟨⟨.inl e::cutAt.before,cutAt.after,site.outsideEnd e::cutAt.oldBefore,cutAt.oldAfter,
        ?_,?_,?_,?_,cutAt.suffixResidual⟩⟩
      · simpa only [List.cons_append] using congrArg (Sum.inl e::·) cutAt.raw_eq
      · simpa only [List.cons_append] using congrArg (site.outsideEnd e::·) cutAt.old_eq
      · simp only [List.length_cons,cutAt.position]
      · simpa only [List.cons_append,←prefixSplit] using ActionCanonicalBlocks.outside (e:=e) before
  | @through e exit tail oldTail inside front route start rest ih =>
    cases ordinal with
    | zero => exact occurrence_zero site (.through inside front route start rest) atOccurrence
    | succ n =>
      have bound : front.length≤n+1 := by
        by_cases bound : front.length≤n+1
        · exact bound
        · have within : n+1<front.length := by omega
          rw [List.getElem?_append_left within] at atOccurrence
          cases front with
          | nil => simp at within
          | cons x xs =>
            have atTail : xs[n]?=some (.inl ⟨.inl node,p⟩) := atOccurrence
            have member := List.mem_of_getElem? atTail
            exact False.elim (route.kept_not_tail site node p (List.mem_append_left _ member))
      rw [List.getElem?_append_right bound] at atOccurrence
      obtain ⟨cutAt⟩ := ih atOccurrence
      have prefixHead : (cutAt.before++[Sum.inl (.inl ⟨node,p⟩ : Endpoint cut)]).head?=
          some (.inl (.inr (.inl (.inr exit)))) := cutAt.prefix_head site
      obtain ⟨prefixTail,prefixSplit⟩ := List.head?_eq_some_iff.mp prefixHead
      have before := cutAt.prefixResidual
      rw [prefixSplit] at before
      refine ⟨⟨.inl e::(inside.map Sum.inr++cutAt.before),cutAt.after,
        front++cutAt.oldBefore,cutAt.oldAfter,?_,?_,?_,?_,cutAt.suffixResidual⟩⟩
      · simpa only [List.cons_append,List.append_assoc] using
          congrArg (fun xs => Sum.inl e::(inside.map Sum.inr++xs)) cutAt.raw_eq
      · simpa only [List.append_assoc] using congrArg (front++·) cutAt.old_eq
      · rw [List.length_append,cutAt.position]
        omega
      · simpa only [List.cons_append,List.append_assoc,←prefixSplit] using
          ActionCanonicalBlocks.through inside front route start before
end
end Lamping.AG
