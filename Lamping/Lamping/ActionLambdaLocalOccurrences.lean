import Lamping.Lamping.ActionOccurrenceLabelling
namespace Lamping.AG
open Graph
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))

private theorem principal_node {principal : SiteActionPrincipal site} {node : K⊕(Unit⊕Unit)}
    {p : Port (site.net.label node).sort}
    (member : (.inl ⟨node,p⟩ : Endpoint site.net)∈principal.edges) :
    (.inl ⟨node,p⟩ : Endpoint site.net)=.inl ⟨.inr (.inl ()),.inl ()⟩ := by
  have head_or : ∀ (es : List (Endpoint site.net)),
      (∀ e f,(e,f)∈es.zip es.tail →∃ w d,site.net.wire e=.inr (.inr (w,d)) ∧f=.inr (.inr (w,!d))) →
      (.inl ⟨node,p⟩ : Endpoint site.net)∈es →es.head?=some (.inl ⟨node,p⟩) := by
    intro es turns inside
    induction es with
    | nil => cases inside
    | cons x xs ih =>
      rcases List.mem_cons.mp inside with same |inside
      · subst x; rfl
      · cases xs with
        | nil => cases inside
        | cons y ys =>
          have remaining : ∀ e f,(e,f)∈(y::ys).zip (y::ys).tail →
              ∃ w d,site.net.wire e=.inr (.inr (w,d)) ∧f=.inr (.inr (w,!d)) := by
            intro e f pair; exact turns e f (List.mem_cons_of_mem _ pair)
          have first := ih remaining inside
          have same : y=(.inl ⟨node,p⟩ : Endpoint site.net) := Option.some.inj first
          obtain ⟨w,d,_,atY⟩ := turns x y (by simp)
          rw [same] at atY
          cases atY
  exact Option.some.inj ((head_or principal.edges principal.transparent member).symm.trans principal.first)

private theorem reverse_principal_node {principal : SiteActionPrincipal site} {node : K⊕(Unit⊕Unit)}
    {p : Port (site.net.label node).sort}
    (member : (.inl ⟨node,p⟩ : Endpoint site.net)∈reverseEdges principal.edges) :
    (.inl ⟨node,p⟩ : Endpoint site.net)=.inl ⟨.inr (.inr ()),.inl ()⟩ := by
  have last_or : ∀ (es : List (Endpoint site.net)),
      (∀ e f,(e,f)∈es.zip es.tail →∃ w d,site.net.wire e=.inr (.inr (w,d)) ∧f=.inr (.inr (w,!d))) →
      ∀ e,e∈es →site.net.wire e=(.inl ⟨node,p⟩ : Endpoint site.net) →es.getLast?=some e := by
    intro es turns e inside arrives
    induction es with
    | nil => cases inside
    | cons x xs ih => cases xs with
      | nil =>
        have same : e=x := List.mem_singleton.mp inside
        subst e; rfl
      | cons y ys =>
        rcases List.mem_cons.mp inside with same |inside
        · subst x
          obtain ⟨w,d,atE,_⟩ := turns e y (by simp)
          rw [arrives] at atE
          cases atE
        · have remaining : ∀ e f,(e,f)∈(y::ys).zip (y::ys).tail →
              ∃ w d,site.net.wire e=.inr (.inr (w,d)) ∧f=.inr (.inr (w,!d)) := by
            intro e f pair; exact turns e f (List.mem_cons_of_mem _ pair)
          exact ih remaining inside
  obtain ⟨e,inside,arrives⟩ := List.mem_map.mp member
  have last := last_or principal.edges principal.transparent e (List.mem_reverse.mp inside) arrives
  have same := Option.some.inj (last.symm.trans principal.last)
  rw [same,Pairing.involutive] at arrives
  exact arrives.symm

private theorem crossing_positive_aux {principal : SiteActionPrincipal site}
    (a : Aux s.active) (q target : Aux s.passive) (ordinal : Nat) (positive : 0<ordinal)
    (point : (principal.crossing site a q)[ordinal]?=some (.inl ⟨.inr (.inr ()),.inr target⟩)) :
    q=target ∧ordinal+1=(principal.crossing site a q).length := by
  cases ordinal with
  | zero => omega
  | succ n =>
    change (principal.edges++[.inl ⟨.inr (.inr ()),.inr q⟩])[n]?=_ at point
    have bound : principal.edges.length≤n := by
      by_cases bound : principal.edges.length≤n
      · exact bound
      · have within : n<principal.edges.length := by omega
        rw [List.getElem?_append_left within] at point
        have bad := principal_node site (List.mem_of_getElem? point)
        cases bad
    rw [List.getElem?_append_right bound] at point
    have zero : n-principal.edges.length=0 := by
      cases h : n-principal.edges.length with
      | zero => rfl
      | succ k => rw [h] at point; cases point
    rw [zero] at point
    have same := Option.some.inj point
    have ports : (.inr q : Port (.op s.passive))=.inr target := by
      simpa only [Sigma.mk.injEq,heq_eq_eq, true_and] using (Sum.inl.inj same)
    refine ⟨Sum.inr.inj ports,?_⟩
    simp only [SiteActionPrincipal.crossing,List.length_cons,List.length_append,List.length_nil]
    omega

private theorem reverse_crossing_aux_absent {principal : SiteActionPrincipal site}
    (a : Aux s.active) (q target : Aux s.passive) (ordinal : Nat) (positive : 0<ordinal)
    (point : (reverseEdges (principal.crossing site a q))[ordinal]?=some (.inl ⟨.inr (.inr ()),.inr target⟩)) : False := by
  have shape : reverseEdges (principal.crossing site a q)=
      site.net.wire (.inl ⟨.inr (.inr ()),.inr q⟩)::
      (reverseEdges principal.edges++[.inl ⟨.inr (.inl ()),.inr a⟩]) := by
    simp only [SiteActionPrincipal.crossing,reverseEdges,List.reverse_cons,List.reverse_append,
      List.map_append,List.map_cons,List.map_nil,Pairing.involutive]
    rfl
  cases ordinal with
  | zero => omega
  | succ n =>
    rw [shape] at point
    have member : (.inl ⟨.inr (.inr ()),.inr target⟩ : Endpoint site.net)∈
        reverseEdges principal.edges++[.inl ⟨.inr (.inl ()),.inr a⟩] := List.mem_of_getElem? point
    rcases List.mem_append.mp member with inside |last
    · have bad := reverse_principal_node site inside
      have ports : (.inr target : Port (.op s.passive))=.inl () := by
        simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using (Sum.inl.inj bad)
      cases ports
    · have bad := List.mem_singleton.mp last
      have nodes := congrArg Sigma.fst (Sum.inl.inj bad)
      cases nodes

private theorem no_lambda_aux_aux {f : Op} {index : Nat} (lam : f=.lam) (p q : Aux f) {a b : Context}
    (rule : Traversal index (.op f) (.inr p) (.inr q) a b) : False := by
  subst f
  cases p <;> cases q
  · exact rule.no_binding.1 rfl
  · exact rule.no_binding.1 rfl
  · exact rule.no_binding.2 rfl
  · exact rule.distinct rfl

private theorem passive_lambda_absent (lam : s.passive=.lam) (p q : Aux s.passive) {a b : Context}
    (labels : Labelling site.net (site.passiveCanonical p q) a b) : False := by
  cases labels with
  | cons turn after =>
    rw [Pairing.involutive] at turn
    cases turn with
    | node node p q rule => exact no_lambda_aux_aux lam p q rule

end

/-- Only physical forward crossings of the three actual action schemas.
This refinement contains no labels, invariant, or transparency conclusion. -/
inductive ActionLambdaCross {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
    {kept : K → Label signature} : {s : Schema} →
    (site : PathSite s kept (B:=B) (W:=W) (V:=V)) → SiteActionPrincipal site → Aux s.passive →
    List (Endpoint s.right.net) → List (Endpoint site.net) → Prop where
  | fan {f i j lt} {site : PathSite (.fanAction f i j lt) kept (B:=B) (W:=W) (V:=V)}
      (principal : SiteActionPrincipal site) (branch : Bool) (q : Aux f) :
      ActionLambdaCross site principal q (fanCrossEdges branch q) (principal.crossing site branch q)
  | cro {f i j lt} {site : PathSite (.croAction f i j lt) kept (B:=B) (W:=W) (V:=V)}
      (principal : SiteActionPrincipal site) (q : Aux f) :
      ActionLambdaCross site principal q (unaryCrossEdges (s:=.croAction f i j lt) (Bij.refl _) q) (principal.crossing site () q)
  | bra {f i j lt} {site : PathSite (.braAction f i j lt) kept (B:=B) (W:=W) (V:=V)}
      (principal : SiteActionPrincipal site) (q : Aux f) :
      ActionLambdaCross site principal q (unaryCrossEdges (s:=.braAction f i j lt) (Bij.refl _) q) (principal.crossing site () q)

section Reflection
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))

/-- A noninitial passive lambda auxiliary departure in an actual canonical
block is its FINAL source segment and comes from a forward RHS crossing.
In particular the selected ctx→body turn straddles the front/rest overlap;
the source head is not incorrectly excluded when frontier wires alias. -/
theorem ActionCanonicalLocal.lambda_aux_occurrence {principal : SiteActionPrincipal site} {rhs old}
    (relation : ActionCanonicalLocal site principal rhs old) (lam : s.passive=.lam)
    {a b : Context} (labels : Labelling s.right.net rhs a b)
    (aux : Aux s.passive) (ordinal : Nat) (positive : 0<ordinal)
    (point : old[ordinal]?=some (.inl ⟨.inr (.inr ()),.inr aux⟩)) :
    ActionLambdaCross site principal aux rhs old ∧ordinal+1=old.length := by
  cases relation with
  | @fan f i j lt actual principal rhs old relation => cases relation with
    | cross branch q =>
      obtain ⟨same,last⟩ := crossing_positive_aux actual branch q aux ordinal positive point
      subst q
      exact ⟨.fan principal branch aux,last⟩
    | backward branch q => exact False.elim (reverse_crossing_aux_absent actual branch q aux ordinal positive point)
    | passive branch p q =>
      exact False.elim (passive_lambda_absent actual lam p q
        ((FanCanonicalLocal.passive (principal:=principal) branch p q).source_labels actual labels))
  | @cro f i j lt actual principal rhs old relation => cases relation with
    | cross q =>
      obtain ⟨same,last⟩ := crossing_positive_aux actual () q aux ordinal positive point
      subst q
      exact ⟨.cro principal aux,last⟩
    | backward q => exact False.elim (reverse_crossing_aux_absent actual () q aux ordinal positive point)
    | passive p q =>
      have source := (ActionCanonicalLocal.cro (UnaryCanonicalLocal.passive (principal:=principal) p q)).source_labels actual labels
      exact False.elim (passive_lambda_absent actual lam p q source)
  | @bra f i j lt actual principal rhs old relation => cases relation with
    | cross q =>
      obtain ⟨same,last⟩ := crossing_positive_aux actual () q aux ordinal positive point
      subst q
      exact ⟨.bra principal aux,last⟩
    | backward q => exact False.elim (reverse_crossing_aux_absent actual () q aux ordinal positive point)
    | passive p q =>
      have source := (ActionCanonicalLocal.bra (UnaryCanonicalLocal.passive (principal:=principal) p q)).source_labels actual labels
      exact False.elim (passive_lambda_absent actual lam p q source)
end Reflection
end Lamping.AG
