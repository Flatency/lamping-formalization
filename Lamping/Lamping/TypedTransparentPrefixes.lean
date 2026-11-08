import Lamping.Lamping.MatchingDefinitions
import Lamping.Lamping.PathSitePrincipalRoutes
namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

/-- An already given proper-ended path cannot stop inside a specified finite
transparent route. This reflects a prefix, and never extends a partial path. -/
theorem Labelling.typed_transparent_prefix {es : List (Endpoint g)} {a b : Context}
    (labels : Labelling g es a b) (typed : ∃ k,accessKind g es=some k)
    (route : List (Endpoint g)) (nonempty : route≠[])
    (first : es.head?=route.head?)
    (turns : ∀ e f,(e,f)∈route.zip route.tail →
      ∃ w d,g.wire e=.inr (.inr (w,d)) ∧f=.inr (.inr (w,!d))) :
    ∃ suffix,es=route.dropLast++suffix ∧ suffix.head?=route.getLast? ∧
      Labelling g suffix a b := by
  induction route generalizing es a b with
  | nil => exact False.elim (nonempty rfl)
  | cons e route ih =>
    cases route with
    | nil =>
      exact ⟨es,by simp,by simpa only [List.head?_cons,List.getLast?_cons,List.getLast?_nil] using first,labels⟩
    | cons f route =>
      obtain ⟨w,d,arrives,leaves⟩ := turns e f (by simp)
      cases es with
      | nil => cases first
      | cons x es =>
        have same : x=e := Option.some.inj first
        subst x
        cases es with
        | nil =>
          obtain ⟨k,observes⟩ := typed
          change (match g.wire e with
            | .inl ⟨n,p⟩ => portKind (g.label n).sort p
            | _ => none)=some k at observes
          rw [arrives] at observes
          cases observes
        | cons y es =>
          cases labels with
          | @cons _ _ _ _ middle _ turn rest =>
            have next : y=f ∧middle=a := by
              have actual := turn
              rw [arrives] at actual
              cases actual
              exact ⟨leaves.symm,rfl⟩
            obtain ⟨same,contextEq⟩ := next
            subst y
            subst middle
            have restTyped : ∃ k,accessKind g (f::es)=some k := by
              simpa only [accessKind,List.getLast?_cons_cons] using typed
            obtain ⟨suffix,split,head,remaining⟩ := ih rest restTyped (by simp) rfl
              (by intro x y member; exact turns x y (by
                    simp only [List.tail_cons,List.zip_cons_cons,List.mem_cons]; exact Or.inr member))
            exact ⟨suffix,by change e::f::es=e::((f::route).dropLast++suffix); rw [←split],
              by simpa only [List.getLast?_cons_cons] using head,remaining⟩
end
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

/-- An actual proper-ended path arriving at a non-observable node port must
already contain its next node turn. No continuation is invented. -/
theorem Labelling.typed_nonterminal_departure {es : List (Endpoint g)} {a b : Context}
    (labels : Labelling g es a b) (typed : ∃ k,accessKind g es=some k)
    (e : Endpoint g) (first : es.head?=some e) (node : N) (p : Port (g.label node).sort)
    (arrives : g.wire e=.inl ⟨node,p⟩) (nonterminal : portKind (g.label node).sort p=none) :
    ∃ q rest middle,es=e::(.inl ⟨node,q⟩)::rest ∧
      Traversal (g.label node).index (g.label node).sort p q a middle ∧
      Labelling g ((.inl ⟨node,q⟩)::rest) middle b := by
  cases es with
  | nil => cases first
  | cons x es =>
    have same : x=e := Option.some.inj first
    subst x
    cases es with
    | nil =>
      obtain ⟨k,observes⟩ := typed
      change (match g.wire e with
        | .inl ⟨n,p⟩ => portKind (g.label n).sort p
        | _ => none)=some k at observes
      rw [arrives] at observes
      change portKind (g.label node).sort p=some k at observes
      rw [nonterminal] at observes
      cases observes
    | cons f rest =>
      cases labels with
      | cons turn tail =>
        rw [arrives] at turn
        obtain ⟨q,same,rule⟩ := turn.from_node node p rfl
        subst f
        exact ⟨q,rest,_,rfl,rule,tail⟩
end
end Lamping.AG


