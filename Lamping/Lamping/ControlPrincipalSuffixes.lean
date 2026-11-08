import Lamping.Lamping.ControlPrincipalPrefixes
import Lamping.Lamping.ActionCanonicalRoutes
namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

/-- Reflect a specified transparent prefix of an existing path ending at a
wired boundary. The boundary prevents an early stop inside that route. -/
theorem Labelling.boundary_transparent_prefix {es : List (Endpoint g)} {a b : Context}
    (labels : Labelling g es a b) (root : B) (finish : es.getLast?=some (g.wire (.inr (.inl root))))
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
          have ends : e=g.wire (.inr (.inl root)) := Option.some.inj (by simpa using finish)
          rw [ends,Pairing.involutive] at arrives
          cases arrives
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
            have restFinish : (f::es).getLast?=some (g.wire (.inr (.inl root))) := by
              simpa only [List.getLast?_cons_cons] using finish
            obtain ⟨suffix,split,head,remaining⟩ := ih rest restFinish (by simp) rfl
              (by intro x y member; exact turns x y (by
                    simp only [List.tail_cons,List.zip_cons_cons,List.mem_cons]; exact Or.inr member))
            exact ⟨suffix,by change e::f::es=e::((f::route).dropLast++suffix); rw [←split],
              by simpa only [List.getLast?_cons_cons] using head,remaining⟩
end

section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))

/-- Every existing rooted path arriving at the passive principal already has
one fixed active-control writer. This remains the same physical auxiliary
under every labelling of that same path. It asserts no new continuation. -/
theorem PathSite.rooted_control_writer
    {es : List (Endpoint site.net)} {a b : Context}
    (labels : Labelling site.net es a b) (root : B)
    (first : es.head?=some (.inr (.inl root)))
    (last : es.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩))) :
    ∃ q : Aux s.active,∀ input output,Labelling site.net es input output →
      ∃ writerInput,Traversal s.low (.op s.active) (.inr q) (.inl ()) writerInput output := by
  obtain ⟨route,routeHead,routeLast,turns⟩ := site.reverse_principal_route
  have nonempty : route≠[] := by intro empty; rw [empty] at routeHead; cases routeHead
  have reversedHead : (reverseEdges es).head?=route.head? := by
    simp only [reverseEdges,List.head?_map,List.head?_reverse,last,Option.map_some,Pairing.involutive]
    exact routeHead.symm
  have reversedLast : (reverseEdges es).getLast?=some (site.net.wire (.inr (.inl root))) := by
    simp only [reverseEdges,List.getLast?_map,List.getLast?_reverse,first,Option.map_some]
  obtain ⟨suffix,split,suffixHead,remaining⟩ := labels.reverse.boundary_transparent_prefix
    root reversedLast route nonempty reversedHead turns
  rw [routeLast] at suffixHead
  have suffixLast : suffix.getLast?=some (site.net.wire (.inr (.inl root))) := by
    have same : (reverseEdges es).getLast?=suffix.getLast? := by
      rw [split]
      cases suffix with
      | nil => cases suffixHead
      | cons x xs => simp only [List.getLast?_append,List.getLast?_cons,Option.some_or]
    exact same.symm.trans reversedLast
  cases suffix with
  | nil => cases suffixHead
  | cons e rest =>
    have same : e=site.net.wire (.inl ⟨.inr (.inl ()),.inl ()⟩) := Option.some.inj suffixHead
    subst e
    cases rest with
    | nil =>
      have equal : site.net.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)=site.net.wire (.inr (.inl root)) := Option.some.inj (by simpa using suffixLast)
      have impossible := congrArg site.net.wire.mate equal
      simp only [Pairing.involutive] at impossible
      cases impossible
    | cons next rest =>
      cases remaining with
      | @cons _ _ _ _ middle _ turn tail =>
        rw [Pairing.involutive] at turn
        obtain ⟨port,nextEq,rule⟩ := turn.from_node (.inr (.inl ())) (.inl ()) rfl
        subst next
        change Traversal s.low (.op s.active) (.inl ()) port b middle at rule
        cases port with
        | inl u => cases u; exact False.elim (rule.distinct rfl)
        | inr q =>
          refine ⟨q,?_⟩
          intro input output changed
          obtain ⟨newSuffix,newSplit,_,newRemaining⟩ := changed.reverse.boundary_transparent_prefix
            root reversedLast route nonempty reversedHead turns
          have suffixEq : newSuffix=site.net.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)::
              (.inl ⟨.inr (.inl ()),.inr q⟩)::rest :=
            (List.append_cancel_left (split.symm.trans newSplit)).symm
          rw [suffixEq] at newRemaining
          cases newRemaining with
          | cons newTurn tail =>
            rw [Pairing.involutive] at newTurn
            cases newTurn with
            | node node p q actual => exact ⟨_,actual.reverse⟩
end
end Lamping.AG



