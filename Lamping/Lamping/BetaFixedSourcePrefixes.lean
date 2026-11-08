import Lamping.Lamping.FixedBetaDetourBlocks
import Lamping.Lamping.ActionPrincipalInternal
import Lamping.Lamping.LocalTransport
namespace Lamping.AG
open Graph
private theorem no_binding {i kind p q a b}
    (rule : Traversal i kind p q a b) (sort : kind=.op .lam) (role : HEq p lamBind) : False := by
  subst kind
  exact rule.no_binding.1 (eq_of_heq role)
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

private theorem first_ordinary {e f : Endpoint g} {tail : List (Endpoint g)} {a b middle : Context} {count : Nat}
    {edge : BetaEdge g}
    (path : FixedBetaDetourBlocks edge (e::f::tail) a b count)
    (ordinary : LabelledTurn g (g.wire e) f a middle) :
    FixedBetaDetourBlocks edge (f::tail) middle b count := by
  generalize eqs : (e::f::tail : List (Endpoint g))=raw at path
  cases path with
  | single => cases eqs
  | ordinary turn rest =>
    cases eqs
    have same := turn.output_unique ordinary
    subst middle
    exact rest
  | backward x arrival head rest =>
    have same : e=x := (List.cons.inj eqs).1
    subst x
    rw [arrival] at ordinary
    obtain ⟨q,_leaving,rule⟩ := ordinary.from_node edge.lam edge.lamBind rfl
    exact False.elim (no_binding rule (congrArg Label.sort edge.lamLabel) edge.lamBind_role)

/-- Remove an existing ordinary prefix from a stream for ONE fixed beta.
The shared segment is kept in the suffix once; no backward block can have
been consumed, since its first binding turn is never an ordinary turn. -/
theorem FixedBetaDetourBlocks.ordinary_suffix
    {pre post : List (Endpoint g)} {e : Endpoint g} {a middle b : Context} {count : Nat}
    {edge : BetaEdge g}
    (path : FixedBetaDetourBlocks edge (pre++e::post) a b count)
    (before : Labelling g (pre++[e]) a middle) :
    FixedBetaDetourBlocks edge (e::post) middle b count := by
  induction pre generalizing a with
  | nil => cases before with | single => exact path
  | cons x pre ih =>
    cases pre with
    | nil =>
      cases before with
      | cons turn rest =>
        cases rest with
        | single => exact first_ordinary path turn
    | cons y pre =>
      cases before with
      | cons turn rest =>
        have after := first_ordinary path turn
        exact ih after rest
end
section
variable {s : Schema} {K B W V : Type}
variable [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed
/-- Reflect an already present finite internal transparent route. An outside
terminal rules out stopping before its end, even if the given whole path is
control-ended and hence not a typed RootAccess. No path is extended. -/
theorem ExpandedLabelling.outside_internal_route_prefix
    {es : List (Endpoint site.net)} {a b : Context}
    (labels : ExpandedLabelling site.net es a b) (last : Endpoint cut)
    (finish : es.getLast?=some (site.outsideEnd last))
    (route : List (Endpoint site.net)) (nonempty : route≠[])
    (first : es.head?=route.head?)
    (inside : ∀ e∈route,∃ i,e=site.internalEnd i)
    (steps : ∀ e f,(e,f)∈route.zip route.tail →
      ∃ w d,site.net.wire e=.inr (.inr (w,d)) ∧f=.inr (.inr (w,!d))) :
    ∃ suffix,es=route.dropLast++suffix ∧suffix.head?=route.getLast? ∧ExpandedLabelling site.net suffix a b := by
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
              cases turn with
              | ordinary actual => cases actual; exact ⟨leaves.symm,rfl⟩
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
