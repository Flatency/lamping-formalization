import Lamping.Lamping.MatchingBetaLambdaVisibility
import Lamping.Lamping.InitialPathConstruction
namespace Lamping.AG
open Graph Lambda
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.beta i) V) site.closed

private theorem first_entry_impossible
    {root : B} {t : Term} (matching : Matches site.net root t)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (oldT : Transparency site.net root) (empty : site.betaSyntaxFiber root t=[])
    {pre : List (Endpoint site.net)} {a b : Context} (labels : Labelling site.net pre a b)
    (rooted : pre.head?=some (.inr (.inl root)))
    {e : Endpoint cut} {f : (Schema.beta i).Frontier}
    (finish : pre.getLast?=some (site.outsideEnd e))
    (arrival : (cut).wire e=.inr (.inl (.inr f)))
    (entry : f=.inl false ∨ f=.inr false) : False := by
  have last : pre.getLast?=some (site.net.wire (site.outsideEnd (.inr (.inl (.inr f))))) := by
    rw [←arrival,←site.outsideEnd_wire,Pairing.involutive]
    exact finish
  have forward := labels.root_forward_of_flow flow root rooted positive
  rcases entry with rfl | rfl
  · have actual : pre.getLast?=some (site.net.wire (.inl ⟨.inr (.inl ()),appCtx⟩)) := last
    have kind : accessKind site.net pre=some .app := by
      simp only [accessKind,actual,Option.bind_some,Pairing.involutive]
      rfl
    exact site.empty_betaSyntaxFiber_not_visible matching flow positive empty
      ⟨pre,⟨⟨⟨a,b,labels⟩,forward⟩,rooted,⟨.app,kind⟩⟩⟩ actual
  · have actual : pre.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),lamBind⟩)) := last
    have kind : accessKind site.net pre=some .var := by
      simp only [accessKind,actual,Option.bind_some,Pairing.involutive]
      rfl
    exact site.empty_betaSyntaxFiber_not_binding_visible matching flow positive oldT empty
      ⟨pre,⟨⟨⟨a,b,labels⟩,forward⟩,rooted,⟨.var,kind⟩⟩⟩ actual

/-- A genuine RHS wire excursion cannot make its first entrance when the
old syntax fiber is empty. The prefix is extended only along the supplied
finite outside turns; no continuation or generated-path oracle is used. -/
theorem WireExcursions.empty_beta_outside
    {root : B} {t : Term} (matching : Matches site.net root t)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (oldT : Transparency site.net root) (empty : site.betaSyntaxFiber root t=[])
    {raw a b} (path : WireExcursions cut (Schema.beta i).right.net raw a b)
    (directions : BetaEntriesForward site raw)
    {pre : List (Endpoint site.net)} {initial : Context}
    (before : Labelling site.net pre initial a)
    (rooted : pre.head?=some (.inr (.inl root)))
    {first : Endpoint cut} (head : raw.head?=some (.inl first))
    (finish : pre.getLast?=some (site.outsideEnd first)) :
    ∃ outside : List (Endpoint cut), raw=outside.map Sum.inl ∧ Labelling cut outside a b := by
  induction path generalizing pre initial first with
  | single e a => exact ⟨[e],rfl,.single e a⟩
  | @outside e f tail a middle b turn rest ih =>
    have same : first=e := (Sum.inl.inj (Option.some.inj head)).symm
    subst first
    have actual := turn.outsideEnd site
    rw [←site.outsideEnd_wire] at actual
    have joined : Labelling site.net (pre++[site.outsideEnd f]) initial middle := by
      apply before.append_seam (.single _ _)
      intro x y hx hy
      have xeq := Option.some.inj (hx.symm.trans finish)
      have yeq := Option.some.inj hy
      rw [xeq,←yeq]
      exact actual
    have joinedRoot : (pre++[site.outsideEnd f]).head?=some (.inr (.inl root)) := by
      rw [List.head?_append,rooted]
      rfl
    obtain ⟨outside,eqs,labels⟩ := ih
      (fun x mem => directions x (List.mem_cons_of_mem _ mem)) joined joinedRoot rfl
      (by simp only [List.getLast?_append,List.getLast?_singleton,Option.some_or])
    have outsideHead : outside.head?=some f := by
      have h := congrArg List.head? eqs
      rw [List.head?_map] at h
      cases split : outside with
      | nil => rw [split] at h; cases h
      | cons x xs => rw [split] at h; exact congrArg some (Sum.inl.inj (Option.some.inj h)).symm
    obtain ⟨post,outsideEq⟩ := List.head?_eq_some_iff.mp outsideHead
    refine ⟨e::outside,?_,?_⟩
    · simp only [List.map_cons,←eqs]
    · rw [outsideEq] at labels ⊢
      exact .cons turn labels
  | @through e f tail a b arrival rest ih =>
    have same : first=e := (Sum.inl.inj (Option.some.inj head)).symm
    subst first
    exact False.elim (first_entry_impossible site matching flow positive oldT empty before rooted
      finish arrival (directions f (by simp)))
end
end Lamping.AG


