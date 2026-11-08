import Lamping.Lamping.ActionCanonicalResidual
namespace Lamping.AG
open Graph
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed

/-- A finite ordered residual retaining the actual canonical source block.
No assignment or uniform replay conclusion is stored in its constructors. -/
inductive ActionCanonicalBlocks (principal : SiteActionPrincipal site) :
    List (PlugSegment cut s.right.net) → List (Endpoint site.net) → Prop where
  | single (e : Endpoint cut) : ActionCanonicalBlocks principal [.inl e] [site.outsideEnd e]
  | outside {e f : Endpoint cut} {tail old}
      (rest : ActionCanonicalBlocks principal (.inl f::tail) old) :
      ActionCanonicalBlocks principal (.inl e::.inl f::tail) (site.outsideEnd e::old)
  | through {e : Endpoint cut} {exit : s.Frontier} {tail old}
      (inside : List (Endpoint s.right.net)) (front : List (Endpoint site.net))
      (route : ActionCanonicalLocal site principal inside
        (front++[site.outsideEnd (.inr (.inl (.inr exit)))]))
      (start : (front++[site.outsideEnd (.inr (.inl (.inr exit)))]).head?=some (site.outsideEnd e))
      (rest : ActionCanonicalBlocks principal (.inl (.inr (.inl (.inr exit)))::tail) old) :
      ActionCanonicalBlocks principal
        (.inl e::(inside.map Sum.inr++ .inl (.inr (.inl (.inr exit)))::tail)) (front++old)

theorem ActionCanonicalBlocks.erase {principal : SiteActionPrincipal site} {raw old}
    (relation : ActionCanonicalBlocks site principal raw old) :
    LocalBlockResidual cut s.right.net site.net site.outsideEnd raw old := by
  induction relation with
  | single e => exact .single e
  | outside rest ih => exact .outside ih
  | through inside front route start rest ih => exact .through inside front start ih

theorem ActionCanonicalBlocks.head {principal : SiteActionPrincipal site} {raw old}
    (relation : ActionCanonicalBlocks site principal raw old)
    {e : Endpoint cut} (first : raw.head?=some (.inl e)) : old.head?=some (site.outsideEnd e) := by
  induction relation generalizing e with
  | single f => have same := Sum.inl.inj (Option.some.inj first); subst f; rfl
  | @outside f h tail old rest ih =>
    have same := Sum.inl.inj (Option.some.inj first)
    subst f
    rfl
  | @through f exit tail old inside front route start rest ih =>
    have same := Sum.inl.inj (Option.some.inj first)
    subst f
    cases front with
    | nil =>
      have endpoint : site.outsideEnd (.inr (.inl (.inr exit)))=site.outsideEnd e := Option.some.inj start
      simpa only [List.nil_append,endpoint] using ih rfl
    | cons x front => simpa only [List.cons_append,List.head?_cons] using start

private theorem last_append {T : Type} (pre tail : List T) (nonempty : tail≠[]) :
    (pre++tail).getLast?=tail.getLast? := by
  cases result : tail.getLast? with
  | none => exact False.elim (nonempty (List.getLast?_eq_none_iff.mp result))
  | some x => simp only [List.getLast?_append,result,Option.some_or]

theorem PlugExcursions.action_canonical_lift (action : IsAction s) (principal : SiteActionPrincipal site)
    {raw : List (PlugSegment cut s.right.net)} {a b : Context}
    (path : PlugExcursions cut s.right.net raw a b)
    (first last : Endpoint cut) (head : raw.head?=some (.inl first))
    (finish : raw.getLast?=some (.inl last)) :
    ∃ old,ActionCanonicalBlocks site principal raw old ∧Labelling site.net old a b ∧
      old.head?=some (site.outsideEnd first) ∧old.getLast?=some (site.outsideEnd last) := by
  induction path generalizing first last with
  | single e a =>
    have firstEq : e=first := Sum.inl.inj (Option.some.inj head)
    have lastEq : e=last := Sum.inl.inj (Option.some.inj finish)
    subst first; subst last
    exact ⟨[site.outsideEnd e],.single e,.single _ _,rfl,rfl⟩
  | @outside e f tail a middle b turn rest ih =>
    have firstEq : e=first := Sum.inl.inj (Option.some.inj head)
    subst first
    obtain ⟨old,residual,labels,oldHead,oldLast⟩ := ih f last rfl
      (by simpa only [List.getLast?_cons_cons] using finish)
    obtain ⟨post,split⟩ := List.head?_eq_some_iff.mp oldHead
    have actual := turn.outsideEnd site
    rw [←site.outsideEnd_wire] at actual
    refine ⟨site.outsideEnd e::old,.outside residual,?_,rfl,?_⟩
    · rw [split] at labels ⊢
      exact .cons actual labels
    · rw [split,List.getLast?_cons_cons]
      simpa only [split] using oldLast
  | @through e entry exit tail a middle b inside arrival rest ih =>
    have firstEq : e=first := Sum.inl.inj (Option.some.inj head)
    subst first
    have lastTail : (.inl (.inr (.inl (.inr exit)))::tail : List (PlugSegment cut s.right.net)).getLast?=some (.inl last) := by
      have lastEq := last_append ([.inl e]++inside.edges.map (Sum.inr : Endpoint s.right.net → PlugSegment cut s.right.net))
        (.inl (.inr (.inl (.inr exit)))::tail) (by simp)
      rw [←lastEq]
      exact finish
    obtain ⟨old,residual,labels,oldHead,oldLast⟩ := ih _ last rfl lastTail
    obtain ⟨route,canonical,routeLabels⟩ := action_canonical_local site action principal entry exit a middle inside
    obtain ⟨routeHead,routeLast⟩ := canonical.source_endpoints site entry exit inside.start inside.finish
    have start : route.head?=some (site.outsideEnd e) := by
      have comes : site.net.wire (site.outsideEnd e)=site.outsideEnd (.inr (.inl (.inr entry))) := by
        rw [site.outsideEnd_wire,arrival]
      rw [←comes,Pairing.involutive] at routeHead
      exact routeHead
    obtain ⟨front,routeSplit⟩ := List.getLast?_eq_some_iff.mp routeLast
    obtain ⟨post,oldSplit⟩ := List.head?_eq_some_iff.mp oldHead
    refine ⟨front++old,.through inside.edges front (by simpa only [routeSplit] using canonical)
      (by simpa only [routeSplit] using start) residual,?_,?_,?_⟩
    · rw [routeSplit] at routeLabels
      rw [oldSplit] at labels ⊢
      exact routeLabels.join labels
    · cases front with
      | nil =>
        have same : site.outsideEnd (.inr (.inl (.inr exit)))=site.outsideEnd e :=
          Option.some.inj (by simpa only [routeSplit,List.nil_append,List.head?_cons] using start)
        simpa only [List.nil_append,same] using oldHead
      | cons x front => simpa only [routeSplit,List.cons_append,List.head?_cons] using start
    · rw [List.getLast?_append,oldLast,Option.some_or]

/-- The physical whole path chooses its principal component and every literal
canonical source block once. The original assignment is preserved. -/
theorem PathSite.action_canonical_ancestor (action : IsAction s)
    {es : List (Endpoint site.reduce)} {a b : Context} (labels : Labelling site.reduce es a b)
    (first last : Endpoint cut)
    (head : es.head?=some (AG.plugLeft cut s.right.net first))
    (finish : es.getLast?=some (AG.plugLeft cut s.right.net last)) :
    ∃ principal : SiteActionPrincipal site,∃ old,
      ActionCanonicalBlocks site principal (es.map (plugEnd (cut).label s.right.net.label).invFun) old ∧
      Labelling site.net old a b ∧old.head?=some (site.outsideEnd first) ∧
      old.getLast?=some (site.outsideEnd last) := by
  obtain ⟨principal⟩ := site.actionPrincipal_exists
  have raw := labels.local_excursions cut s.right.net first last head finish
  exact ⟨principal,raw.action_canonical_lift site action principal first last
    (by rw [List.head?_map,head]; exact congrArg some ((plugEnd (cut).label s.right.net.label).left_inv (.inl first)))
    (by rw [List.getLast?_map,finish]; exact congrArg some ((plugEnd (cut).label s.right.net.label).left_inv (.inl last)))⟩
end
end Lamping.AG


