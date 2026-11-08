import Lamping.Lamping.UnaryCanonicalComparison
namespace Lamping.AG
open Graph
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed
private theorem outside_injective : Function.Injective site.outsideEnd := by
  intro e f same
  let split := fragmentEnd (B:=B) (W:=W) site.net.label (pathPartition s V)
  have mapped := congrArg split same
  change split (split.invFun (.inl e))=split (split.invFun (.inl f)) at mapped
  simpa only [split.right_inv,Sum.inl.injEq] using mapped

theorem ActionCanonicalLocal.front_tail_internal {principal : SiteActionPrincipal site}
    {rhs old front ending} (route : ActionCanonicalLocal site principal rhs old)
    (split : old=front++[ending]) :
    ∀ e∈front.tail,∃ index,e=site.internalEnd index := by
  have frontEq : front=old.dropLast := by rw [split,List.dropLast_concat]
  subst front
  have crossTail (p : Aux s.active) (q : Aux s.passive) :
      ∀ e∈(principal.crossing site p q).dropLast.tail,∃ index,e=site.internalEnd index := by
    have drop : (principal.crossing site p q).dropLast=
        site.net.wire (.inl ⟨.inr (.inl ()),.inr p⟩)::principal.edges := by
      change ((site.net.wire (.inl ⟨.inr (.inl ()),.inr p⟩)::principal.edges)++[_]).dropLast=_
      exact List.dropLast_concat
    rw [drop,List.tail_cons]
    exact principal.internal_segments site
  have backTail (p : Aux s.active) (q : Aux s.passive) :
      ∀ e∈(reverseEdges (principal.crossing site p q)).dropLast.tail,∃ index,e=site.internalEnd index := by
    have drop : (reverseEdges (principal.crossing site p q)).dropLast=
        site.net.wire (.inl ⟨.inr (.inr ()),.inr q⟩)::reverseEdges principal.edges := by
      rw [principal.reverse_crossing_edges site p q]
      change ((site.net.wire (.inl ⟨.inr (.inr ()),.inr q⟩)::reverseEdges principal.edges)++[_]).dropLast=_
      exact List.dropLast_concat
    rw [drop,List.tail_cons]
    exact principal.reverse_internal_segments site
  cases route with
  | fan inside => cases inside with
    | cross p q => exact crossTail p q
    | backward p q => exact backTail p q
    | passive branch p q => simp [PathSite.passiveCanonical]
  | cro inside => cases inside with
    | cross q => exact crossTail () q
    | backward q => exact backTail () q
    | passive p q => simp [PathSite.passiveCanonical]
  | bra inside => cases inside with
    | cross q => exact crossTail () q
    | backward q => exact backTail () q
    | passive p q => simp [PathSite.passiveCanonical]

private theorem cut_internal_front {front rest pre post : List (Endpoint site.net)} {pivot : Endpoint cut}
    (internal : ∀ e∈front,∃ index,e=site.internalEnd index)
    (split : front++rest=pre++site.outsideEnd pivot::post) :
    ∃ middle,pre=front++middle ∧rest=middle++site.outsideEnd pivot::post := by
  induction front generalizing pre with
  | nil => exact ⟨pre,rfl,split⟩
  | cons e front ih =>
    cases pre with
    | nil =>
      have first := (List.cons.inj split).1
      obtain ⟨index,inside⟩ := internal e (by simp)
      exact False.elim (site.internal_outside_ne index pivot (inside.symm.trans first))
    | cons x pre =>
      have parts := List.cons.inj split
      have head := parts.1
      subst x
      obtain ⟨middle,before,after⟩ := ih
        (fun e member=>internal e (List.mem_cons_of_mem _ member)) parts.2
      exact ⟨middle,congrArg (e::·) before,after⟩
private theorem raw_prefix_shape {T U : Type} {e pivot : T} {tail before after : List (T⊕U)}
    (split : Sum.inl e::tail=before++Sum.inl pivot::after) :
    ∃ rest,before++[Sum.inl pivot]=Sum.inl e::rest := by
  cases before with
  | nil =>
    have first := (List.cons.inj split).1
    exact ⟨[],congrArg (fun x=>[x]) first.symm⟩
  | cons x before =>
    have first := (List.cons.inj split).1
    refine ⟨before++[Sum.inl pivot],?_⟩
    simpa only [List.cons_append] using congrArg (·::(before++[Sum.inl pivot])) first.symm

/-- A supplied outside occurrence cuts with one shared raw/old segment.
The cut may be the first outside segment of a canonical local block. -/
theorem ActionCanonicalBlocks.split_at_outside
    {principal : SiteActionPrincipal site} {raw old}
    (relation : ActionCanonicalBlocks site principal raw old)
    {before after : List (Endpoint site.net)} (pivot : Endpoint cut)
    (split : old=before++site.outsideEnd pivot::after) :
    ∃ rawBefore rawAfter,raw=rawBefore++Sum.inl pivot::rawAfter ∧
      ActionCanonicalBlocks site principal (rawBefore++[Sum.inl pivot]) (before++[site.outsideEnd pivot]) ∧
      ActionCanonicalBlocks site principal (Sum.inl pivot::rawAfter) (site.outsideEnd pivot::after) := by
  induction relation generalizing before after with
  | single e =>
    cases before with
    | nil =>
      have first := outside_injective site (List.cons.inj split).1
      subst e
      have afterEmpty := (List.cons.inj split).2.symm
      subst after
      exact ⟨[],[],rfl,.single pivot,.single pivot⟩
    | cons x before =>
      have lengths := congrArg List.length split
      simp only [List.length_cons,List.length_append,List.length_nil] at lengths
      omega
  | @outside e f tail old rest ih =>
    cases before with
    | nil =>
      have parts := List.cons.inj split
      have first := outside_injective site parts.1
      subst e
      refine ⟨[],.inl f::tail,rfl,.single pivot,?_⟩
      simpa only [parts.2] using ActionCanonicalBlocks.outside (e:=pivot) rest
    | cons x before =>
      have parts := List.cons.inj split
      have first := parts.1
      subst x
      obtain ⟨rawBefore,rawAfter,rawSplit,left,right⟩ := ih parts.2
      obtain ⟨rawTail,rawShape⟩ := raw_prefix_shape rawSplit
      refine ⟨.inl e::rawBefore,rawAfter,?_,?_,right⟩
      · exact congrArg (Sum.inl e::·) rawSplit
      · change ActionCanonicalBlocks site principal (Sum.inl e::(rawBefore++[Sum.inl pivot]))
          (site.outsideEnd e::(before++[site.outsideEnd pivot]))
        rw [rawShape] at left ⊢
        exact .outside left
  | @through e exit tail old inside front route start rest ih =>
    cases before with
    | nil =>
      have fullHead := ActionCanonicalBlocks.head site (.through inside front route start rest) rfl
      rw [split] at fullHead
      have first := outside_injective site (Option.some.inj fullHead).symm
      subst e
      refine ⟨[],inside.map Sum.inr++Sum.inl (.inr (.inl (.inr exit)))::tail,rfl,.single pivot,?_⟩
      simpa only [split] using ActionCanonicalBlocks.through inside front route start rest
    | cons x before =>
      have frontNonempty := canonical_front_nonempty site route
      cases front with
      | nil => exact False.elim (frontNonempty rfl)
      | cons first insideOld =>
        have entry := Option.some.inj start
        subst first
        have parts := List.cons.inj split
        have same := parts.1
        subst x
        have allInside : ∀ point∈insideOld,∃ index,point=site.internalEnd index := by
          exact route.front_tail_internal site rfl
        obtain ⟨middle,beforeSplit,oldSplit⟩ := cut_internal_front site allInside parts.2
        obtain ⟨rawBefore,rawAfter,rawSplit,left,right⟩ := ih oldSplit
        obtain ⟨rawTail,rawShape⟩ := raw_prefix_shape rawSplit
        refine ⟨.inl e::(inside.map Sum.inr++rawBefore),rawAfter,?_,?_,right⟩
        · change Sum.inl e::(inside.map Sum.inr++Sum.inl (.inr (.inl (.inr exit)))::tail)=
            Sum.inl e::((inside.map Sum.inr++rawBefore)++Sum.inl pivot::rawAfter)
          rw [List.append_assoc,←rawSplit]
        · change ActionCanonicalBlocks site principal
            (Sum.inl e::((inside.map Sum.inr++rawBefore)++[Sum.inl pivot]))
            (site.outsideEnd e::(before++[site.outsideEnd pivot]))
          rw [List.append_assoc,rawShape,beforeSplit,List.append_assoc]
          rw [rawShape] at left
          simpa only [List.cons_append,List.append_assoc] using
            ActionCanonicalBlocks.through inside (site.outsideEnd e::insideOld) route start left
end
end Lamping.AG