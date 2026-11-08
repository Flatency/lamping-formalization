import Lamping.Lamping.ActionCanonicalAssembly
namespace Lamping.AG
open Graph
section
variable {f : Op} {i j : Nat} {lt : i<j}
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature}
variable (site : PathSite (.fanAction f i j lt) kept (B:=B) (W:=W) (V:=V))

theorem FanCanonicalLocal.fixed_source_unique {principal : SiteActionPrincipal site}
    {rhs first second} (left : FanCanonicalLocal site principal rhs first)
    (right : FanCanonicalLocal site principal rhs second) : first=second := by
  cases left <;> cases right <;>
    simp_all [reverseEdges]
end
section
variable {s : Schema} {k : Nat}
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))
variable (single : Bij Unit (Aux s.active))
theorem UnaryCanonicalLocal.fixed_source_unique {principal : SiteActionPrincipal site}
    {rhs first second} (left : UnaryCanonicalLocal site single (k:=k) principal rhs first)
    (right : UnaryCanonicalLocal site single (k:=k) principal rhs second) : first=second := by
  cases left <;> cases right <;>
    simp_all [reverseEdges]
end
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))
theorem ActionCanonicalLocal.fixed_source_unique {principal : SiteActionPrincipal site}
    {rhs first second} (left : ActionCanonicalLocal site principal rhs first)
    (right : ActionCanonicalLocal site principal rhs second) : first=second := by
  cases left with
  | fan left => cases right with | fan right => exact left.fixed_source_unique _ right
  | cro left => cases right with | cro right => exact left.fixed_source_unique _ _ right
  | bra left => cases right with | bra right => exact left.fixed_source_unique _ _ right

private theorem right_block_unique {L R : Type} {xs ys : List R} {x y : L}
    {tail post : List (L⊕R)}
    (same : xs.map Sum.inr++Sum.inl x::tail=ys.map Sum.inr++Sum.inl y::post) :
    xs=ys ∧x=y ∧tail=post := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => have eqs := List.cons.inj same; exact ⟨rfl,Sum.inl.inj eqs.1,eqs.2⟩
    | cons h ys => cases same
  | cons h xs ih =>
    cases ys with
    | nil => cases same
    | cons k ys =>
      obtain ⟨head,rest⟩ := List.cons.inj same
      have heads := Sum.inr.inj head
      obtain ⟨rfl,rfl,rfl⟩ := ih rest
      subst k
      exact ⟨rfl,rfl,rfl⟩

theorem ActionCanonicalBlocks.fixed_source_unique_of_eq
    {principal : SiteActionPrincipal site} {raw otherRaw first second}
    (left : ActionCanonicalBlocks site principal raw first)
    (right : ActionCanonicalBlocks site principal otherRaw second)
    (same : raw=otherRaw) : first=second := by
  induction left generalizing otherRaw second with
  | single e =>
    cases right with
    | single f => cases same; rfl
    | outside other => cases same
    | through inside front route start rest =>
      have nonempty := route.nonempty site
      cases inside with
      | nil => exact False.elim (nonempty rfl)
      | cons h inside => simp only [List.map_cons,List.cons_append] at same; cases same
  | @outside e f tail old rest ih =>
    cases right with
    | single f => cases same
    | @outside h k post other remaining =>
      obtain ⟨initial,tailEq⟩ := List.cons.inj same
      have heads := Sum.inl.inj initial
      subst h
      exact congrArg (_::·) (ih remaining tailEq)
    | through inside front route start remaining =>
      have nonempty := route.nonempty site
      cases inside with
      | nil => exact False.elim (nonempty rfl)
      | cons h inside => simp only [List.map_cons,List.cons_append] at same; cases same
  | @through e exit tail old inside front route start rest ih =>
    cases right with
    | single f =>
      have nonempty := route.nonempty site
      cases inside with
      | nil => exact False.elim (nonempty rfl)
      | cons h inside => simp only [List.map_cons,List.cons_append] at same; cases same
    | outside remaining =>
      have nonempty := route.nonempty site
      cases inside with
      | nil => exact False.elim (nonempty rfl)
      | cons h inside => simp only [List.map_cons,List.cons_append] at same; cases same
    | @through h otherExit post other otherInside otherFront otherRoute otherStart remaining =>
      obtain ⟨_,after⟩ := List.cons.inj same
      obtain ⟨insideEq,exitEq,tailEq⟩ := right_block_unique after
      have exits := Sum.inr.inj (Sum.inl.inj (Sum.inr.inj exitEq))
      subst otherExit
      subst otherInside
      subst post
      have oldEq := route.fixed_source_unique site otherRoute
      have frontEq := List.append_cancel_right oldEq
      rw [frontEq,ih remaining rfl]

/-- The same actual reduced literal path fixes its old canonical route.
This direction does not assert that old paths distinguish fan copies. -/
theorem ActionCanonicalBlocks.fixed_source_unique
    {principal : SiteActionPrincipal site} {raw first second}
    (left : ActionCanonicalBlocks site principal raw first)
    (right : ActionCanonicalBlocks site principal raw second) : first=second :=
  left.fixed_source_unique_of_eq site right rfl
end

section
variable {f : Op} {i j : Nat} {lt : i<j}
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature}
variable (site : PathSite (.fanAction f i j lt) kept (B:=B) (W:=W) (V:=V))

/-- Two real passive fan copies have different RHS routes and the same old
route. Thus local canonical source uniqueness has no unrestricted converse. -/
theorem FanCanonicalLocal.passive_copies_split (principal : SiteActionPrincipal site)
    (p q : Aux f) :
    FanCanonicalLocal site principal (fanPassiveEdges false p q) (site.passiveCanonical p q) ∧
    FanCanonicalLocal site principal (fanPassiveEdges true p q) (site.passiveCanonical p q) ∧
    fanPassiveEdges (i:=i) (j:=j) false p q≠fanPassiveEdges (i:=i) (j:=j) true p q := by
  exact ⟨.passive false p q,.passive true p q,by simp [fanPassiveEdges]⟩
end
end Lamping.AG