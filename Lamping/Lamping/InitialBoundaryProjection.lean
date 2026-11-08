import Lamping.Lamping.InitialTraceShape
import Lamping.Lamping.InitialAppRoutes
namespace Lamping.AG.InitialOffsets
open Graph Lambda
private theorem last_append_nonempty {T : Type} (xs ys : List T) (nonempty : ys≠[]) :
    (xs++ys).getLast?=ys.getLast? := by
  rw [List.getLast?_append]
  cases h : ys.getLast? with
  | none => exact False.elim (nonempty (List.getLast?_eq_none_iff.mp h))
  | some v => rfl
private theorem map_last_reflect {S T : Type} (f : S → T) (injective : Function.Injective f)
    (xs : List S) (y : S) (h : (xs.map f).getLast?=some (f y)) : xs.getLast?=some y := by
  rw [List.getLast?_map] at h
  cases last : xs.getLast? with
  | none => simp [last] at h
  | some v =>
    simp only [last,Option.map_some,Option.some.injEq] at h
    have eq := injective h
    rw [eq]
/-- Boundary form of the genuine first-seam decomposition. The no-stay input
is a property of the finite source patch, independent of the child path. -/
theorem LocalPath.outer_child
    {K R B F W V : Type} [FiniteNames K] [FiniteNames R] [FiniteNames B]
    [FiniteNames F] [FiniteNames W] [FiniteNames V]
    (c : Net signature K (B⊕F) W) (r : Net signature R F V)
    {bp : B → Bool} {fp : F → Bool} {wp : W → Bool} {vp : V → Bool}
    (cflow : FlowOn c (Sum.elim bp (fun z => !(fp z))) wp)
    (rflow : FlowOn r fp vp)
    (noReturn : ∀ z z' A B', fp z=false → fp z'=true → LocalPath c (.inr z) (.inr z') A B' → False)
    (x y : B) (out : bp x=true)
    (noStay : ∀ A B', LocalPath c (.inl x) (.inl y) A B' → False)
    {a b : Context} (p : LocalPath (plug c r) x y a b) :
    ∃ (z z' : F) (mid last : Context)
      (first : LocalPath c (.inl x) (.inr z) a mid)
      (middle : LocalPath r z z' mid last)
      (suffix : LocalPath c (.inr z') (.inl y) last b),
      fp z=true ∧ fp z'=false ∧
      p.edges=first.edges.map (plugLeft c r) ++ middle.edges.map (plugRight c r) ++
        suffix.edges.map (plugLeft c r) := by
  rcases p with ⟨es,start,finish,labels⟩
  cases es with
  | nil => simp at start
  | cons e tail =>
    simp only [List.head?_cons,Option.some.injEq] at start; subst e
    change Labelling (plug c r) (plugLeft c r (.inr (.inl (.inl x)))::tail) a b at labels
    have localFinish : (plugLeft c r (.inr (.inl (.inl x)))::tail).getLast?=
        some (plugLeft c r (c.wire (.inr (.inl (.inl y))))) := by
      rw [←plugLeft_wire]; exact finish
    rcases labels.outer_child_decompose c r cflow rflow noReturn (x:=.inr (.inl (.inl x))) out localFinish with
      ⟨xs,eq,stay⟩ | ⟨xs,z,z',mid,last,middle,ys,entry,exit,eq,leading,entryFinish,trailing⟩
    · have sourceFinish : (.inr (.inl (.inl x))::xs).getLast?=some (c.wire (.inr (.inl (.inl y)))) := by
        apply map_last_reflect (plugLeft c r)
          (fun _ _ h => by have same := (plugEnd c.label r.label).injective h; exact Sum.inl.inj same)
        change (plugLeft c r (.inr (.inl (.inl x)))::xs.map (plugLeft c r)).getLast?=_
        rw [←eq]
        exact localFinish
      exact False.elim (noStay a b ⟨_,rfl,sourceFinish,stay⟩)
    · have suffixFinish : (.inr (.inl (.inr z'))::ys).getLast?=some (c.wire (.inr (.inl (.inl y)))) := by
        apply map_last_reflect (plugLeft c r)
          (fun _ _ h => by have same := (plugEnd c.label r.label).injective h; exact Sum.inl.inj same)
        rw [eq] at localFinish
        change (((.inr (.inl (.inl x))::xs).map (plugLeft c r) ++ middle.edges.map (plugRight c r)) ++
          (.inr (.inl (.inr z'))::ys).map (plugLeft c r)).getLast?=_ at localFinish
        rw [last_append_nonempty _ _ (by simp)] at localFinish
        exact localFinish
      refine ⟨z,z',mid,last,⟨_,rfl,entryFinish,leading⟩,middle,⟨_,rfl,suffixFinish,trailing⟩,entry,exit,?_⟩
      change (plugLeft c r (.inr (.inl (.inl x)))::tail)=((.inr (.inl (.inl x))::xs).map (plugLeft c r) ++ middle.edges.map (plugRight c r)) ++ (.inr (.inl (.inr z'))::ys).map (plugLeft c r)
      rw [eq]
      rfl
end Lamping.AG.InitialOffsets
