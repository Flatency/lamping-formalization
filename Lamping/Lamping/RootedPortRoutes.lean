import Lamping.Lamping.EncodedAddressing
namespace Lamping.AG
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable (g : Net signature N B W)
/-- A real labelled root-to-port route. Its physical target is specified; merely
having the same port kind or the same syntax shape elsewhere is insufficient. -/
def RootedPortRoute (root : B) (target : Endpoint g) : Prop :=
  ∃ (es : List (Endpoint g)) (a b : Context),Labelling g es a b ∧
    es.head?=some (.inr (.inl root)) ∧es.getLast?=some (g.wire target)
end
private theorem last_append_nonempty {T : Type} (xs ys : List T) (nonempty : ys≠[]) :
    (xs++ys).getLast?=ys.getLast? := by
  rw [List.getLast?_append]
  cases h : ys.getLast? with
  | none => exact False.elim (nonempty (List.getLast?_eq_none_iff.mp h))
  | some => rfl
section
variable {K R B F W V : Type} [FiniteNames K] [FiniteNames R] [FiniteNames B]
  [FiniteNames F] [FiniteNames W] [FiniteNames V]
variable (c : Net signature K (B⊕F) W) (r : Net signature R F V)
/-- An explicit-list form of child entry, retaining the actual concatenation
so later endpoint transport is independent of existential witness choices. -/
theorem Labelling.enter_child_exact {root : B} {entry : F}
    (first : LocalPath c (.inl root) (.inr entry) a b)
    {es : List (Endpoint r)} (child : Labelling r es b d)
    (head : es.head?=some (.inr (.inl entry))) :
    Labelling (plug c r) (first.edges.map (AG.plugLeft c r)++es.map (AG.plugRight c r)) a d := by
  apply (first.labeling.plugLeft c r).append_seam (child.plugRight c)
  intro left right last start
  have leftEq : left=AG.plugLeft c r (c.wire (.inr (.inl (.inr entry)))) := by
    have original : (first.edges.map (AG.plugLeft c r)).getLast?=
        some (AG.plugLeft c r (c.wire (.inr (.inl (.inr entry))))) := by
      rw [List.getLast?_map,first.finish]; rfl
    exact Option.some.inj (last.symm.trans original)
  have rightEq : right=AG.plugRight c r (.inr (.inl entry)) := by
    have original : (es.map (AG.plugRight c r)).head?=some (AG.plugRight c r (.inr (.inl entry))) := by
      rw [List.head?_map,head]; rfl
    exact Option.some.inj (start.symm.trans original)
  rw [leftEq,rightEq,←plugLeft_wire,Pairing.involutive]
  exact .transparent (Sum.inr entry) false b

theorem RootedPortRoute.enter_child {root : B} {entry : F} {target : Endpoint r}
    (route : RootedPortRoute r entry target)
    (first : ∀ a,LocalPath c (.inl root) (.inr entry) a a) :
    RootedPortRoute (plug c r) root (AG.plugRight c r target) := by
  obtain ⟨es,a,b,labels,head,last⟩ := route
  have nonempty : es.map (AG.plugRight c r)≠[] := by
    intro empty
    have heads := congrArg List.head? empty
    rw [List.head?_map,head] at heads
    cases heads
  refine ⟨(first a).edges.map (AG.plugLeft c r)++es.map (AG.plugRight c r),a,b,
    labels.enter_child_exact c r (first a) head,?_,?_⟩
  · rw [List.head?_append,List.head?_map,(first a).start]; rfl
  · rw [last_append_nonempty _ _ nonempty,List.getLast?_map,last]
    exact congrArg some (plugRight_wire c r target).symm
end
section
variable {N M B C W V : Type} [FiniteNames N] [FiniteNames M] [FiniteNames B]
  [FiniteNames C] [FiniteNames W] [FiniteNames V]
variable (g : Net signature N B W) (h : Net signature M C V)
theorem RootedPortRoute.unionLeft {root : B} {target : Endpoint g} (route : RootedPortRoute g root target) :
    RootedPortRoute (unionNet g h) (.inl root) (InitialOffsets.unionL g h target) := by
  obtain ⟨es,a,b,labels,head,last⟩ := route
  refine ⟨es.map (InitialOffsets.unionL g h),a,b,labels.unionLeft g h,?_,?_⟩
  · rw [List.head?_map,head]; rfl
  · rw [List.getLast?_map,last]; exact congrArg some (union_left g h target).symm

theorem RootedPortRoute.unionRight {root : C} {target : Endpoint h} (route : RootedPortRoute h root target) :
    RootedPortRoute (unionNet g h) (.inr root) (InitialOffsets.unionR g h target) := by
  obtain ⟨es,a,b,labels,head,last⟩ := route
  refine ⟨es.map (InitialOffsets.unionR g h),a,b,labels.unionRight g h,?_,?_⟩
  · rw [List.head?_map,head]; rfl
  · rw [List.getLast?_map,last]; exact congrArg some (union_right g h target).symm
end
end Lamping.AG
