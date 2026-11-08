import Lamping.Lamping.PathDefinitions
namespace Lamping.AG
open Graph

private theorem member_head_or_previous {A : Type} (es : List A) (e : A) (member : e∈es) :
    es.head?=some e ∨∃ previous,(previous,e)∈es.zip es.tail := by
  induction es with
  | nil => cases member
  | cons x xs ih =>
    rcases List.mem_cons.mp member with rfl |member
    · exact Or.inl rfl
    · cases xs with
      | nil => cases member
      | cons y ys =>
        rcases ih member with first |⟨previous,pair⟩
        · have same := Option.some.inj first
          subst e
          exact Or.inr ⟨x,by simp⟩
        · exact Or.inr ⟨previous,List.mem_cons_of_mem _ pair⟩

private theorem member_last_or_next {A : Type} (es : List A) (e : A) (member : e∈es) :
    es.getLast?=some e ∨∃ next,(e,next)∈es.zip es.tail := by
  induction es with
  | nil => cases member
  | cons x xs ih =>
    cases xs with
    | nil =>
      have same := List.mem_singleton.mp member
      subst e
      exact Or.inl rfl
    | cons y ys =>
      rcases List.mem_cons.mp member with rfl |member
      · exact Or.inr ⟨y,by simp⟩
      · rcases ih member with last |⟨next,pair⟩
        · exact Or.inl (by simpa only [List.getLast?_cons_cons] using last)
        · exact Or.inr ⟨next,List.mem_cons_of_mem _ pair⟩

private theorem zip_members {A C : Type} {xs : List A} {ys : List C} {a : A} {b : C}
    (member : (a,b)∈xs.zip ys) : a∈xs ∧b∈ys := by
  induction xs generalizing ys with
  | nil => simp at member
  | cons x xs ih =>
    cases ys with
    | nil => simp at member
    | cons y ys =>
      rcases List.mem_cons.mp member with same |rest
      · have left := congrArg Prod.fst same
        have right := congrArg Prod.snd same
        exact ⟨List.mem_cons.mpr (Or.inl left),List.mem_cons.mpr (Or.inl right)⟩
      · obtain ⟨left,right⟩ := ih rest
        exact ⟨List.mem_cons_of_mem _ left,List.mem_cons_of_mem _ right⟩

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

/-- One supplied finite physical principal corridor, allowing repeated W
vertices and edges. This is geometry of an existing route, never completion. -/
structure TransparentCorridor (g : Net signature N B W) where
  first : NodePort signature N g.label
  last : NodePort signature N g.label
  edges : List (Endpoint g)
  start : edges.head?=some (.inl first)
  finish : edges.getLast?=some (g.wire (.inl last))
  transparent : ∀ e f,(e,f)∈edges.zip edges.tail →
    ∃ w d,g.wire e=.inr (.inr (w,d)) ∧f=.inr (.inr (w,!d))

def TransparentCorridor.vertex (route : TransparentCorridor g) (w : W) : Prop :=
  ∃ d,(.inr (.inr (w,d)) : Endpoint g)∈route.edges

def TransparentCorridor.internal (route : TransparentCorridor g) (e : Endpoint g) : Prop :=
  e=.inl route.first ∨e=.inl route.last ∨
    ∃ w d,route.vertex w ∧e=.inr (.inr (w,d))

/-- Every departure in the actual route belongs to its selected component. -/
theorem TransparentCorridor.departure_internal (route : TransparentCorridor g)
    (e : Endpoint g) (member : e∈route.edges) : route.internal e := by
  rcases member_head_or_previous route.edges e member with first |⟨previous,pair⟩
  · exact Or.inl (Option.some.inj (first.symm.trans route.start))
  · obtain ⟨w,d,_arrives,leaves⟩ := route.transparent previous e pair
    exact Or.inr (Or.inr ⟨w,!d,⟨!d,by rw [←leaves]; exact member⟩,leaves⟩)

/-- Every arrival in the route also lies in the same selected component. -/
theorem TransparentCorridor.arrival_internal (route : TransparentCorridor g)
    (e : Endpoint g) (member : e∈route.edges) : route.internal (g.wire e) := by
  rcases member_last_or_next route.edges e member with last |⟨next,pair⟩
  · have same := Option.some.inj (last.symm.trans route.finish)
    exact Or.inr (Or.inl (by rw [same,Pairing.involutive]))
  · obtain ⟨w,d,arrives,leaves⟩ := route.transparent e next pair
    have nextMember : next∈route.edges := List.mem_of_mem_tail (zip_members pair).2
    exact Or.inr (Or.inr ⟨w,d,⟨!d,by rw [←leaves]; exact nextMember⟩,arrives⟩)

/-- The opposite end of any selected W vertex is an actual arrival. -/
theorem TransparentCorridor.vertex_opposite (route : TransparentCorridor g)
    (w : W) (d : Bool) (member : (.inr (.inr (w,d)) : Endpoint g)∈route.edges) :
    route.internal (g.wire (.inr (.inr (w,!d)))) := by
  rcases member_head_or_previous route.edges (.inr (.inr (w,d))) member with first |⟨previous,pair⟩
  · have impossible := Option.some.inj (first.symm.trans route.start)
    cases impossible
  · obtain ⟨v,side,arrives,leaves⟩ := route.transparent previous (.inr (.inr (w,d))) pair
    have vertexSame := Sum.inr.inj (Sum.inr.inj leaves)
    have sameW : w=v := congrArg Prod.fst vertexSame
    have sameD : d= !side := congrArg Prod.snd vertexSame
    subst v
    have opposite : (!d)=side := by rw [sameD]; cases side <;> rfl
    rw [opposite,←arrives,Pairing.involutive]
    exact route.departure_internal previous (zip_members pair).1

/-- The actual wire pairing restricts to the route's two endpoint ports and
all selected W vertices, including both sides. No outside component is lost. -/
theorem TransparentCorridor.wire_internal (route : TransparentCorridor g)
    (e : Endpoint g) (member : route.internal e) : route.internal (g.wire e) := by
  rcases member with first |last |⟨w,d,⟨side,occurs⟩,atVertex⟩
  · subst e
    obtain ⟨tail,split⟩ := List.head?_eq_some_iff.mp route.start
    apply route.arrival_internal
    rw [split]; simp
  · subst e
    obtain ⟨before,split⟩ := List.getLast?_eq_some_iff.mp route.finish
    have occurs : g.wire (.inl route.last)∈route.edges := by rw [split]; simp
    exact route.departure_internal _ occurs
  · subst e
    by_cases same : d=side
    · subst d
      exact route.arrival_internal _ occurs
    · have equal : d= !side := by cases d <;> cases side <;> simp_all
      rw [equal]
      exact route.vertex_opposite w side occurs
end
end Lamping.AG
