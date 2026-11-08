import Lamping.Lamping.TransparentCorridors
namespace Lamping.AG
open Graph

private theorem mapped_adjacent {A C : Type} (f : A → C) (es : List A) (x y : C)
    (member : (x,y)∈(es.map f).zip (es.map f).tail) :
    ∃ a b,(a,b)∈es.zip es.tail ∧x=f a ∧y=f b := by
  induction es with
  | nil => simp at member
  | cons a tail ih =>
    cases tail with
    | nil => simp at member
    | cons b rest =>
      rcases List.mem_cons.mp member with same |member
      · exact ⟨a,b,by simp,congrArg Prod.fst same,congrArg Prod.snd same⟩
      · obtain ⟨u,v,pair,left,right⟩ := ih member
        exact ⟨u,v,List.mem_cons_of_mem _ pair,left,right⟩

section
variable {N M B W V : Type} [FiniteNames N] [FiniteNames M] [FiniteNames B]
variable [FiniteNames W] [FiniteNames V]
variable {g : Net signature N B W} {h : Net signature M B V}

/-- Reindex the supplied physical corridor by the actual whole graph iso. -/
def TransparentCorridor.map (route : TransparentCorridor g) (iso : NetIso g h) :
    TransparentCorridor h where
  first := iso.ports route.first
  last := iso.ports route.last
  edges := route.edges.map iso.ends
  start := by rw [List.head?_map,route.start,Option.map_some]; exact congrArg some (iso.node_end _)
  finish := by
    rw [List.getLast?_map,route.finish,Option.map_some,iso.wiring,iso.node_end]
  transparent := by
    intro x y member
    obtain ⟨a,b,pair,left,right⟩ := mapped_adjacent iso.ends route.edges x y member
    obtain ⟨w,d,arrives,leaves⟩ := route.transparent a b pair
    refine ⟨iso.vertices w,d,?_,?_⟩
    · rw [left,←iso.wiring,arrives,iso.vertex_end]
    · rw [right,leaves,iso.vertex_end]

/-- A vertex is selected exactly when its original physical vertex occurs in
the old corridor. No extra vertices or components are introduced. -/
theorem TransparentCorridor.map_vertex_iff (route : TransparentCorridor g) (iso : NetIso g h)
    (v : V) : (route.map iso).vertex v ↔route.vertex (iso.vertices.invFun v) := by
  constructor
  · rintro ⟨d,member⟩
    obtain ⟨e,oldMember,same⟩ := List.mem_map.mp member
    have image : iso.ends (.inr (.inr (iso.vertices.invFun v,d)))=.inr (.inr (v,d)) := by
      rw [iso.vertex_end,iso.vertices.right_inv]
    have old : e=.inr (.inr (iso.vertices.invFun v,d)) := iso.ends.injective (same.trans image.symm)
    exact ⟨d,by rw [←old]; exact oldMember⟩
  · rintro ⟨d,member⟩
    refine ⟨d,List.mem_map.mpr ⟨.inr (.inr (iso.vertices.invFun v,d)),member,?_⟩⟩
    rw [iso.vertex_end,iso.vertices.right_inv]
end
end Lamping.AG
