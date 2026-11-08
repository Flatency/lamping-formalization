import Lamping.Lamping.PlugPrefixExcursions
namespace Lamping.AG
open Graph
section
variable {K R B F W V : Type} [FiniteNames K] [FiniteNames R] [FiniteNames B]
  [FiniteNames F] [FiniteNames W] [FiniteNames V]
variable (c : Net signature K (B⊕F) W) (r : Net signature R F V)

private theorem last_append {T : Type} (pre tail : List T) (nonempty : tail≠[]) :
    (pre++tail).getLast?=tail.getLast? := by
  cases result : tail.getLast? with
  | none => exact False.elim (nonempty (List.getLast?_eq_none_iff.mp result))
  | some x => simp only [List.getLast?_append,result,Option.some_or]

/-- The last genuinely RHS block is preceded by a complete actual outside
prefix. Every context and raw occurrence is retained, with no completion. -/
structure PendingRhsBlock (es : List (PlugSegment c r)) (a b : Context) where
  pre : List (PlugSegment c r)
  last : Endpoint c
  enter : F
  middle : Context
  inside : List (Endpoint r)
  equation : es=pre++inside.map Sum.inr
  prefixPath : PlugExcursions c r pre a middle
  prefixHead : pre.head?=es.head?
  prefixLast : pre.getLast?=some (.inl last)
  arrival : c.wire last=.inr (.inl (.inr enter))
  insideHead : inside.head?=some (.inr (.inl enter))
  insideLabels : Labelling r inside middle b

theorem PendingRhsBlock.labelling {es : List (PlugSegment c r)} {a b : Context}
    (pending : PendingRhsBlock c r es a b) : PlugLabelling c r es a b := by
  have left := pending.prefixPath.labelling c r
  have right := PlugLabelling.of_right c r pending.insideLabels
  have head : (pending.inside.map (Sum.inr : Endpoint r → PlugSegment c r)).head?=
      some (.inr (.inr (.inl pending.enter))) := by rw [List.head?_map,pending.insideHead]; rfl
  have turn : PlugTurn c r (plugSegmentWire c r (.inl pending.last))
      (.inr (.inr (.inl pending.enter))) pending.middle pending.middle := by
    change PlugTurn c r (.inl (c.wire pending.last)) _ _ _
    rw [pending.arrival]
    exact .enter _ _
  rw [pending.equation]
  exact left.splice c r right _ _ pending.prefixLast head turn

theorem PlugPrefixExcursions.last_block {es : List (PlugSegment c r)} {a b : Context}
    (path : PlugPrefixExcursions c r es a b) :
    PlugExcursions c r es a b ∨Nonempty (PendingRhsBlock c r es a b) := by
  induction path with
  | single e a => exact Or.inl (.single _ _)
  | @pending e enter xs a b arrival inside =>
    exact Or.inr ⟨⟨[.inl e],e,enter,a,.inr (.inl enter)::xs,rfl,.single _ _,rfl,rfl,arrival,rfl,inside⟩⟩
  | @outside e f tail a middle b turn rest ih =>
    rcases ih with complete | pending
    · exact Or.inl (.outside turn complete)
    · obtain ⟨pending⟩ := pending
      have head : pending.pre.head?=some (.inl f) := pending.prefixHead
      obtain ⟨preTail,split⟩ := List.head?_eq_some_iff.mp head
      have prefixPath : PlugExcursions c r (.inl e::pending.pre) a pending.middle := by
        have old := pending.prefixPath
        rw [split] at old ⊢
        exact .outside turn old
      refine Or.inr ⟨⟨.inl e::pending.pre,pending.last,pending.enter,pending.middle,pending.inside,
        ?_,prefixPath,rfl,?_,pending.arrival,pending.insideHead,pending.insideLabels⟩⟩
      · simp only [pending.equation,List.cons_append]
      · rw [split,List.getLast?_cons_cons]
        simpa only [split] using pending.prefixLast
  | @through e enter exit tail a middle b inside arrival rest ih =>
    rcases ih with complete | pending
    · exact Or.inl (.through inside arrival complete)
    · obtain ⟨pending⟩ := pending
      have head : pending.pre.head?=some (.inl (.inr (.inl (.inr exit)))) := pending.prefixHead
      obtain ⟨preTail,split⟩ := List.head?_eq_some_iff.mp head
      let newPre : List (PlugSegment c r) := .inl e::(inside.edges.map Sum.inr++pending.pre)
      have prefixPath : PlugExcursions c r newPre a pending.middle := by
        have old := pending.prefixPath
        rw [split] at old
        dsimp only [newPre]
        rw [split]
        exact .through inside arrival old
      refine Or.inr ⟨⟨newPre,pending.last,pending.enter,pending.middle,pending.inside,
        ?_,prefixPath,rfl,?_,pending.arrival,pending.insideHead,pending.insideLabels⟩⟩
      · simp only [newPre,pending.equation,List.cons_append,List.append_assoc]
      · change (([(Sum.inl e : PlugSegment c r)]++inside.edges.map (Sum.inr : Endpoint r → PlugSegment c r))++pending.pre).getLast?=some (.inl pending.last)
        rw [last_append _ _ (by rw [split]; simp)]
        exact pending.prefixLast
end
end Lamping.AG



