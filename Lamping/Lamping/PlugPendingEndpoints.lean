import Lamping.Lamping.PlugPendingBlocks
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

theorem PlugExcursions.last_outside {es : List (PlugSegment c r)} {a b : Context}
    (path : PlugExcursions c r es a b) : ∃ last : Endpoint c,es.getLast?=some (.inl last) := by
  induction path with
  | single e a => exact ⟨e,rfl⟩
  | outside turn rest ih =>
    obtain ⟨last,finish⟩ := ih
    exact ⟨last,by simpa only [List.getLast?_cons_cons] using finish⟩
  | @through e enter exit tail a middle b inside arrival rest ih =>
    obtain ⟨last,finish⟩ := ih
    refine ⟨last,?_⟩
    change (([(Sum.inl e : PlugSegment c r)]++inside.edges.map (Sum.inr : Endpoint r → PlugSegment c r))++
      (.inl (.inr (.inl (.inr exit)))::tail)).getLast?=some (.inl last)
    rw [last_append _ _ (by simp)]
    exact finish

theorem PendingRhsBlock.inside_finish {es : List (PlugSegment c r)} {a b : Context}
    (pending : PendingRhsBlock c r es a b) (last : Endpoint r)
    (finish : es.getLast?=some (.inr last)) : pending.inside.getLast?=some last := by
  have nonempty : pending.inside≠[] := pending.insideLabels.nonempty
  have mapNonempty : pending.inside.map (Sum.inr : Endpoint r → PlugSegment c r)≠[] := by
    cases shape : pending.inside with
    | nil => exact False.elim (nonempty shape)
    | cons x xs => simp
  rw [pending.equation,last_append _ _ mapNonempty,List.getLast?_map] at finish
  cases result : pending.inside.getLast? with
  | none => rw [result] at finish; cases finish
  | some x =>
    rw [result] at finish
    have same : x=last := Sum.inr.inj (Option.some.inj finish)
    exact congrArg some same

/-- A right-ended actual prefix cannot be mistaken for a complete
outside-ended block stream. Its actual last RHS endpoint is retained. -/
theorem PlugPrefixExcursions.pending_at_rhs {es : List (PlugSegment c r)} {a b : Context}
    (path : PlugPrefixExcursions c r es a b) (last : Endpoint r)
    (finish : es.getLast?=some (.inr last)) :
    ∃ pending : PendingRhsBlock c r es a b,pending.inside.getLast?=some last := by
  rcases path.last_block c r with complete | pending
  · obtain ⟨oldLast,oldFinish⟩ := complete.last_outside c r
    rw [finish] at oldFinish
    cases oldFinish
  · obtain ⟨pending⟩ := pending
    exact ⟨pending,pending.inside_finish c r last finish⟩

/-- Direct physical interface for a path ending at a newly created RHS
node's incoming wire. No pending block or outside-prefix witness is assumed. -/
theorem Labelling.pending_new_node {es : List (Endpoint (plug c r))} {a b : Context}
    (labels : Labelling (plug c r) es a b) (first : Endpoint c)
    (head : es.head?=some (AG.plugLeft c r first))
    (node : R) (port : Port (r.label node).sort)
    (finish : es.getLast?=some ((plug c r).wire (.inl ⟨.inr node,port⟩))) :
    ∃ pending : PendingRhsBlock c r (es.map (plugEnd c.label r.label).invFun) a b,
      pending.inside.getLast?=some (r.wire (.inl ⟨node,port⟩)) := by
  apply (labels.prefix_excursions c r first head).pending_at_rhs c r (r.wire (.inl ⟨node,port⟩))
  rw [List.getLast?_map,finish]
  change some ((plugEnd c.label r.label).invFun ((plug c r).wire (.inl ⟨.inr node,port⟩)))=_
  rw [plugSegmentWire_inverse]
  rfl
end
end Lamping.AG

