import Lamping.Lamping.CancellationSourceExcursions
import Lamping.Lamping.TypedWireSourceContraction
import Lamping.Lamping.CancellationAncestor
namespace Lamping.AG
open Graph
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))

private theorem outside_injective : Function.Injective site.outsideEnd := by
  intro e f same
  let split := fragmentEnd (B:=B) (W:=W) site.net.label (pathPartition s V)
  change split.invFun (.inl e)=split.invFun (.inl f) at same
  have mapped := congrArg split same
  simpa only [split.right_inv,Sum.inl.injEq] using mapped

private theorem outside_turn {e : Endpoint (cutFragment site.net (pathPartition s V) site.closed)}
    {f : Endpoint site.net} {a b : Context}
    (turn : LabelledTurn site.net (site.net.wire (site.outsideEnd e)) f a b) :
    (∃ next,f=site.outsideEnd next ∧
      LabelledTurn (cutFragment site.net (pathPartition s V) site.closed)
        ((cutFragment site.net (pathPartition s V) site.closed).wire e) next a b) ∨
    ∃ frontier,(cutFragment site.net (pathPartition s V) site.closed).wire e=
      .inr (.inl (.inr frontier)) := by
  rw [site.outsideEnd_wire] at turn
  generalize (cutFragment site.net (pathPartition s V) site.closed).wire e=endpoint at turn ⊢
  rcases endpoint with ⟨node,p⟩ | ((boundary | frontier) | ⟨vertex,direction⟩)
  · change LabelledTurn site.net (.inl ⟨.inl node,p⟩) f a b at turn
    obtain ⟨q,same,rule⟩ := turn.from_node (.inl node) p rfl
    exact Or.inl ⟨.inl ⟨node,q⟩,same,.node node p q rule⟩
  · change LabelledTurn site.net (.inr (.inl boundary)) f a b at turn
    cases turn
  · exact Or.inr ⟨frontier,rfl⟩
  · change LabelledTurn site.net (.inr (.inr (.inl vertex,direction))) f a b at turn
    cases turn
    exact Or.inl ⟨.inr (.inr (vertex,!direction)),rfl,.transparent vertex direction a⟩

/-- Every supplied proper-ended old path across an actual cancellation has
an actual reduced path with the SAME entry/output contexts and retained
endpoints. The finite literal residual is constructed from actual typed
crossings; target existence is a conclusion, never a premise. -/
theorem PathSite.cancellation_source_contraction (cancel : IsCancellation s)
    {old : List (Endpoint site.net)} {a b : Context}
    (labels : Labelling site.net old a b) (typed : ∃ k,accessKind site.net old=some k)
    (first last : Endpoint (cutFragment site.net (pathPartition s V) site.closed))
    (head : old.head?=some (site.outsideEnd first))
    (finish : old.getLast?=some (site.outsideEnd last)) :
    ∃ es,Labelling site.reduce es a b ∧CancellationResidual site es old ∧
      es.head?=some (AG.plugLeft _ s.right.net first) ∧
      es.getLast?=some (AG.plugLeft _ s.right.net last) := by
  let c := cutFragment site.net (pathPartition s V) site.closed
  let r := s.right.net
  cases cancel
  all_goals
    obtain ⟨raw,path,residual,start,endEq⟩ := Labelling.contract_typed_wire_source c r site.net
      site.outsideEnd (outside_injective site) site.outsideEnd_wire (outside_turn site)
      (fun frontier {es} {input} {output} given actual ends => by
        have split := site.cancellation_typed_exit (by constructor) frontier given actual ends
        cases frontier <;> exact split)
      labels typed first last head finish
    refine ⟨raw.map (plugEnd c.label r.label),(path.labelling c r).actual c r,?_,?_,?_⟩
    · change WireBlockResidual c r site.net site.outsideEnd
        ((raw.map (plugEnd c.label r.label)).map (plugEnd c.label r.label).invFun) old
      simpa only [List.map_map,Function.comp_def,(plugEnd c.label r.label).left_inv,List.map_id_fun'] using residual
    · rw [List.head?_map,start]
      rfl
    · rw [List.getLast?_map,endEq]
      rfl
end
end Lamping.AG
