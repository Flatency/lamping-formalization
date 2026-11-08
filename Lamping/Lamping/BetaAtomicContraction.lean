import Lamping.Lamping.BetaAtomicExterior
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.beta i) V) site.closed
private theorem exterior_residual (edge : BetaEdge site.net)
    {es : List (Endpoint cut)} {a b : Context} (labels : Labelling cut es a b) :
    BetaPathResidual site edge (es.map (fun e => Sum.inl e)) (es.map site.outsideEnd) := by
  induction labels with
  | single e a => exact .single e
  | cons turn rest ih => exact .outside ih
/-- Construct an actual RHS path from a supplied ordinary forward atomic
piece. Its empty word rules out removed proper turns, so the target and its
labelling are derived through the cut/plug maps, not given as a shape oracle. -/
theorem PathSite.beta_atomic_contraction (edge : BetaEdge site.net)
    {old : List (Endpoint site.net)} {a b : Context}
    (labels : Labelling site.net old a b) (forward : Forward site.net old)
    (emptyWord : accessWord site.net old=[])
    (first : Endpoint cut) (head : old.head?=some (site.outsideEnd first)) :
    ∃ target : List (Endpoint site.reduce),
      BetaPathResidual site edge (target.map (plugEnd _ _).invFun) old ∧
      Labelling site.reduce target a b ∧target.head?=some (AG.plugLeft _ _ first) ∧
      ∀ last,old.getLast?=some (site.outsideEnd last) →target.getLast?=some (AG.plugLeft _ _ last) := by
  obtain ⟨exterior,literal,cutLabels⟩ := site.beta_empty_word_exterior labels forward emptyWord first head
  let target := exterior.map (AG.plugLeft cut (Schema.beta i).right.net)
  have rawEq : target.map (plugEnd _ _).invFun=exterior.map (fun e => Sum.inl e) := by
    simp only [target,List.map_map]
    apply List.map_congr_left
    intro e _
    exact (plugEnd (cut).label (Schema.beta i).right.net.label).left_inv (.inl e)
  have targetLabels : Labelling site.reduce target a b := cutLabels.plugLeft cut (Schema.beta i).right.net
  have relation : BetaPathResidual site edge (target.map (plugEnd _ _).invFun) old := by
    rw [rawEq,literal]
    exact exterior_residual site edge cutLabels
  have exteriorHead : exterior.head?=some first := by
    have same := congrArg List.head? literal
    rw [head,List.head?_map] at same
    cases exterior with
    | nil => cases same
    | cons x xs =>
      exact congrArg some ((site.outsideEnd_injective (Option.some.inj same)).symm)
  refine ⟨target,relation,targetLabels,by simp only [target,List.head?_map,exteriorHead,Option.map_some],?_⟩
  intro last finish
  rw [literal,List.getLast?_map] at finish
  cases lastEq : exterior.getLast? with
  | none => rw [lastEq] at finish; cases finish
  | some actual =>
    rw [lastEq] at finish
    have same := site.outsideEnd_injective (Option.some.inj finish)
    simp only [target,List.getLast?_map,lastEq,Option.map_some,same]

/-- The selected original source fragment supplies the actual Forward and
empty-token facts; only its supplied assignment and actual outside departure
are consumed. No source or target whole-term correctness is an input. -/
theorem SourceEdgeFragment.beta_atomic_contraction
    {root : B} {original : LTerm} {sourceEdge : SourceEdge} {p : Path}
    (fragment : SourceEdgeFragment original site.net root sourceEdge p) (edge : BetaEdge site.net)
    (first : Endpoint cut) (outside : fragment.fromEndpoint=site.outsideEnd first)
    {a b : Context} (labels : Labelling site.net fragment.segments a b) :
    ∃ target : List (Endpoint site.reduce),
      BetaPathResidual site edge (target.map (plugEnd _ _).invFun) fragment.segments ∧
      Labelling site.reduce target a b ∧target.head?=some (AG.plugLeft _ _ first) ∧
      ∀ last,fragment.segments.getLast?=some (site.outsideEnd last) →target.getLast?=some (AG.plugLeft _ _ last) := by
  exact site.beta_atomic_contraction edge labels fragment.forward fragment.emptyWord first
    (fragment.start.trans (congrArg some outside))
end
end Lamping.AG