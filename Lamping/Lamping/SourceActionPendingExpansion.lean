import Lamping.Lamping.RootSourcePrefixExpansion
import Lamping.Lamping.ActionPendingWords
namespace Lamping.AG
open Graph Lambda
section
variable {s : Schema} {K B W V : Type}
variable [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed

private theorem word_append {N D U : Type} [FiniteNames N] [FiniteNames D] [FiniteNames U]
    (g : Net signature N D U) (xs ys : List (Endpoint g)) (positive : xs≠[]) :
    accessWord g (xs++ys)=accessWord g xs++accessTokens g ys := by
  cases xs with
  | nil => exact False.elim (positive rfl)
  | cons e xs => exact List.flatMap_append

/-- Expand a real source prefix and append a genuinely labelled truncated
RHS block. The prefix may end at a control auxiliary: no typed-prefix premise
or extension is invented. The resulting physical path and word are constructed. -/
theorem PathSite.source_pending_expansion (action : IsAction s)
    {root : B} {t : Term} {boundary : B → Bool}
    (matching : Matches site.net root t) (inputs : RootInputs site.net root)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    {old : List (Endpoint site.net)} {input middle output : Context}
    (labels : Labelling site.net old input middle)
    (rooted : old.head?=some (.inr (.inl root))) (entry : s.Frontier)
    (finish : old.getLast?=some (site.net.wire (site.outsideEnd (.inr (.inl (.inr entry))))))
    (inside : List (Endpoint s.right.net)) (insideLabels : Labelling s.right.net inside middle output)
    (insideHead : inside.head?=some (.inr (.inl entry))) :
    ∃ es : List (Endpoint site.reduce),Labelling site.reduce es input output ∧
      es.head?=some (.inr (.inl root)) ∧
      es.getLast?=inside.getLast?.map (AG.plugRight cut s.right.net) ∧
      accessWord site.reduce es=accessWord site.net old++accessTokens s.right.net inside := by
  let first : Endpoint cut := .inr (.inl (.inl root))
  let last : Endpoint cut := (cut).wire (.inr (.inl (.inr entry)))
  have outsideLast : old.getLast?=some (site.outsideEnd last) := by
    simpa only [last,site.outsideEnd_wire] using finish
  obtain ⟨principal⟩ := site.actionPrincipal_exists
  obtain ⟨raw,path,residual,rawHead,rawLast⟩ := site.expand_labelled_source_outside action principal matching inputs
    flow positive labels first last rooted outsideLast [] input (.single _ _) rfl
  let allRaw := raw++inside.map Sum.inr
  let pending : PendingRhsBlock cut s.right.net allRaw input output := {
    pre := raw
    last := last
    enter := entry
    middle := middle
    inside := inside
    equation := rfl
    prefixPath := path
    prefixHead := by
      cases raw with
      | nil => cases rawHead
      | cons e raw => rfl
    prefixLast := rawLast
    arrival := (cut).wire.involutive _
    insideHead := insideHead
    insideLabels := insideLabels }
  let es : List (Endpoint (plug cut s.right.net)) := allRaw.map (plugEnd (cut).label s.right.net.label)
  have rawPositive : raw≠[] := by intro empty; rw [empty] at rawHead; cases rawHead
  have mappedPositive : raw.map (plugEnd (cut).label s.right.net.label)≠[] := by
    cases raw with
    | nil => exact False.elim (rawPositive rfl)
    | cons e raw => simp
  have rightMap : (inside.map Sum.inr).map (plugEnd (cut).label s.right.net.label)=
      inside.map (AG.plugRight cut s.right.net) := by rw [List.map_map]; rfl
  have physicalEq : es=(raw.map (plugEnd (cut).label s.right.net.label) : List (Endpoint (plug cut s.right.net)))++inside.map (AG.plugRight cut s.right.net) := by
    change (allRaw.map _)=_
    simp only [allRaw,List.map_append,rightMap]
  have word := residual.word site path
  have rightTokens : accessTokens site.reduce (inside.map (AG.plugRight cut s.right.net))=accessTokens s.right.net inside :=
    accessTokens_plugRight cut s.right.net inside
  refine ⟨es,(pending.labelling cut s.right.net).actual cut s.right.net,?_,?_,?_⟩
  · rw [physicalEq,List.head?_append,List.head?_map,rawHead]
    rfl
  · rw [physicalEq,List.getLast?_append,List.getLast?_map]
    cases lastInside : inside.getLast? with
    | none => exact False.elim (insideLabels.nonempty (List.getLast?_eq_none_iff.mp lastInside))
    | some e => simp only [Option.map_some,Option.some_or]
  · rw [physicalEq,word_append site.reduce _ _ mappedPositive,word,rightTokens]
end
end Lamping.AG



