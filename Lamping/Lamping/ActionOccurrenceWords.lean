import Lamping.Lamping.ActionWholeWords
import Lamping.Lamping.ActionOccurrenceLabelling
namespace Lamping.AG
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable (g : Net signature N B W)

/-- Count the shared departure once, including the singleton-physicalPrefix case. -/
theorem accessWord_overlap (pre : List (Endpoint g)) (e : Endpoint g) (tail : List (Endpoint g)) :
    accessWord g (pre++e::tail)=accessWord g (pre++[e])++accessWord g (e::tail) := by
  cases pre with
  | nil => rfl
  | cons x pre => simp only [List.cons_append,accessWord,List.flatMap_append,List.flatMap_cons,
      List.flatMap_nil,List.append_nil,List.append_assoc]
end
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed
local notation "rhs" => s.right.net

/-- The suffix after a specified retained departure has exactly the source
suffix word. The actual whole and physicalPrefix shapes certify the two canonical
word equations; a bare residual relation would not suffice. -/
theorem ActionResidualOccurrence.suffix_word
    {principal : SiteActionPrincipal site} {raw old node p ordinal}
    (cutAt : ActionResidualOccurrence site principal raw old node p ordinal)
    (relation : ActionCanonicalBlocks site principal raw old)
    {a b : Context} (shape : PlugExcursions cut rhs raw a b)
    (first : Endpoint cut) (rooted : raw.head?=some (.inl first)) :
    accessWord site.reduce ((.inl ⟨.inl node,p⟩)::cutAt.after.map (plugEnd (cut).label (rhs).label))=
      accessWord site.net ((.inl ⟨.inl node,p⟩)::cutAt.oldAfter) := by
  have labels := (shape.labelling cut rhs).actual cut rhs
  have fullSplit : raw.map (plugEnd (cut).label (rhs).label)=
      cutAt.before.map (plugEnd (cut).label (rhs).label)++
      (.inl ⟨.inl node,p⟩)::cutAt.after.map (plugEnd (cut).label (rhs).label) := by
    have mapped := congrArg (List.map (plugEnd (cut).label (rhs).label)) cutAt.raw_eq
    simpa only [List.map_append,List.map_cons] using mapped
  rw [fullSplit] at labels
  obtain ⟨middle,prefixLabels,_suffixLabels⟩ := labels.split_segment
  let physicalPrefix : List (Endpoint site.reduce) :=
    cutAt.before.map (plugEnd (cut).label (rhs).label)++[.inl ⟨.inl node,p⟩]
  have represented : physicalPrefix=
      (cutAt.before++[(Sum.inl (.inl ⟨node,p⟩ : Endpoint cut) : PlugSegment cut rhs)]).map
        (plugEnd (cut).label (rhs).label) := by
    simp only [physicalPrefix,List.map_append,List.map_cons,List.map_nil]
    rfl
  have prefixHead : physicalPrefix.head?=some (AG.plugLeft cut rhs first) := by
    rw [represented,List.head?_map,cutAt.prefix_head site,rooted]
    rfl
  have prefixLast : physicalPrefix.getLast?=some (AG.plugLeft cut rhs (.inl ⟨node,p⟩)) := by
    simp only [physicalPrefix,List.getLast?_append,List.getLast?_cons,List.getLast?_nil,Option.some_or]
    rfl
  have prefixShape := prefixLabels.local_excursions cut rhs first (.inl ⟨node,p⟩) prefixHead prefixLast
  have rawPrefix : physicalPrefix.map (plugEnd (cut).label (rhs).label).invFun=
      cutAt.before++[.inl (.inl ⟨node,p⟩ : Endpoint cut)] := by
    rw [represented]
    simp only [List.map_map,Function.comp_def,(plugEnd (cut).label (rhs).label).left_inv]
    simp
  change PlugExcursions cut rhs (physicalPrefix.map (plugEnd (cut).label (rhs).label).invFun) a middle at prefixShape
  rw [rawPrefix] at prefixShape
  have prefixWords := cutAt.prefixResidual.word site prefixShape
  have prefixEq : accessWord site.reduce physicalPrefix=
      accessWord site.net (cutAt.oldBefore++[.inl ⟨.inl node,p⟩]) := by
    rw [represented]
    exact prefixWords
  have wholeWords := (relation.word site shape).trans (congrArg (accessWord site.net) cutAt.old_eq)
  rw [fullSplit,
    accessWord_overlap site.reduce (cutAt.before.map (plugEnd (cut).label (rhs).label))
      (.inl ⟨.inl node,p⟩) (cutAt.after.map (plugEnd (cut).label (rhs).label)),
    accessWord_overlap site.net cutAt.oldBefore (.inl ⟨.inl node,p⟩) cutAt.oldAfter] at wholeWords
  change accessWord site.reduce physicalPrefix++_=_ at wholeWords
  rw [prefixEq] at wholeWords
  exact List.append_cancel_left wholeWords
end
end Lamping.AG
