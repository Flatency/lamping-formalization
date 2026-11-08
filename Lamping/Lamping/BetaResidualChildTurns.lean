import Lamping.Lamping.BetaSourceRouteWords
namespace Lamping.AG
open Graph Lambda
private theorem child_rule {kind : Kind} {ctx departure : Port kind} {step : Step}
    (roles : SyntaxChildPorts kind ctx departure step) (level : Nat) (a : Context) :
    Traversal level kind ctx departure a a := by
  cases roles
  · exact .direct (.appFun a)
  · exact .direct (.appArg a)
  · exact .direct (.lamBody a)
private def departureToken : (kind : Kind) → Port kind → Path
  | .op .app,.inl () => [.fn]
  | .op .app,.inr true => [.arg]
  | .op .lam,.inr true => [.body]
  | _,_ => []
private theorem child_token {actual : Label signature} {ctx departure : Port actual.sort} {step : Step}
    (roles : SyntaxChildPorts actual.sort ctx departure step) : departureToken actual.sort departure=[step] := by
  cases actual with
  | mk kind level => cases roles <;> rfl
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.beta i) V) site.closed
private theorem raw_head {edge : BetaEdge site.net} {raw old} (relation : BetaPathResidual site edge raw old) :
    ∃ first : Endpoint cut,raw.head?=some (.inl first) := by cases relation <;> exact ⟨_,rfl⟩
private theorem reflect_head {edge : BetaEdge site.net} {raw old} (relation : BetaPathResidual site edge raw old)
    (first : Endpoint cut) (head : old.head?=some (site.outsideEnd first)) : raw.head?=some (.inl first) := by
  obtain ⟨actual,rawHead⟩ := raw_head site relation
  have same := site.outsideEnd_injective (Option.some.inj ((relation.head site rawHead).symm.trans head))
  simpa only [same] using rawHead
/-- An actual retained syntax-child turn joins two contracted pieces.
The complete-development geometry supplies this retained node; here its
real local primitive and departure token construct the new label and word. -/
theorem BetaPathResidual.kept_child_splice {edge : BetaEdge site.net}
    {leftRaw rightRaw leftOld rightOld} {a seam b : Context}
    (left : BetaPathResidual site edge leftRaw leftOld) (right : BetaPathResidual site edge rightRaw rightOld)
    (leftLabels : PlugLabelling cut (Schema.beta i).right.net leftRaw a seam)
    (rightLabels : PlugLabelling cut (Schema.beta i).right.net rightRaw seam b)
    (node : K) (ctx departure : Port (kept node).sort) (step : Step)
    (roles : SyntaxChildPorts (kept node).sort ctx departure step)
    (finish : leftOld.getLast?=some (site.net.wire (.inl ⟨.inl node,ctx⟩)))
    (head : rightOld.head?=some (.inl ⟨.inl node,departure⟩))
    (leftWord : accessWord site.reduce (leftRaw.map (plugEnd _ _))=[])
    (word : Path) (rightWord : accessWord site.reduce (rightRaw.map (plugEnd _ _))=word) :
    BetaPathResidual site edge (leftRaw++rightRaw) (leftOld++rightOld) ∧
      PlugLabelling cut (Schema.beta i).right.net (leftRaw++rightRaw) a b ∧
      accessWord site.reduce ((leftRaw++rightRaw).map (plugEnd _ _))=step::word := by
  let endPoint : Endpoint cut := (cut).wire (.inl ⟨node,ctx⟩)
  have outsideEnd : site.outsideEnd endPoint=site.net.wire (.inl ⟨.inl node,ctx⟩) :=
    (site.outsideEnd_wire (.inl ⟨node,ctx⟩)).symm
  have leftFinish := left.reflect_finish site endPoint (finish.trans (congrArg some outsideEnd.symm))
  have rightStart : rightRaw.head?=some (.inl (.inl ⟨node,departure⟩)) := reflect_head site right _ head
  obtain ⟨tail,rightSplit⟩ := List.head?_eq_some_iff.mp rightStart
  rw [rightSplit] at right rightLabels
  have extension := BetaPathResidual.outside (site:=site) (e:=endPoint) right
  have extensionLabels : PlugLabelling cut (Schema.beta i).right.net
      (.inl endPoint::.inl (.inl ⟨node,departure⟩)::tail) seam b := by
    exact .cons (.left (by
      change LabelledTurn cut ((cut).wire endPoint) (.inl ⟨node,departure⟩) seam seam
      rw [Pairing.involutive]
      exact LabelledTurn.node (g:=cut) node ctx departure (child_rule roles (kept node).index seam))) rightLabels
  have result := left.splice_last site extension endPoint leftFinish rfl
  have actual := leftLabels.splice_last extensionLabels leftFinish rfl
  obtain ⟨oldStem,oldSplit⟩ := List.getLast?_eq_some_iff.mp (left.finish site leftFinish)
  obtain ⟨rawStem,rawSplit⟩ := List.getLast?_eq_some_iff.mp leftFinish
  refine ⟨?_,?_,?_⟩
  · simpa only [oldSplit,rawSplit,List.dropLast_concat,List.append_assoc,List.singleton_append,rightSplit] using result
  · simpa only [rawSplit,List.dropLast_concat,List.append_assoc,List.singleton_append,rightSplit] using actual
  · have mappedNonempty : leftRaw.map (plugEnd _ _)≠[] := by
      intro empty
      have nil := List.map_eq_nil_iff.mp empty
      rw [nil] at leftLabels
      cases leftLabels
    have token : arrivalWord site.reduce ((plugEnd _ _) (.inl (.inl ⟨node,departure⟩)))=[step] := child_token roles
    rw [List.map_append,accessWord_append site.reduce _ _ mappedNonempty,leftWord]
    rw [rightSplit,List.map_cons,List.flatMap_cons,token]
    have tailWord := rightWord
    rw [rightSplit] at tailWord
    simpa only [List.nil_append,List.singleton_append] using congrArg (List.cons step) tailWord
end
end Lamping.AG