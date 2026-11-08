import Lamping.Lamping.BetaResidualSplicing
namespace Lamping.AG
open Graph
section
variable {K R B F W U : Type} [FiniteNames K] [FiniteNames R] [FiniteNames B]
  [FiniteNames F] [FiniteNames W] [FiniteNames U]
variable {c : Net signature K (B⊕F) W} {r : Net signature R F U}
private theorem plug_append_at_last {pre tail : List (PlugSegment c r)} {last : PlugSegment c r}
    {a seam b : Context} (before : PlugLabelling c r pre a seam)
    (after : PlugLabelling c r (last::tail) seam b) (finish : pre.getLast?=some last) :
    PlugLabelling c r (pre++tail) a b := by
  induction before with
  | single e a =>
    have same : e=last := Option.some.inj finish
    subst last
    exact after
  | cons turn rest ih => exact .cons turn (ih after (by simpa only [List.getLast?_cons_cons] using finish))
theorem PlugLabelling.splice_last {pre tail : List (PlugSegment c r)} {last : PlugSegment c r}
    {a seam b : Context} (before : PlugLabelling c r pre a seam)
    (after : PlugLabelling c r tail seam b)
    (finish : pre.getLast?=some last) (head : tail.head?=some last) :
    PlugLabelling c r (pre.dropLast++tail) a b := by
  obtain ⟨post,tailSplit⟩ := List.head?_eq_some_iff.mp head
  obtain ⟨stem,preSplit⟩ := List.getLast?_eq_some_iff.mp finish
  rw [tailSplit] at after
  have joined := plug_append_at_last before after finish
  simpa only [preSplit,tailSplit,List.dropLast_concat,List.append_assoc,List.singleton_append] using joined
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.beta i) V) site.closed
private theorem raw_head {edge : BetaEdge site.net} {raw old} (relation : BetaPathResidual site edge raw old) :
    ∃ first : Endpoint cut,raw.head?=some (.inl first) := by
  cases relation <;> exact ⟨_,rfl⟩
private theorem reflect_head {edge : BetaEdge site.net} {raw old} (relation : BetaPathResidual site edge raw old)
    (first : Endpoint cut) (head : old.head?=some (site.outsideEnd first)) : raw.head?=some (.inl first) := by
  obtain ⟨actual,rawHead⟩ := raw_head site relation
  have oldHead := relation.head site rawHead
  have same := site.outsideEnd_injective (Option.some.inj (oldHead.symm.trans head))
  simpa only [same] using rawHead

/-- Combine two actual contracted pieces across the beta context/body
reconnection. Actual RHS seam turns supply the new labels and a finite
residual splice supplies the literal old principal, without a target oracle. -/
theorem BetaPathResidual.context_splice {edge : BetaEdge site.net} (geometry : SiteBetaGeometry site edge)
    {leftRaw rightRaw leftOld rightOld} {a seam b : Context}
    (left : BetaPathResidual site edge leftRaw leftOld) (right : BetaPathResidual site edge rightRaw rightOld)
    (leftLabels : PlugLabelling cut (Schema.beta i).right.net leftRaw a seam)
    (rightLabels : PlugLabelling cut (Schema.beta i).right.net rightRaw seam b)
    (finish : leftOld.getLast?=some (site.net.wire (.inl ⟨edge.app,edge.appCtx⟩)))
    (head : rightOld.head?=some (.inl ⟨edge.lam,edge.lamBody⟩)) :
    ∃ raw,BetaPathResidual site edge raw (leftOld++edge.principal++rightOld) ∧
      PlugLabelling cut (Schema.beta i).right.net raw a b := by
  let endPoint : Endpoint cut := (cut).wire (.inr (.inl (.inr (.inl false))))
  have outsideEnd : site.outsideEnd endPoint=site.net.wire (.inl ⟨edge.app,edge.appCtx⟩) := by
    dsimp only [endPoint]
    rw [←site.outsideEnd_wire,geometry.appCtx]; rfl
  have leftFinish := left.reflect_finish site endPoint (finish.trans (congrArg some outsideEnd.symm))
  have rightStart : rightRaw.head?=some (.inl (.inr (.inl (.inr (.inr true))))) :=
    reflect_head site right _ (head.trans (congrArg some (by rw [geometry.body]; rfl)))
  obtain ⟨tail,rightSplit⟩ := List.head?_eq_some_iff.mp rightStart
  rw [rightSplit] at right rightLabels
  have extension := BetaPathResidual.context (site:=site) (edge:=edge)
    (e:=endPoint) (by exact Pairing.involutive _ _) right
  have extensionLabels : PlugLabelling cut (Schema.beta i).right.net
      (.inl endPoint::.inr (.inr (.inl (.inl false)))::.inl (.inr (.inl (.inr (.inr true))))::tail) seam b := by
    apply PlugLabelling.cons
    · change PlugTurn cut (Schema.beta i).right.net (.inl ((cut).wire endPoint)) _ seam seam
      rw [Pairing.involutive]; exact .enter (.inl false : Bool⊕Bool) seam
    · exact .cons (.leave (.inr true : Bool⊕Bool) seam) rightLabels
  have result := left.splice_last site extension endPoint leftFinish rfl
  have actual := leftLabels.splice_last extensionLabels leftFinish rfl
  have oldFinish := left.finish site leftFinish
  obtain ⟨stem,oldSplit⟩ := List.getLast?_eq_some_iff.mp oldFinish
  refine ⟨_,?_,actual⟩
  simpa only [oldSplit,List.dropLast_concat,List.append_assoc,List.singleton_append] using result

/-- The matching binding/argument reconnection contracts the complete
physical reverse principal, retaining both ordered pieces and assignments. -/
theorem BetaPathResidual.binding_splice {edge : BetaEdge site.net} (geometry : SiteBetaGeometry site edge)
    {leftRaw rightRaw leftOld rightOld} {a seam b : Context}
    (left : BetaPathResidual site edge leftRaw leftOld) (right : BetaPathResidual site edge rightRaw rightOld)
    (leftLabels : PlugLabelling cut (Schema.beta i).right.net leftRaw a seam)
    (rightLabels : PlugLabelling cut (Schema.beta i).right.net rightRaw seam b)
    (finish : leftOld.getLast?=some (site.net.wire (.inl ⟨edge.lam,edge.lamBind⟩)))
    (head : rightOld.head?=some edge.argEnd) :
    ∃ raw,BetaPathResidual site edge raw (leftOld++edge.reverseRoute++rightOld) ∧
      PlugLabelling cut (Schema.beta i).right.net raw a b := by
  let endPoint : Endpoint cut := (cut).wire (.inr (.inl (.inr (.inr false))))
  have outsideEnd : site.outsideEnd endPoint=site.net.wire (.inl ⟨edge.lam,edge.lamBind⟩) := by
    dsimp only [endPoint]
    rw [←site.outsideEnd_wire,geometry.binding]; rfl
  have leftFinish := left.reflect_finish site endPoint (finish.trans (congrArg some outsideEnd.symm))
  have rightStart : rightRaw.head?=some (.inl (.inr (.inl (.inr (.inl true))))) :=
    reflect_head site right _ (head.trans (congrArg some (by rw [geometry.argument]; rfl)))
  obtain ⟨tail,rightSplit⟩ := List.head?_eq_some_iff.mp rightStart
  rw [rightSplit] at right rightLabels
  have extension := BetaPathResidual.binding (site:=site) (edge:=edge)
    (e:=endPoint) (by exact Pairing.involutive _ _) right
  have extensionLabels : PlugLabelling cut (Schema.beta i).right.net
      (.inl endPoint::.inr (.inr (.inl (.inr false)))::.inl (.inr (.inl (.inr (.inl true))))::tail) seam b := by
    apply PlugLabelling.cons
    · change PlugTurn cut (Schema.beta i).right.net (.inl ((cut).wire endPoint)) _ seam seam
      rw [Pairing.involutive]; exact .enter (.inr false : Bool⊕Bool) seam
    · exact .cons (.leave (.inl true : Bool⊕Bool) seam) rightLabels
  have result := left.splice_last site extension endPoint leftFinish rfl
  have actual := leftLabels.splice_last extensionLabels leftFinish rfl
  have oldFinish := left.finish site leftFinish
  obtain ⟨stem,oldSplit⟩ := List.getLast?_eq_some_iff.mp oldFinish
  refine ⟨_,?_,actual⟩
  simpa only [oldSplit,List.dropLast_concat,List.append_assoc,List.singleton_append] using result

/-- Exact raw context reconnection, for physical word accounting. -/
theorem BetaPathResidual.context_splice_canonical {edge : BetaEdge site.net} (geometry : SiteBetaGeometry site edge)
    {leftRaw rightRaw leftOld rightOld} {a seam b : Context}
    (left : BetaPathResidual site edge leftRaw leftOld) (right : BetaPathResidual site edge rightRaw rightOld)
    (leftLabels : PlugLabelling cut (Schema.beta i).right.net leftRaw a seam)
    (rightLabels : PlugLabelling cut (Schema.beta i).right.net rightRaw seam b)
    (finish : leftOld.getLast?=some (site.net.wire (.inl ⟨edge.app,edge.appCtx⟩)))
    (head : rightOld.head?=some (.inl ⟨edge.lam,edge.lamBody⟩)) :
    BetaPathResidual site edge (leftRaw++(.inr (.inr (.inl (.inl false))))::rightRaw)
      (leftOld++edge.principal++rightOld) ∧
      PlugLabelling cut (Schema.beta i).right.net (leftRaw++(.inr (.inr (.inl (.inl false))))::rightRaw) a b := by
  let endPoint : Endpoint cut := (cut).wire (.inr (.inl (.inr (.inl false))))
  have outsideEnd : site.outsideEnd endPoint=site.net.wire (.inl ⟨edge.app,edge.appCtx⟩) := by
    dsimp only [endPoint]
    rw [←site.outsideEnd_wire,geometry.appCtx]; rfl
  have leftFinish := left.reflect_finish site endPoint (finish.trans (congrArg some outsideEnd.symm))
  have rightStart : rightRaw.head?=some (.inl (.inr (.inl (.inr (.inr true))))) :=
    reflect_head site right _ (head.trans (congrArg some (by rw [geometry.body]; rfl)))
  obtain ⟨tail,rightSplit⟩ := List.head?_eq_some_iff.mp rightStart
  rw [rightSplit] at right rightLabels
  have extension := BetaPathResidual.context (site:=site) (edge:=edge)
    (e:=endPoint) (by exact Pairing.involutive _ _) right
  have extensionLabels : PlugLabelling cut (Schema.beta i).right.net
      (.inl endPoint::.inr (.inr (.inl (.inl false)))::.inl (.inr (.inl (.inr (.inr true))))::tail) seam b := by
    apply PlugLabelling.cons
    · change PlugTurn cut (Schema.beta i).right.net (.inl ((cut).wire endPoint)) _ seam seam
      rw [Pairing.involutive]; exact .enter (.inl false : Bool⊕Bool) seam
    · exact .cons (.leave (.inr true : Bool⊕Bool) seam) rightLabels
  have result := left.splice_last site extension endPoint leftFinish rfl
  have actual := leftLabels.splice_last extensionLabels leftFinish rfl
  have oldFinish := left.finish site leftFinish
  obtain ⟨stem,oldSplit⟩ := List.getLast?_eq_some_iff.mp oldFinish
  obtain ⟨rawStem,rawSplit⟩ := List.getLast?_eq_some_iff.mp leftFinish
  constructor
  · simpa only [oldSplit,rawSplit,List.dropLast_concat,List.append_assoc,List.singleton_append,rightSplit] using result
  · simpa only [rawSplit,List.dropLast_concat,List.append_assoc,List.singleton_append,rightSplit] using actual


/-- Exact raw binding reconnection, for physical word accounting. -/
theorem BetaPathResidual.binding_splice_canonical {edge : BetaEdge site.net} (geometry : SiteBetaGeometry site edge)
    {leftRaw rightRaw leftOld rightOld} {a seam b : Context}
    (left : BetaPathResidual site edge leftRaw leftOld) (right : BetaPathResidual site edge rightRaw rightOld)
    (leftLabels : PlugLabelling cut (Schema.beta i).right.net leftRaw a seam)
    (rightLabels : PlugLabelling cut (Schema.beta i).right.net rightRaw seam b)
    (finish : leftOld.getLast?=some (site.net.wire (.inl ⟨edge.lam,edge.lamBind⟩)))
    (head : rightOld.head?=some edge.argEnd) :
    BetaPathResidual site edge (leftRaw++(.inr (.inr (.inl (.inr false))))::rightRaw)
      (leftOld++edge.reverseRoute++rightOld) ∧
      PlugLabelling cut (Schema.beta i).right.net (leftRaw++(.inr (.inr (.inl (.inr false))))::rightRaw) a b := by
  let endPoint : Endpoint cut := (cut).wire (.inr (.inl (.inr (.inr false))))
  have outsideEnd : site.outsideEnd endPoint=site.net.wire (.inl ⟨edge.lam,edge.lamBind⟩) := by
    dsimp only [endPoint]
    rw [←site.outsideEnd_wire,geometry.binding]; rfl
  have leftFinish := left.reflect_finish site endPoint (finish.trans (congrArg some outsideEnd.symm))
  have rightStart : rightRaw.head?=some (.inl (.inr (.inl (.inr (.inl true))))) :=
    reflect_head site right _ (head.trans (congrArg some (by rw [geometry.argument]; rfl)))
  obtain ⟨tail,rightSplit⟩ := List.head?_eq_some_iff.mp rightStart
  rw [rightSplit] at right rightLabels
  have extension := BetaPathResidual.binding (site:=site) (edge:=edge)
    (e:=endPoint) (by exact Pairing.involutive _ _) right
  have extensionLabels : PlugLabelling cut (Schema.beta i).right.net
      (.inl endPoint::.inr (.inr (.inl (.inr false)))::.inl (.inr (.inl (.inr (.inl true))))::tail) seam b := by
    apply PlugLabelling.cons
    · change PlugTurn cut (Schema.beta i).right.net (.inl ((cut).wire endPoint)) _ seam seam
      rw [Pairing.involutive]; exact .enter (.inr false : Bool⊕Bool) seam
    · exact .cons (.leave (.inl true : Bool⊕Bool) seam) rightLabels
  have result := left.splice_last site extension endPoint leftFinish rfl
  have actual := leftLabels.splice_last extensionLabels leftFinish rfl
  have oldFinish := left.finish site leftFinish
  obtain ⟨stem,oldSplit⟩ := List.getLast?_eq_some_iff.mp oldFinish
  obtain ⟨rawStem,rawSplit⟩ := List.getLast?_eq_some_iff.mp leftFinish
  constructor
  · simpa only [oldSplit,rawSplit,List.dropLast_concat,List.append_assoc,List.singleton_append,rightSplit] using result
  · simpa only [rawSplit,List.dropLast_concat,List.append_assoc,List.singleton_append,rightSplit] using actual
end
end Lamping.AG