import Lamping.Lamping.ActionPendingCanonicalTrim
import Lamping.Lamping.ActionKeptParentCuts
import Lamping.Lamping.ActionCopiedBindingFragmentCuts
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Label signature} {f : Op} {i j : Nat} {lt : i<j}
variable (site : PathSite (.fanAction f i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.fanAction f i j lt) V) site.closed
private abbrev fanBindingRight (f : Op) (i j : Nat) (lt : i<j) := (Schema.fanAction f i j lt).right.net
local notation "rhs" => fanBindingRight f i j lt
/-- The actual copied-auxiliary classifier supplies both removed segments,
the reader rule and the SAME prefix assignment on the supplied principal. -/
theorem PendingRhsBlock.fan_aux_canonical_trim (principal : SiteActionPrincipal site)
    {raw : List (PlugSegment cut rhs)} {a b : Context}
    (pending : PendingRhsBlock cut rhs raw a b)
    (first : Endpoint cut) (head : raw.head?=some (.inl first)) (branch : Bool) (q : Aux f)
    (finish : pending.inside.getLast?=some ((rhs).wire (.inl ⟨.inl branch,.inr q⟩))) :
    ∃ old,ActionCanonicalBlocks site principal pending.pre old ∧
      Labelling site.net old a pending.middle ∧old.head?=some (site.outsideEnd first) ∧
      old.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inr q⟩)) ∧
      raw=pending.pre++[.inr (.inr (.inl (.inr q))),.inr (.inl ⟨.inr q,.inr branch⟩)] ∧
      Traversal i (.op .fan) (.inl ()) (.inr branch) pending.middle b ∧
      accessWord site.reduce (raw.map (plugEnd _ _))=accessWord site.net old := by
  obtain ⟨entry,shape,rule⟩ := fanRight_copied_aux_prefix f i j branch q pending.enter pending.inside
    pending.middle b pending.insideLabels pending.insideHead finish
  obtain ⟨old,relation,labels,start,last⟩ := pending.prefixPath.action_canonical_lift site
    (.fan f i j lt) principal first pending.last (pending.prefixHead.trans head) pending.prefixLast
  have ending : site.outsideEnd pending.last=site.net.wire (.inl ⟨.inr (.inr ()),.inr q⟩) := by
    have wired := site.outsideEnd_wire pending.last
    rw [pending.arrival,entry] at wired
    have same := congrArg site.net.wire.mate wired
    simpa only [Pairing.involutive] using same
  have whole := pending.equation
  rw [shape] at whole
  have words := relation.word site pending.prefixPath
  have physical : accessWord site.reduce (raw.map (plugEnd _ _))=
      accessWord site.reduce (pending.pre.map (plugEnd _ _)) := by
    have nonempty : pending.pre≠[] := by
      intro empty
      have starts := pending.prefixHead.trans head
      rw [empty] at starts
      cases starts
    refine (congrArg (fun es=>accessWord site.reduce (es.map (plugEnd _ _))) whole).trans ?_
    cases preEq : pending.pre with
    | nil => exact False.elim (nonempty preEq)
    | cons e es =>
      simp only [List.cons_append,List.map_cons,List.map_append,accessWord,
        List.flatMap_append,List.map_nil,List.flatMap_cons,List.flatMap_nil]
      have token (e : Endpoint rhs) :
          arrivalWord site.reduce ((plugEnd (cut).label (rhs).label) (.inr e))=arrivalWord rhs e :=
        arrivalWord_plugRight cut rhs e
      rw [token,token]
      change _++([]++([]++[]))= _
      exact List.append_nil _
  refine ⟨old,relation,labels,start,?_,whole,rule,physical.trans words⟩
  rw [←ending]
  exact last

/-- SAME-word Matches fixes the actual old whole prefix, including its exact
assignment. This is not a fragment cut or a fan target-uniqueness assertion. -/
theorem PathSite.fan_aux_canonical_access
    {directions : B→Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {term : Term}
    (matching : Matches site.net root term) (principal : SiteActionPrincipal site)
    (source : RootAccess site.net root) (target : RootAccess site.reduce root)
    (word : accessWord site.net source.val=accessWord site.reduce target.val)
    (branch : Bool) (q : Aux f)
    (finish : target.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),.inr q⟩)))
    {a b : Context} (labels : Labelling site.reduce target.val a b) :
    ∃ pending : PendingRhsBlock cut rhs (target.val.map (plugEnd (cut).label (rhs).label).invFun) a b,
      ActionCanonicalBlocks site principal pending.pre source.val ∧
      Labelling site.net source.val a pending.middle ∧
      source.val.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inr q⟩)) ∧
      target.val.map (plugEnd (cut).label (rhs).label).invFun=pending.pre++
        [.inr (.inr (.inl (.inr q))),.inr (.inl ⟨.inr q,.inr branch⟩)] := by
  let first : Endpoint cut := .inr (.inl (.inl root))
  have actualHead : target.val.head?=some (AG.plugLeft cut rhs first) := target.property.2.1
  obtain ⟨pending,insideFinish⟩ := labels.pending_new_node cut rhs first actualHead
    (.inl branch) (.inr q) finish
  have rawHead : (target.val.map (plugEnd (cut).label (rhs).label).invFun).head?=some (.inl first) := by
    rw [List.head?_map,actualHead]
    exact congrArg some ((plugEnd (cut).label (rhs).label).left_inv (.inl first))
  obtain ⟨old,relation,oldLabels,oldHead,oldLast,shape,_rule,words⟩ :=
    pending.fan_aux_canonical_trim site principal first rawHead branch q insideFinish
  rw [plug_decomposition_flatten] at words
  have sourceHead : old.head?=some (.inr (.inl root)) := oldHead
  have kind : accessKind site.net old=accessKind site.reduce target.val := by
    simp only [accessKind,oldLast,finish,Option.bind_some,Pairing.involutive]
    rfl
  have typed : ∃observation,accessKind site.net old=some observation := by
    rw [kind];exact target.property.2.2
  have forward := oldLabels.root_forward_of_flow flow root sourceHead positive
  let oldAccess : RootAccess site.net root := ⟨old,⟨⟨⟨a,pending.middle,oldLabels⟩,forward⟩,sourceHead,typed⟩⟩
  have same : oldAccess=source := matching.accessWord_injective (words.symm.trans word.symm)
  have literal : old=source.val := congrArg Subtype.val same
  rw [literal] at relation oldLabels oldLast
  exact ⟨pending,relation,oldLabels,oldLast,shape⟩
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.fanAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "s" => Schema.fanAction Op.lam i j lt
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed
private abbrev keptCopiedFanRight (i j : Nat) (lt : i<j) := (Schema.fanAction Op.lam i j lt).right.net
local notation "rhs" => keptCopiedFanRight i j lt

theorem SourceEdgeFragment.fan_kept_parent_copied_binding_cut
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase)
    (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site) {edge : SourceEdge} {position : Path}
    (source : SourceEdgeFragment current site.net root edge position)
    (target : SourceEdgeFragment current site.reduce root edge position)
    (role : SourceDeparture parentTerm step edge.fromPort)
    (sourceParent : RootAccess site.net root) (targetParent : RootAccess site.reduce root)
    (sourceWord : position=accessWord site.net sourceParent.val++[step])
    (targetWord : position=accessWord site.reduce targetParent.val++[step])
    (parentNode : K) (parentPort : Port (kept parentNode).sort)
    (parentEnd : targetParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inl parentNode,parentPort⟩)))
    (branch : Bool)
    (endAt : target.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),.inr false⟩)))
    {a b : Context} (labels : Labelling site.reduce target.access.val a b) :
    ∃ pivot : Endpoint cut,∃ rawPiece : List (PlugSegment cut rhs),∃ seam output : Context,
      sourceParent.val.getLast?=some (site.outsideEnd pivot) ∧
      targetParent.val.getLast?=some (AG.plugLeft cut rhs pivot) ∧
      target.segments.map (plugEnd (cut).label (rhs).label).invFun=rawPiece++
        [.inr (.inr (.inl (.inr false))),.inr (.inl ⟨.inr false,.inr branch⟩)] ∧
      ActionCanonicalBlocks site principal (Sum.inl pivot::rawPiece)
        (site.outsideEnd pivot::source.segments) ∧
      PlugLabelling cut rhs (Sum.inl pivot::rawPiece) seam output := by
  obtain ⟨pending,whole,_sourceLabels,_sourceEnd,trimmed⟩ :=
    site.fan_aux_canonical_access flow root positive sourceMatches principal source.access target.access
      (source.word.trans target.word.symm) branch false endAt labels
  have targetCut := target.child_prefix targetMatches role targetParent targetWord
  obtain ⟨middle,assignment,_pieceLabels⟩ := target.assignments a b labels
  rw [targetCut.1] at assignment
  have parentLabels : Labelling site.reduce targetParent.val a middle := by
    rcases assignment with ⟨empty,_⟩ | actual
    · have head := targetParent.property.2.1;rw [empty] at head;cases head
    · exact actual
  have parentWord : accessWord site.net sourceParent.val=accessWord site.reduce targetParent.val :=
    List.append_cancel_right (sourceWord.symm.trans targetWord)
  obtain ⟨parent,_parentLabels,parentFinish⟩ :=
    site.action_kept_canonical_access (.fan .lam i j lt) flow root positive sourceMatches principal
      sourceParent targetParent parentWord parentNode parentPort parentEnd parentLabels
  let pivot : Endpoint cut := (cut).wire (.inl ⟨parentNode,parentPort⟩)
  have oldLast : sourceParent.val.getLast?=some (site.outsideEnd pivot) := by
    change sourceParent.val.getLast?=some (site.outsideEnd ((cut).wire (.inl ⟨parentNode,parentPort⟩)))
    rw [←site.outsideEnd_wire];exact parentFinish
  have newLast : targetParent.val.getLast?=some (AG.plugLeft cut rhs pivot) :=
    parentEnd.trans (congrArg some (plugLeft_wire cut rhs (.inl ⟨parentNode,parentPort⟩)))
  have rawLast : (targetParent.val.map (plugEnd (cut).label (rhs).label).invFun).getLast?=
      some (Sum.inl pivot) := by
    rw [List.getLast?_map,newLast]
    exact congrArg some ((plugEnd (cut).label (rhs).label).left_inv (.inl pivot))
  obtain ⟨initial,parentShape⟩ := List.getLast?_eq_some_iff.mp rawLast
  have untrimmed : (initial++[Sum.inl pivot])++
      target.segments.map (plugEnd (cut).label (rhs).label).invFun=pending.pre++
        [.inr (.inr (.inl (.inr false))),.inr (.inl ⟨.inr false,.inr branch⟩)] := by
    rw [←parentShape,←List.map_append,←targetCut.2]
    exact trimmed
  obtain ⟨rawPiece,prefixSplit,pieceSplit⟩ := trim_after_literal_pivot initial
    (target.segments.map (plugEnd (cut).label (rhs).label).invFun) pending.pre (Sum.inl pivot)
    (.inr (.inr (.inl (.inr false)))) (.inr (.inl ⟨.inr false,.inr branch⟩))
    untrimmed (by intro wrong;cases wrong) (by intro wrong;cases wrong)
  have rawSplit : pending.pre=
      targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++rawPiece := by
    rw [parentShape];exact prefixSplit
  obtain ⟨oldPiece,seam,oldSplit,relation,_sameParentLabels,pieceLabels⟩ :=
    whole.cut_at_raw_parent site parent pending.prefixPath.labelling rawSplit pivot rawLast
  have sourceCut := (source.child_prefix sourceMatches role sourceParent sourceWord).2
  have samePiece : oldPiece=source.segments := List.append_cancel_left (oldSplit.symm.trans sourceCut)
  rw [samePiece] at relation
  exact ⟨pivot,rawPiece,seam,pending.middle,oldLast,newLast,pieceSplit,relation,pieceLabels⟩
end
end Lamping.AG
#print axioms Lamping.AG.PendingRhsBlock.fan_aux_canonical_trim
#print axioms Lamping.AG.PathSite.fan_aux_canonical_access
#print axioms Lamping.AG.SourceEdgeFragment.fan_kept_parent_copied_binding_cut

