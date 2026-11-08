import Lamping.Lamping.FanCopiedBindingCuts
import Lamping.Lamping.ActionPendingLambdaBranches
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.fanAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.fanAction Op.lam i j lt) V) site.closed
private abbrev fanContextRight (i j : Nat) (lt : i<j) := (Schema.fanAction Op.lam i j lt).right.net
local notation "rhs" => fanContextRight i j lt
/-- A copied-context pending block has one actual frontier segment. Its
canonical prefix plus the SAME principal is THIS supplied source whole. -/
theorem PathSite.fan_lambda_context_canonical_trim
    {directions : B→Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {term : Term}
    (matching : Matches site.net root term) (principal : SiteActionPrincipal site)
    (source : RootAccess site.net root) (target : RootAccess site.reduce root)
    (word : accessWord site.net source.val=accessWord site.reduce target.val)
    (branch : Bool)
    (finish : target.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),.inl ()⟩)))
    {a b : Context} (labels : Labelling site.reduce target.val a b) :
    ∃ (pending : PendingRhsBlock cut rhs (target.val.map (plugEnd (cut).label (rhs).label).invFun) a b)
      (oldPre : List (Endpoint site.net)),
      pending.middle=b ∧ActionCanonicalBlocks site principal pending.pre oldPre ∧
      Labelling site.net oldPre a b ∧source.val=oldPre++principal.edges ∧
      oldPre.getLast?=some (site.net.wire (.inl ⟨.inr (.inl ()),.inr branch⟩)) ∧
      target.val.map (plugEnd (cut).label (rhs).label).invFun=
        pending.pre++[.inr (.inr (.inl (.inl branch)))] := by
  let first : Endpoint cut := .inr (.inl (.inl root))
  obtain ⟨pending,insideFinish⟩ := labels.pending_new_node cut rhs first target.property.2.1
    (.inl branch) (.inl ()) finish
  have rawHead : (target.val.map (plugEnd (cut).label (rhs).label).invFun).head?=some (.inl first) := by
    rw [List.head?_map,target.property.2.1]
    exact congrArg some ((plugEnd (cut).label (rhs).label).left_inv (.inl first))
  obtain ⟨entry,shape,contexts⟩ := fanRight_lam_context_prefix i j branch pending.enter pending.inside
    pending.middle b pending.insideLabels pending.insideHead insideFinish
  obtain ⟨oldPre,relation,oldLabels,oldHead,oldLast⟩ := pending.prefixPath.action_canonical_lift site
    (.fan .lam i j lt) principal first pending.last (pending.prefixHead.trans rawHead) pending.prefixLast
  rw [contexts] at oldLabels
  have ending : site.outsideEnd pending.last=site.net.wire (.inl ⟨.inr (.inl ()),.inr branch⟩) := by
    have wired := site.outsideEnd_wire pending.last
    rw [pending.arrival,entry] at wired
    have same := congrArg site.net.wire.mate wired
    simpa only [Pairing.involutive] using same
  rw [ending] at oldLast
  have principalNonempty : principal.edges≠[] := by intro empty;have h:=principal.first;rw [empty] at h;cases h
  have routeLabels := transparent_route_labelling site.net principal.edges principalNonempty principal.transparent
    (InitialOffsets.fanAt i branch b)
  have wholeLabels : Labelling site.net (oldPre++principal.edges) a (InitialOffsets.fanAt i branch b) :=
    oldLabels.append_seam routeLabels (by
      intro e f atLast atFirst
      have sameE := Option.some.inj (atLast.symm.trans oldLast)
      have sameF := Option.some.inj (atFirst.symm.trans principal.first)
      subst e;subst f
      rw [Pairing.involutive]
      exact LabelledTurn.node (g:=site.net) (.inr (.inl ())) _ _
        (.direct (InitialOffsets.Event.apply_rel (.fan i branch) b)))
  have rooted : (oldPre++principal.edges).head?=some (.inr (.inl root)) := by
    rw [List.head?_append,oldHead,Option.some_or];rfl
  have last : (oldPre++principal.edges).getLast?=
      some (site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)) := by
    rw [List.getLast?_append,principal.last,Option.some_or]
  have typed : accessKind site.net (oldPre++principal.edges)=some .lam := by
    simp only [accessKind,last,Option.bind_some,Pairing.involutive];rfl
  let oldAccess : RootAccess site.net root := ⟨oldPre++principal.edges,
    ⟨⟨⟨a,_,wholeLabels⟩,wholeLabels.root_forward_of_flow flow root rooted positive⟩,rooted,⟨.lam,typed⟩⟩⟩
  have rawShape : target.val.map (plugEnd (cut).label (rhs).label).invFun=
      pending.pre++[.inr (.inr (.inl (.inl branch)))] := by
    have actual := pending.equation
    rw [shape] at actual
    exact actual
  have preWords := relation.word site pending.prefixPath
  have targetWords : accessWord site.reduce target.val=accessWord site.net oldPre := by
    have prefixWord := preWords
    have wordWhole : accessWord site.reduce ((target.val.map (plugEnd (cut).label (rhs).label).invFun).map
        (plugEnd (cut).label (rhs).label))=accessWord site.net oldPre := by
      rw [rawShape]
      have nonempty : pending.pre≠[] := by intro empty;have h:=pending.prefixHead.trans rawHead;rw [empty] at h;cases h
      cases preEq : pending.pre with
      | nil => exact False.elim (nonempty preEq)
      | cons e es =>
        rw [preEq] at prefixWord
        simp only [List.cons_append,List.map_cons,List.map_append,accessWord,List.flatMap_append,
          List.flatMap_cons,List.flatMap_nil,List.map_nil] at prefixWord ⊢
        have token (e : Endpoint rhs) :
            arrivalWord site.reduce ((plugEnd (cut).label (rhs).label) (.inr e))=arrivalWord rhs e :=
          arrivalWord_plugRight cut rhs e
        rw [token]
        change _++([]++[])=_
        simpa only [List.append_nil] using prefixWord
    simpa only [plug_decomposition_flatten] using wordWhole
  have extendedWords : accessWord site.net (oldPre++principal.edges)=accessWord site.net oldPre := by
    cases oldPre with
    | nil => have h:=oldHead;cases h
    | cons e es =>
      change (es++principal.edges).flatMap (arrivalWord site.net)=_
      have empty := principal.tokens_empty site (.fan .lam i j lt)
      change principal.edges.flatMap (arrivalWord site.net)=[] at empty
      rw [List.flatMap_append,empty,List.append_nil];rfl
  have same : oldAccess=source := matching.accessWord_injective (extendedWords.trans (targetWords.symm.trans word.symm))
  exact ⟨pending,oldPre,contexts,relation,oldLabels,(congrArg Subtype.val same).symm,oldLast,rawShape⟩
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.fanAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "s" => Schema.fanAction Op.lam i j lt
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed
private abbrev keptCopiedFanRight (i j : Nat) (lt : i<j) := (Schema.fanAction Op.lam i j lt).right.net
local notation "rhs" => keptCopiedFanRight i j lt

theorem SourceEdgeFragment.fan_kept_parent_copied_context_cut
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
    (endAt : target.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),.inl ()⟩)))
    {a b : Context} (labels : Labelling site.reduce target.access.val a b) :
    ∃ (pivot : Endpoint cut) (rawPiece : List (PlugSegment cut rhs))
      (oldPiece : List (Endpoint site.net)) (seam : Context),
      sourceParent.val.getLast?=some (site.outsideEnd pivot) ∧
      targetParent.val.getLast?=some (AG.plugLeft cut rhs pivot) ∧
      source.segments=oldPiece++principal.edges ∧
      target.segments.map (plugEnd (cut).label (rhs).label).invFun=
        rawPiece++[.inr (.inr (.inl (.inl branch)))] ∧
      ActionCanonicalBlocks site principal (Sum.inl pivot::rawPiece) (site.outsideEnd pivot::oldPiece) ∧
      PlugLabelling cut rhs (Sum.inl pivot::rawPiece) seam b := by
  obtain ⟨pending,oldPre,contexts,whole,_sourceLabels,wholeSplit,_sourceEnd,trimmed⟩ :=
    site.fan_lambda_context_canonical_trim flow root positive sourceMatches principal source.access target.access
      (source.word.trans target.word.symm) branch endAt labels
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
        [.inr (.inr (.inl (.inl branch)))] := by
    rw [←parentShape,←List.map_append,←targetCut.2]
    exact trimmed
  have extended := congrArg (fun xs=>xs++[.inr (.inr (.inl (.inl branch)))]) untrimmed
  simp only [List.append_assoc,List.singleton_append] at extended
  obtain ⟨rawPiece,prefixSplit,pieceSplitExtra⟩ := trim_after_literal_pivot initial
    (target.segments.map (plugEnd (cut).label (rhs).label).invFun++[.inr (.inr (.inl (.inl branch)))])
    pending.pre (Sum.inl pivot) (.inr (.inr (.inl (.inl branch)))) (.inr (.inr (.inl (.inl branch))))
    (by simpa only [List.append_assoc] using extended) (by intro wrong;cases wrong) (by intro wrong;cases wrong)
  have pieceSplit : target.segments.map (plugEnd (cut).label (rhs).label).invFun=
      rawPiece++[.inr (.inr (.inl (.inl branch)))] :=
    List.append_cancel_right (by simpa only [List.append_assoc] using pieceSplitExtra)
  have rawSplit : pending.pre=
      targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++rawPiece := by
    rw [parentShape];exact prefixSplit
  obtain ⟨oldPiece,seam,oldSplit,relation,_sameParentLabels,pieceLabels⟩ :=
    whole.cut_at_raw_parent site parent pending.prefixPath.labelling rawSplit pivot rawLast
  have sourceCut := (source.child_prefix sourceMatches role sourceParent sourceWord).2
  rw [oldSplit,List.append_assoc] at wholeSplit
  have sourcePiece : source.segments=oldPiece++principal.edges :=
    List.append_cancel_left (sourceCut.symm.trans wholeSplit)
  rw [contexts] at pieceLabels
  exact ⟨pivot,rawPiece,oldPiece,seam,oldLast,newLast,sourcePiece,pieceSplit,relation,pieceLabels⟩
end

end Lamping.AG
#print axioms Lamping.AG.PathSite.fan_lambda_context_canonical_trim
#print axioms Lamping.AG.SourceEdgeFragment.fan_kept_parent_copied_context_cut

