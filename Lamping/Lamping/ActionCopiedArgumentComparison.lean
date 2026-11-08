import Lamping.Lamping.ActionArgumentPadding
import Lamping.Lamping.ActionRawOutsideCut
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.croAction Op.app i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.croAction Op.app i j lt) V) site.closed
private abbrev argumentCroRight (i j : Nat) (lt : i<j) := (Schema.croAction Op.app i j lt).right.net
local notation "rhs" => argumentCroRight i j lt
local notation "argumentSegment" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inl ()) appArg)) : PlugSegment cut rhs)
local notation "writerSegment" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inr true) (Sum.inl ()))) : PlugSegment cut rhs)
local notation "exitPivot" => (Sum.inr (Sum.inl (Sum.inr (Sum.inr true))) : Endpoint cut)
local notation "oldArgument" => (Sum.inl (Sigma.mk (Sum.inr (Sum.inr ())) appArg) : Endpoint site.net)
/-- The actual whole assignment and literal padded parent determine THIS
ARG piece ordinal; neither an old split nor the wanted old head is supplied. -/
theorem SourceEdgeFragment.cro_copied_argument_kept_cut
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site) {edge : SourceEdge} {position : Path}
    (source : SourceEdgeFragment current site.net root edge position)
    (target : SourceEdgeFragment current site.reduce root edge position)
    (role : SourceDeparture parentTerm .arg edge.fromPort)
    (sourceParent : RootAccess site.net root) (targetParent : RootAccess site.reduce root)
    (sourceWord : position=accessWord site.net sourceParent.val++[.arg])
    (targetWord : position=accessWord site.reduce targetParent.val++[.arg])
    (parentFinish : targetParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),appCtx⟩)))
    (endNode : K) (endPort : Port (kept endNode).sort)
    (endAt : target.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl endNode,endPort⟩)))
    {a b : Context} (wholeLabels : Labelling site.reduce target.access.val a b) :
    ∃ rawTail oldTail seam,
      target.segments.map (plugEnd (cut).label (rhs).label).invFun=
        argumentSegment::writerSegment::Sum.inl exitPivot::rawTail ∧
      source.segments=oldArgument::oldTail ∧
      ActionCanonicalBlocks site principal (Sum.inl exitPivot::rawTail)
        (site.outsideEnd exitPivot::oldTail) ∧
      PlugLabelling cut rhs (Sum.inl exitPivot::rawTail) seam b := by
  have targetCut := target.child_prefix targetMatches role targetParent targetWord
  obtain ⟨pieceInput,_prefixLabels,pieceLabels⟩ := target.assignments a b wholeLabels
  obtain ⟨rawTail,_writerOutput,targetShape,_writerRule,_tailLabels⟩ := unary_copied_argument_fragment cut .cro
    (Bij.refl _) i (j-1) (Or.inr (Or.inl rfl)) targetMatches target role targetParent targetWord parentFinish pieceLabels
  change List (PlugSegment cut rhs) at rawTail
  change target.segments.map (plugEnd (cut).label (rhs).label).invFun=
    argumentSegment::writerSegment::Sum.inl exitPivot::rawTail at targetShape
  obtain ⟨whole,_sourceWholeLabels,_sourceEnd⟩ := site.action_kept_canonical_access (.cro .app i j lt)
    flow root positive sourceMatches principal source.access target.access
    (source.word.trans target.word.symm) endNode endPort endAt wholeLabels
  obtain ⟨c,d,parentLabels⟩ := targetParent.property.1.1
  have parentWord : accessWord site.net sourceParent.val=accessWord site.reduce targetParent.val :=
    List.append_cancel_right (sourceWord.symm.trans targetWord)
  have parent := site.cro_argument_padding_access flow root positive sourceMatches principal
    sourceParent targetParent parentWord parentFinish parentLabels
  have rawSplit : target.access.val.map (plugEnd (cut).label (rhs).label).invFun=
      (targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++
        [argumentSegment,writerSegment,Sum.inl exitPivot])++rawTail := by
    rw [targetCut.2,List.map_append,targetShape]
    simp only [List.append_assoc,List.cons_append,List.nil_append]
  have parentLast : (targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++
      [argumentSegment,writerSegment,Sum.inl exitPivot]).getLast?=some (Sum.inl exitPivot) := by
    simp only [List.getLast?_append,List.getLast?_cons_cons,List.getLast?_singleton,Option.some_or]
  obtain ⟨oldTail,seam,oldSplit,relation,_actualParentLabels,actualPieceLabels⟩ :=
    whole.cut_at_raw_parent site parent (wholeLabels.plug_decomposition cut rhs) rawSplit exitPivot parentLast
  have sourceCut := source.child_prefix sourceMatches role sourceParent sourceWord
  have sourceShape : source.segments=oldArgument::oldTail := by
    apply List.append_cancel_left (as:=sourceParent.val)
    rw [←sourceCut.2,oldSplit]
    simp only [List.append_assoc,List.singleton_append]
  exact ⟨rawTail,oldTail,seam,targetShape,sourceShape,relation,actualPieceLabels⟩

/-- Whole ARG-piece equality on this actual unary class. Writer assignments
are taken from each real whole path; no source Joint or Aux premise occurs. -/
theorem SourceEdgeFragment.cro_copied_argument_kept_equality
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site) {leftEdge rightEdge : SourceEdge} {p q : Path}
    (sourceLeft : SourceEdgeFragment current site.net root leftEdge p)
    (targetLeft : SourceEdgeFragment current site.reduce root leftEdge p)
    (sourceRight : SourceEdgeFragment current site.net root rightEdge q)
    (targetRight : SourceEdgeFragment current site.reduce root rightEdge q)
    (leftRole : SourceDeparture leftTerm .arg leftEdge.fromPort)
    (rightRole : SourceDeparture rightTerm .arg rightEdge.fromPort)
    (oldParentLeft oldParentRight : RootAccess site.net root)
    (newParentLeft newParentRight : RootAccess site.reduce root)
    (oldWordLeft : p=accessWord site.net oldParentLeft.val++[.arg])
    (oldWordRight : q=accessWord site.net oldParentRight.val++[.arg])
    (newWordLeft : p=accessWord site.reduce newParentLeft.val++[.arg])
    (newWordRight : q=accessWord site.reduce newParentRight.val++[.arg])
    (parentLeftAt : newParentLeft.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),appCtx⟩)))
    (parentRightAt : newParentRight.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),appCtx⟩)))
    (leftNode rightNode : K) (leftPort : Port (kept leftNode).sort) (rightPort : Port (kept rightNode).sort)
    (leftEnd : targetLeft.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl leftNode,leftPort⟩)))
    (rightEnd : targetRight.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl rightNode,rightPort⟩))) :
    targetLeft.segments=targetRight.segments ↔sourceLeft.segments=sourceRight.segments := by
  obtain ⟨a,b,leftLabels⟩ := targetLeft.access.property.1.1
  obtain ⟨c,d,rightLabels⟩ := targetRight.access.property.1.1
  obtain ⟨leftRaw,leftOld,leftSeam,leftShape,leftSource,leftRelation,leftPieceLabels⟩ :=
    sourceLeft.cro_copied_argument_kept_cut site flow root positive sourceMatches targetMatches principal
      targetLeft leftRole oldParentLeft newParentLeft oldWordLeft newWordLeft parentLeftAt leftNode leftPort leftEnd leftLabels
  obtain ⟨rightRaw,rightOld,rightSeam,rightShape,rightSource,rightRelation,rightPieceLabels⟩ :=
    sourceRight.cro_copied_argument_kept_cut site flow root positive sourceMatches targetMatches principal
      targetRight rightRole oldParentRight newParentRight oldWordRight newWordRight parentRightAt rightNode rightPort rightEnd rightLabels
  constructor
  · intro pieces
    have maps := congrArg (fun xs=>xs.map (plugEnd (cut).label (rhs).label).invFun) pieces
    dsimp only at maps
    rw [leftShape,rightShape] at maps
    have tails := (List.cons.inj (List.cons.inj (List.cons.inj maps).2).2).2
    have old : site.outsideEnd exitPivot::leftOld=site.outsideEnd exitPivot::rightOld :=
      leftRelation.fixed_source_unique_of_eq site rightRelation (by rw [tails])
    rw [leftSource,rightSource,(List.cons.inj old).2]
  · intro pieces
    have oldWords := leftSource.symm.trans (pieces.trans rightSource)
    have tails := (List.cons.inj oldWords).2
    have raw := leftRelation.unary_target_unique_of_labels site (by intro h;cases h)
      rightRelation leftPieceLabels rightPieceLabels (by rw [tails])
    have maps : targetLeft.segments.map (plugEnd (cut).label (rhs).label).invFun=
        targetRight.segments.map (plugEnd (cut).label (rhs).label).invFun := by
      rw [leftShape,rightShape,(List.cons.inj raw).2]
    have actual := congrArg (fun xs=>xs.map (plugEnd (cut).label (rhs).label)) maps
    simpa only [plug_decomposition_flatten] using actual
end
#print axioms SourceEdgeFragment.cro_copied_argument_kept_cut
#print axioms SourceEdgeFragment.cro_copied_argument_kept_equality
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.braAction Op.app i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.braAction Op.app i j lt) V) site.closed
private abbrev argumentBraRight (i j : Nat) (lt : i<j) := (Schema.braAction Op.app i j lt).right.net
local notation "rhs" => argumentBraRight i j lt
local notation "argumentSegment" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inl ()) appArg)) : PlugSegment cut rhs)
local notation "writerSegment" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inr true) (Sum.inl ()))) : PlugSegment cut rhs)
local notation "exitPivot" => (Sum.inr (Sum.inl (Sum.inr (Sum.inr true))) : Endpoint cut)
local notation "oldArgument" => (Sum.inl (Sigma.mk (Sum.inr (Sum.inr ())) appArg) : Endpoint site.net)
/-- The actual whole assignment and literal padded parent determine THIS
ARG piece ordinal; neither an old split nor the wanted old head is supplied. -/
theorem SourceEdgeFragment.bra_copied_argument_kept_cut
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site) {edge : SourceEdge} {position : Path}
    (source : SourceEdgeFragment current site.net root edge position)
    (target : SourceEdgeFragment current site.reduce root edge position)
    (role : SourceDeparture parentTerm .arg edge.fromPort)
    (sourceParent : RootAccess site.net root) (targetParent : RootAccess site.reduce root)
    (sourceWord : position=accessWord site.net sourceParent.val++[.arg])
    (targetWord : position=accessWord site.reduce targetParent.val++[.arg])
    (parentFinish : targetParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),appCtx⟩)))
    (endNode : K) (endPort : Port (kept endNode).sort)
    (endAt : target.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl endNode,endPort⟩)))
    {a b : Context} (wholeLabels : Labelling site.reduce target.access.val a b) :
    ∃ rawTail oldTail seam,
      target.segments.map (plugEnd (cut).label (rhs).label).invFun=
        argumentSegment::writerSegment::Sum.inl exitPivot::rawTail ∧
      source.segments=oldArgument::oldTail ∧
      ActionCanonicalBlocks site principal (Sum.inl exitPivot::rawTail)
        (site.outsideEnd exitPivot::oldTail) ∧
      PlugLabelling cut rhs (Sum.inl exitPivot::rawTail) seam b := by
  have targetCut := target.child_prefix targetMatches role targetParent targetWord
  obtain ⟨pieceInput,_prefixLabels,pieceLabels⟩ := target.assignments a b wholeLabels
  obtain ⟨rawTail,_writerOutput,targetShape,_writerRule,_tailLabels⟩ := unary_copied_argument_fragment cut .bra
    (Bij.refl _) i (j+1) (Or.inr (Or.inr rfl)) targetMatches target role targetParent targetWord parentFinish pieceLabels
  change List (PlugSegment cut rhs) at rawTail
  change target.segments.map (plugEnd (cut).label (rhs).label).invFun=
    argumentSegment::writerSegment::Sum.inl exitPivot::rawTail at targetShape
  obtain ⟨whole,_sourceWholeLabels,_sourceEnd⟩ := site.action_kept_canonical_access (.bra .app i j lt)
    flow root positive sourceMatches principal source.access target.access
    (source.word.trans target.word.symm) endNode endPort endAt wholeLabels
  obtain ⟨c,d,parentLabels⟩ := targetParent.property.1.1
  have parentWord : accessWord site.net sourceParent.val=accessWord site.reduce targetParent.val :=
    List.append_cancel_right (sourceWord.symm.trans targetWord)
  have parent := site.bra_argument_padding_access flow root positive sourceMatches principal
    sourceParent targetParent parentWord parentFinish parentLabels
  have rawSplit : target.access.val.map (plugEnd (cut).label (rhs).label).invFun=
      (targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++
        [argumentSegment,writerSegment,Sum.inl exitPivot])++rawTail := by
    rw [targetCut.2,List.map_append,targetShape]
    simp only [List.append_assoc,List.cons_append,List.nil_append]
  have parentLast : (targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++
      [argumentSegment,writerSegment,Sum.inl exitPivot]).getLast?=some (Sum.inl exitPivot) := by
    simp only [List.getLast?_append,List.getLast?_cons_cons,List.getLast?_singleton,Option.some_or]
  obtain ⟨oldTail,seam,oldSplit,relation,_actualParentLabels,actualPieceLabels⟩ :=
    whole.cut_at_raw_parent site parent (wholeLabels.plug_decomposition cut rhs) rawSplit exitPivot parentLast
  have sourceCut := source.child_prefix sourceMatches role sourceParent sourceWord
  have sourceShape : source.segments=oldArgument::oldTail := by
    apply List.append_cancel_left (as:=sourceParent.val)
    rw [←sourceCut.2,oldSplit]
    simp only [List.append_assoc,List.singleton_append]
  exact ⟨rawTail,oldTail,seam,targetShape,sourceShape,relation,actualPieceLabels⟩

/-- Whole ARG-piece equality on this actual unary class. Writer assignments
are taken from each real whole path; no source Joint or Aux premise occurs. -/
theorem SourceEdgeFragment.bra_copied_argument_kept_equality
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site) {leftEdge rightEdge : SourceEdge} {p q : Path}
    (sourceLeft : SourceEdgeFragment current site.net root leftEdge p)
    (targetLeft : SourceEdgeFragment current site.reduce root leftEdge p)
    (sourceRight : SourceEdgeFragment current site.net root rightEdge q)
    (targetRight : SourceEdgeFragment current site.reduce root rightEdge q)
    (leftRole : SourceDeparture leftTerm .arg leftEdge.fromPort)
    (rightRole : SourceDeparture rightTerm .arg rightEdge.fromPort)
    (oldParentLeft oldParentRight : RootAccess site.net root)
    (newParentLeft newParentRight : RootAccess site.reduce root)
    (oldWordLeft : p=accessWord site.net oldParentLeft.val++[.arg])
    (oldWordRight : q=accessWord site.net oldParentRight.val++[.arg])
    (newWordLeft : p=accessWord site.reduce newParentLeft.val++[.arg])
    (newWordRight : q=accessWord site.reduce newParentRight.val++[.arg])
    (parentLeftAt : newParentLeft.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),appCtx⟩)))
    (parentRightAt : newParentRight.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),appCtx⟩)))
    (leftNode rightNode : K) (leftPort : Port (kept leftNode).sort) (rightPort : Port (kept rightNode).sort)
    (leftEnd : targetLeft.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl leftNode,leftPort⟩)))
    (rightEnd : targetRight.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl rightNode,rightPort⟩))) :
    targetLeft.segments=targetRight.segments ↔sourceLeft.segments=sourceRight.segments := by
  obtain ⟨a,b,leftLabels⟩ := targetLeft.access.property.1.1
  obtain ⟨c,d,rightLabels⟩ := targetRight.access.property.1.1
  obtain ⟨leftRaw,leftOld,leftSeam,leftShape,leftSource,leftRelation,leftPieceLabels⟩ :=
    sourceLeft.bra_copied_argument_kept_cut site flow root positive sourceMatches targetMatches principal
      targetLeft leftRole oldParentLeft newParentLeft oldWordLeft newWordLeft parentLeftAt leftNode leftPort leftEnd leftLabels
  obtain ⟨rightRaw,rightOld,rightSeam,rightShape,rightSource,rightRelation,rightPieceLabels⟩ :=
    sourceRight.bra_copied_argument_kept_cut site flow root positive sourceMatches targetMatches principal
      targetRight rightRole oldParentRight newParentRight oldWordRight newWordRight parentRightAt rightNode rightPort rightEnd rightLabels
  constructor
  · intro pieces
    have maps := congrArg (fun xs=>xs.map (plugEnd (cut).label (rhs).label).invFun) pieces
    dsimp only at maps
    rw [leftShape,rightShape] at maps
    have tails := (List.cons.inj (List.cons.inj (List.cons.inj maps).2).2).2
    have old : site.outsideEnd exitPivot::leftOld=site.outsideEnd exitPivot::rightOld :=
      leftRelation.fixed_source_unique_of_eq site rightRelation (by rw [tails])
    rw [leftSource,rightSource,(List.cons.inj old).2]
  · intro pieces
    have oldWords := leftSource.symm.trans (pieces.trans rightSource)
    have tails := (List.cons.inj oldWords).2
    have raw := leftRelation.unary_target_unique_of_labels site (by intro h;cases h)
      rightRelation leftPieceLabels rightPieceLabels (by rw [tails])
    have maps : targetLeft.segments.map (plugEnd (cut).label (rhs).label).invFun=
        targetRight.segments.map (plugEnd (cut).label (rhs).label).invFun := by
      rw [leftShape,rightShape,(List.cons.inj raw).2]
    have actual := congrArg (fun xs=>xs.map (plugEnd (cut).label (rhs).label)) maps
    simpa only [plug_decomposition_flatten] using actual
end
#print axioms SourceEdgeFragment.bra_copied_argument_kept_cut
#print axioms SourceEdgeFragment.bra_copied_argument_kept_equality
end Lamping.AG
