import Lamping.Lamping.ActionCopiedBindingFragmentCuts
import Lamping.Lamping.ActionRawOutsideCut
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.croAction Op.lam i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.croAction Op.lam i j lt) V) site.closed
private abbrev doublecroLambdaContextRight (i j : Nat) (lt : i<j) := (Schema.croAction Op.lam i j lt).right.net
local notation "rhs" => doublecroLambdaContextRight i j lt
local notation "writer1" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inl ()) (Sum.inr true))) : PlugSegment cut rhs)
local notation "writer2" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inr true) (Sum.inl ()))) : PlugSegment cut rhs)
local notation "pivot" => (Sum.inr (Sum.inl (Sum.inr (Sum.inr true))) : Endpoint cut)
local notation "padding" => ([writer1,writer2,Sum.inl pivot] : List (PlugSegment cut rhs))
local notation "oldBody" => (Sum.inl (Sigma.mk (Sum.inr (Sum.inr ())) (Sum.inr true)) : Endpoint site.net)

/-- Conditional BODY-to-context normalization with both lambda ends copied.
The actual padded whole and parent determine the literal raw cut and both
seams. This is body padding, not an auxiliary binding-reader trim. -/
theorem SourceEdgeFragment.cro_double_copied_lambda_context_cut
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site)
    (source : SourceEdgeFragment current site.net root edge position)
    (target : SourceEdgeFragment current site.reduce root edge position)
    (role : SourceDeparture parentTerm .body edge.fromPort)
    (sourceParent : RootAccess site.net root) (targetParent : RootAccess site.reduce root)
    (sourceWord : position=accessWord site.net sourceParent.val++[.body])
    (targetWord : position=accessWord site.reduce targetParent.val++[.body])
    (parentFinish : targetParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)))
    (endFinish : target.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)))
    {a b : Context} (wholeLabels : Labelling site.reduce target.access.val a b) :
    ∃ tail seam,
      target.segments.map (plugEnd (cut).label (rhs).label).invFun=writer1::writer2::Sum.inl pivot::tail ∧
      ActionCanonicalBlocks site principal (Sum.inl pivot::(tail++padding)) (source.segments++[oldBody]) ∧
      PlugLabelling cut rhs (Sum.inl pivot::(tail++padding)) seam (InitialOffsets.croAt i b) := by
  have targetCut := target.child_prefix targetMatches role targetParent targetWord
  obtain ⟨middle,prefixLabels,pieceLabels⟩ := target.assignments a b wholeLabels
  rw [targetCut.1] at prefixLabels
  have parentLabels : Labelling site.reduce targetParent.val a middle := by
    rcases prefixLabels with ⟨empty,_⟩|actual
    · have head := targetParent.property.2.1;rw [empty] at head;cases head
    · exact actual
  have parentWord : accessWord site.net sourceParent.val=accessWord site.reduce targetParent.val :=
    List.append_cancel_right (sourceWord.symm.trans targetWord)
  have parent := site.cro_lambda_canonical_access flow root positive sourceMatches principal
    sourceParent targetParent parentWord parentFinish parentLabels
  have whole := site.cro_lambda_canonical_access flow root positive sourceMatches principal
    source.access target.access (source.word.trans target.word.symm) endFinish wholeLabels
  obtain ⟨_oldPadding,_oldFinish,paddedWholeLabels⟩ := site.cro_lambda_padding_labels
    flow root positive sourceMatches principal source.access target.access
    (source.word.trans target.word.symm) endFinish wholeLabels
  obtain ⟨tail,_writerMiddle,targetShape,_writerRule,_tailLabels⟩ := unary_copied_lambda_body_fragment cut .cro
    (Bij.refl Unit) (by simp) i (j-1) (current:=current) targetMatches target role targetParent targetWord parentFinish pieceLabels
  change List (PlugSegment cut rhs) at tail
  change target.segments.map (plugEnd (cut).label (rhs).label).invFun=writer1::writer2::Sum.inl pivot::tail at targetShape
  have rawSplit : target.access.val.map (plugEnd (cut).label (rhs).label).invFun++padding=
      (targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++padding)++(tail++padding) := by
    rw [targetCut.2,List.map_append,targetShape]
    simp only [List.append_assoc,List.cons_append,List.nil_append]
  have parentLast : (targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++padding).getLast?=
      some (Sum.inl pivot) := by
    simp only [List.getLast?_append,List.getLast?_cons_cons,List.getLast?_singleton,Option.some_or]
  obtain ⟨oldPiece,seam,oldSplit,relation,_actualParentLabels,actualPieceLabels⟩ :=
    whole.cut_at_raw_parent site parent paddedWholeLabels rawSplit pivot parentLast
  have sourceCut := (source.child_prefix sourceMatches role sourceParent sourceWord).2
  have oldPieceShape : oldBody::oldPiece=source.segments++[oldBody] := by
    apply Eq.symm
    apply List.append_cancel_left (as:=sourceParent.val)
    rw [←List.append_assoc,←sourceCut]
    simpa only [List.append_assoc,List.singleton_append] using oldSplit
  change ActionCanonicalBlocks site principal (Sum.inl pivot::(tail++padding)) (oldBody::oldPiece) at relation
  rw [oldPieceShape] at relation
  exact ⟨tail,seam,targetShape,relation,actualPieceLabels⟩

/-- Finite fixed-end cancellation over the actual two cut assignments.
No reachable/nonempty instance or common context value is assumed. -/
theorem SourceEdgeFragment.cro_double_copied_lambda_context_equality
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site)
    (sourceLeft : SourceEdgeFragment current site.net root leftEdge p)
    (targetLeft : SourceEdgeFragment current site.reduce root leftEdge p)
    (sourceRight : SourceEdgeFragment current site.net root rightEdge q)
    (targetRight : SourceEdgeFragment current site.reduce root rightEdge q)
    (leftRole : SourceDeparture leftTerm .body leftEdge.fromPort)
    (rightRole : SourceDeparture rightTerm .body rightEdge.fromPort)
    (oldParentLeft oldParentRight : RootAccess site.net root)
    (newParentLeft newParentRight : RootAccess site.reduce root)
    (oldWordLeft : p=accessWord site.net oldParentLeft.val++[.body])
    (oldWordRight : q=accessWord site.net oldParentRight.val++[.body])
    (newWordLeft : p=accessWord site.reduce newParentLeft.val++[.body])
    (newWordRight : q=accessWord site.reduce newParentRight.val++[.body])
    (parentLeftAt : newParentLeft.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)))
    (parentRightAt : newParentRight.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)))
    (leftEnd : targetLeft.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)))
    (rightEnd : targetRight.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inl ()⟩))) :
    targetLeft.segments=targetRight.segments ↔sourceLeft.segments=sourceRight.segments := by
  obtain ⟨a,b,leftWholeLabels⟩ := targetLeft.access.property.1.1
  obtain ⟨c,d,rightWholeLabels⟩ := targetRight.access.property.1.1
  obtain ⟨leftTail,leftSeam,leftShape,leftRelation,leftLabels⟩ :=
    sourceLeft.cro_double_copied_lambda_context_cut site flow root positive sourceMatches targetMatches principal
      targetLeft leftRole oldParentLeft newParentLeft oldWordLeft newWordLeft parentLeftAt leftEnd leftWholeLabels
  obtain ⟨rightTail,rightSeam,rightShape,rightRelation,rightLabels⟩ :=
    sourceRight.cro_double_copied_lambda_context_cut site flow root positive sourceMatches targetMatches principal
      targetRight rightRole oldParentRight newParentRight oldWordRight newWordRight parentRightAt rightEnd rightWholeLabels
  constructor
  · intro pieces
    have maps := congrArg (fun xs=>xs.map (plugEnd (cut).label (rhs).label).invFun) pieces
    dsimp only at maps
    rw [leftShape,rightShape] at maps
    have tails : leftTail=rightTail := (List.cons.inj (List.cons.inj (List.cons.inj maps).2).2).2
    have old := leftRelation.fixed_source_unique_of_eq site rightRelation (by rw [tails])
    exact List.append_cancel_right old
  · intro pieces
    have normalized := leftRelation.unary_target_unique_of_labels site (by intro h;cases h)
      rightRelation leftLabels rightLabels (by rw [pieces])
    have tails : leftTail=rightTail := List.append_cancel_right (List.cons.inj normalized).2
    have maps : targetLeft.segments.map (plugEnd (cut).label (rhs).label).invFun=
        targetRight.segments.map (plugEnd (cut).label (rhs).label).invFun := by
      rw [leftShape,rightShape,tails]
    have actual := congrArg (fun xs=>xs.map (plugEnd (cut).label (rhs).label)) maps
    simpa only [plug_decomposition_flatten] using actual
end
#print axioms SourceEdgeFragment.cro_double_copied_lambda_context_cut
#print axioms SourceEdgeFragment.cro_double_copied_lambda_context_equality
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.braAction Op.lam i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.braAction Op.lam i j lt) V) site.closed
private abbrev doublebraLambdaContextRight (i j : Nat) (lt : i<j) := (Schema.braAction Op.lam i j lt).right.net
local notation "rhs" => doublebraLambdaContextRight i j lt
local notation "writer1" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inl ()) (Sum.inr true))) : PlugSegment cut rhs)
local notation "writer2" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inr true) (Sum.inl ()))) : PlugSegment cut rhs)
local notation "pivot" => (Sum.inr (Sum.inl (Sum.inr (Sum.inr true))) : Endpoint cut)
local notation "padding" => ([writer1,writer2,Sum.inl pivot] : List (PlugSegment cut rhs))
local notation "oldBody" => (Sum.inl (Sigma.mk (Sum.inr (Sum.inr ())) (Sum.inr true)) : Endpoint site.net)

/-- Conditional BODY-to-context normalization with both lambda ends copied.
The actual padded whole and parent determine the literal raw cut and both
seams. This is body padding, not an auxiliary binding-reader trim. -/
theorem SourceEdgeFragment.bra_double_copied_lambda_context_cut
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site)
    (source : SourceEdgeFragment current site.net root edge position)
    (target : SourceEdgeFragment current site.reduce root edge position)
    (role : SourceDeparture parentTerm .body edge.fromPort)
    (sourceParent : RootAccess site.net root) (targetParent : RootAccess site.reduce root)
    (sourceWord : position=accessWord site.net sourceParent.val++[.body])
    (targetWord : position=accessWord site.reduce targetParent.val++[.body])
    (parentFinish : targetParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)))
    (endFinish : target.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)))
    {a b : Context} (wholeLabels : Labelling site.reduce target.access.val a b) :
    ∃ tail seam,
      target.segments.map (plugEnd (cut).label (rhs).label).invFun=writer1::writer2::Sum.inl pivot::tail ∧
      ActionCanonicalBlocks site principal (Sum.inl pivot::(tail++padding)) (source.segments++[oldBody]) ∧
      PlugLabelling cut rhs (Sum.inl pivot::(tail++padding)) seam (InitialOffsets.braAt i b) := by
  have targetCut := target.child_prefix targetMatches role targetParent targetWord
  obtain ⟨middle,prefixLabels,pieceLabels⟩ := target.assignments a b wholeLabels
  rw [targetCut.1] at prefixLabels
  have parentLabels : Labelling site.reduce targetParent.val a middle := by
    rcases prefixLabels with ⟨empty,_⟩|actual
    · have head := targetParent.property.2.1;rw [empty] at head;cases head
    · exact actual
  have parentWord : accessWord site.net sourceParent.val=accessWord site.reduce targetParent.val :=
    List.append_cancel_right (sourceWord.symm.trans targetWord)
  have parent := site.bra_lambda_canonical_access flow root positive sourceMatches principal
    sourceParent targetParent parentWord parentFinish parentLabels
  have whole := site.bra_lambda_canonical_access flow root positive sourceMatches principal
    source.access target.access (source.word.trans target.word.symm) endFinish wholeLabels
  obtain ⟨_oldPadding,_oldFinish,paddedWholeLabels⟩ := site.bra_lambda_padding_labels
    flow root positive sourceMatches principal source.access target.access
    (source.word.trans target.word.symm) endFinish wholeLabels
  obtain ⟨tail,_writerMiddle,targetShape,_writerRule,_tailLabels⟩ := unary_copied_lambda_body_fragment cut .bra
    (Bij.refl Unit) (by simp) i (j+1) (current:=current) targetMatches target role targetParent targetWord parentFinish pieceLabels
  change List (PlugSegment cut rhs) at tail
  change target.segments.map (plugEnd (cut).label (rhs).label).invFun=writer1::writer2::Sum.inl pivot::tail at targetShape
  have rawSplit : target.access.val.map (plugEnd (cut).label (rhs).label).invFun++padding=
      (targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++padding)++(tail++padding) := by
    rw [targetCut.2,List.map_append,targetShape]
    simp only [List.append_assoc,List.cons_append,List.nil_append]
  have parentLast : (targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++padding).getLast?=
      some (Sum.inl pivot) := by
    simp only [List.getLast?_append,List.getLast?_cons_cons,List.getLast?_singleton,Option.some_or]
  obtain ⟨oldPiece,seam,oldSplit,relation,_actualParentLabels,actualPieceLabels⟩ :=
    whole.cut_at_raw_parent site parent paddedWholeLabels rawSplit pivot parentLast
  have sourceCut := (source.child_prefix sourceMatches role sourceParent sourceWord).2
  have oldPieceShape : oldBody::oldPiece=source.segments++[oldBody] := by
    apply Eq.symm
    apply List.append_cancel_left (as:=sourceParent.val)
    rw [←List.append_assoc,←sourceCut]
    simpa only [List.append_assoc,List.singleton_append] using oldSplit
  change ActionCanonicalBlocks site principal (Sum.inl pivot::(tail++padding)) (oldBody::oldPiece) at relation
  rw [oldPieceShape] at relation
  exact ⟨tail,seam,targetShape,relation,actualPieceLabels⟩

/-- Finite fixed-end cancellation over the actual two cut assignments.
No reachable/nonempty instance or common context value is assumed. -/
theorem SourceEdgeFragment.bra_double_copied_lambda_context_equality
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site)
    (sourceLeft : SourceEdgeFragment current site.net root leftEdge p)
    (targetLeft : SourceEdgeFragment current site.reduce root leftEdge p)
    (sourceRight : SourceEdgeFragment current site.net root rightEdge q)
    (targetRight : SourceEdgeFragment current site.reduce root rightEdge q)
    (leftRole : SourceDeparture leftTerm .body leftEdge.fromPort)
    (rightRole : SourceDeparture rightTerm .body rightEdge.fromPort)
    (oldParentLeft oldParentRight : RootAccess site.net root)
    (newParentLeft newParentRight : RootAccess site.reduce root)
    (oldWordLeft : p=accessWord site.net oldParentLeft.val++[.body])
    (oldWordRight : q=accessWord site.net oldParentRight.val++[.body])
    (newWordLeft : p=accessWord site.reduce newParentLeft.val++[.body])
    (newWordRight : q=accessWord site.reduce newParentRight.val++[.body])
    (parentLeftAt : newParentLeft.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)))
    (parentRightAt : newParentRight.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)))
    (leftEnd : targetLeft.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)))
    (rightEnd : targetRight.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inl ()⟩))) :
    targetLeft.segments=targetRight.segments ↔sourceLeft.segments=sourceRight.segments := by
  obtain ⟨a,b,leftWholeLabels⟩ := targetLeft.access.property.1.1
  obtain ⟨c,d,rightWholeLabels⟩ := targetRight.access.property.1.1
  obtain ⟨leftTail,leftSeam,leftShape,leftRelation,leftLabels⟩ :=
    sourceLeft.bra_double_copied_lambda_context_cut site flow root positive sourceMatches targetMatches principal
      targetLeft leftRole oldParentLeft newParentLeft oldWordLeft newWordLeft parentLeftAt leftEnd leftWholeLabels
  obtain ⟨rightTail,rightSeam,rightShape,rightRelation,rightLabels⟩ :=
    sourceRight.bra_double_copied_lambda_context_cut site flow root positive sourceMatches targetMatches principal
      targetRight rightRole oldParentRight newParentRight oldWordRight newWordRight parentRightAt rightEnd rightWholeLabels
  constructor
  · intro pieces
    have maps := congrArg (fun xs=>xs.map (plugEnd (cut).label (rhs).label).invFun) pieces
    dsimp only at maps
    rw [leftShape,rightShape] at maps
    have tails : leftTail=rightTail := (List.cons.inj (List.cons.inj (List.cons.inj maps).2).2).2
    have old := leftRelation.fixed_source_unique_of_eq site rightRelation (by rw [tails])
    exact List.append_cancel_right old
  · intro pieces
    have normalized := leftRelation.unary_target_unique_of_labels site (by intro h;cases h)
      rightRelation leftLabels rightLabels (by rw [pieces])
    have tails : leftTail=rightTail := List.append_cancel_right (List.cons.inj normalized).2
    have maps : targetLeft.segments.map (plugEnd (cut).label (rhs).label).invFun=
        targetRight.segments.map (plugEnd (cut).label (rhs).label).invFun := by
      rw [leftShape,rightShape,tails]
    have actual := congrArg (fun xs=>xs.map (plugEnd (cut).label (rhs).label)) maps
    simpa only [plug_decomposition_flatten] using actual
end
#print axioms SourceEdgeFragment.bra_double_copied_lambda_context_cut
#print axioms SourceEdgeFragment.bra_double_copied_lambda_context_equality

end Lamping.AG
