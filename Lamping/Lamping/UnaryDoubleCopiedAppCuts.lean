import Lamping.Lamping.ActionCopiedFunctionCuts
import Lamping.Lamping.ActionCopiedArgumentComparison
import Lamping.Lamping.ActionCopiedAppContextCuts
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.croAction Op.app i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.croAction Op.app i j lt) V) site.closed
private abbrev doublecrofunctionRight (i j : Nat) (lt : i<j) := (Schema.croAction Op.app i j lt).right.net
local notation "rhs" => doublecrofunctionRight i j lt
local notation "functionSegment" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inl ()) (Sum.inl ()))) : PlugSegment cut rhs)
local notation "argumentSegment" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inl ()) appArg)) : PlugSegment cut rhs)
local notation "writerSegment" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inr true) (Sum.inl ()))) : PlugSegment cut rhs)
local notation "exitPivot" => (Sum.inr (Sum.inl (Sum.inr (Sum.inl ()))) : Endpoint cut)
local notation "activeAux" => (Sum.inl (Sigma.mk (Sum.inr (Sum.inl ())) (Sum.inr ())) : Endpoint site.net)
local notation "oldArgument" => (Sum.inl (Sigma.mk (Sum.inr (Sum.inr ())) appArg) : Endpoint site.net)
local notation "readerTail" => ([Sum.inr (Sum.inr (Sum.inl (Sum.inr false))),Sum.inr (Sum.inl (Sigma.mk (Sum.inr false) (Sum.inr ())))] : List (PlugSegment cut rhs))

/-- Two-ended finite normalization of an actual copied-APP function edge
ending at copied APP context. Both seams and the OLD split come from the
same whole assignment; the outside writer pivot excludes reader overlap. -/
theorem SourceEdgeFragment.cro_double_copied_app_function_cut
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site)
    (source : SourceEdgeFragment current site.net root edge position)
    (target : SourceEdgeFragment current site.reduce root edge position)
    (role : SourceDeparture parentTerm .fn edge.fromPort)
    (sourceParent : RootAccess site.net root) (targetParent : RootAccess site.reduce root)
    (sourceWord : position=accessWord site.net sourceParent.val++[.fn])
    (targetWord : position=accessWord site.reduce targetParent.val++[.fn])
    (parentFinish : targetParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),appCtx⟩)))
    (endFinish : target.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),appCtx⟩)))
    {a b : Context} (wholeLabels : Labelling site.reduce target.access.val a b) :
    ∃ pending : PendingRhsBlock cut rhs (target.access.val.map (plugEnd (cut).label (rhs).label).invFun) a b,
      ∃ rawTail oldTail seam,
      pending.pre=(targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++[functionSegment,Sum.inl exitPivot])++rawTail ∧
      target.segments.map (plugEnd (cut).label (rhs).label).invFun=[functionSegment,Sum.inl exitPivot]++rawTail++readerTail ∧
      source.segments=reverseEdges principal.edges++activeAux::oldTail ∧
      ActionCanonicalBlocks site principal (Sum.inl exitPivot::rawTail) (site.outsideEnd exitPivot::oldTail) ∧
      PlugLabelling cut rhs (Sum.inl exitPivot::rawTail) seam pending.middle := by
  have targetCut := target.child_prefix targetMatches role targetParent targetWord
  obtain ⟨pieceInput,prefixLabels,pieceLabels⟩ := target.assignments a b wholeLabels
  rw [targetCut.1] at prefixLabels
  have parentLabels : Labelling site.reduce targetParent.val a pieceInput := by
    rcases prefixLabels with ⟨empty,_⟩|actual
    · have head := targetParent.property.2.1;rw [empty] at head;cases head
    · exact actual
  obtain ⟨rawFullTail,targetShape,_targetTailLabels⟩ := unary_copied_function_fragment cut .cro
    (Bij.refl _) i (j-1) targetMatches target role targetParent targetWord parentFinish pieceLabels
  change List (PlugSegment cut rhs) at rawFullTail
  change target.segments.map (plugEnd (cut).label (rhs).label).invFun=[functionSegment,Sum.inl exitPivot]++rawFullTail at targetShape
  obtain ⟨pending,whole,_sourceLabels,_sourceFinish,trimmed⟩ := site.cro_aux_canonical_access
    flow root positive sourceMatches principal source.access target.access
    (source.word.trans target.word.symm) false endFinish wholeLabels
  change PendingRhsBlock cut rhs (target.access.val.map (plugEnd (cut).label (rhs).label).invFun) a b at pending
  have untrimmed : ((targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++[functionSegment])++
      [Sum.inl exitPivot])++rawFullTail=pending.pre++readerTail := by
    rw [←trimmed,targetCut.2,List.map_append,targetShape]
    simp only [List.append_assoc,List.cons_append,List.nil_append]
  obtain ⟨rawTail,trimmedSplit,tailSplit⟩ := trim_after_literal_pivot
    (targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++[functionSegment])
    rawFullTail pending.pre (Sum.inl exitPivot)
    (.inr (.inr (.inl (.inr false)))) (.inr (.inl ⟨.inr false,.inr ()⟩))
    untrimmed (by intro wrong;cases wrong) (by intro wrong;cases wrong)
  have rawSplit : pending.pre=(targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++[functionSegment,Sum.inl exitPivot])++rawTail := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using trimmedSplit
  have parentWord : accessWord site.net sourceParent.val=accessWord site.reduce targetParent.val :=
    List.append_cancel_right (sourceWord.symm.trans targetWord)
  have parent := site.cro_function_padding_access flow root positive sourceMatches principal
    sourceParent targetParent parentWord parentFinish parentLabels
  have parentLast : (targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++[functionSegment,Sum.inl exitPivot]).getLast?=
      some (Sum.inl exitPivot) := by
    simp only [List.getLast?_append,List.getLast?_cons_cons,List.getLast?_singleton,Option.some_or]
  obtain ⟨oldTail,seam,oldSplit,relation,_actualParentLabels,actualPieceLabels⟩ :=
    whole.cut_at_raw_parent site parent pending.prefixPath.labelling rawSplit exitPivot parentLast
  have sourceCut := source.child_prefix sourceMatches role sourceParent sourceWord
  have sourceShape : source.segments=reverseEdges principal.edges++activeAux::oldTail := by
    apply List.append_cancel_left (as:=sourceParent.val)
    rw [←sourceCut.2,oldSplit]
    simp only [List.append_assoc,List.singleton_append]
  refine ⟨pending,rawTail,oldTail,seam,rawSplit,?_,sourceShape,relation,actualPieceLabels⟩
  rw [targetShape,tailSplit]
  simp only [List.append_assoc]
end
#print axioms SourceEdgeFragment.cro_double_copied_app_function_cut
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.croAction Op.app i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.croAction Op.app i j lt) V) site.closed
private abbrev doublecroargumentRight (i j : Nat) (lt : i<j) := (Schema.croAction Op.app i j lt).right.net
local notation "rhs" => doublecroargumentRight i j lt
local notation "functionSegment" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inl ()) (Sum.inl ()))) : PlugSegment cut rhs)
local notation "argumentSegment" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inl ()) appArg)) : PlugSegment cut rhs)
local notation "writerSegment" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inr true) (Sum.inl ()))) : PlugSegment cut rhs)
local notation "exitPivot" => (Sum.inr (Sum.inl (Sum.inr (Sum.inr true))) : Endpoint cut)
local notation "activeAux" => (Sum.inl (Sigma.mk (Sum.inr (Sum.inl ())) (Sum.inr ())) : Endpoint site.net)
local notation "oldArgument" => (Sum.inl (Sigma.mk (Sum.inr (Sum.inr ())) appArg) : Endpoint site.net)
local notation "readerTail" => ([Sum.inr (Sum.inr (Sum.inl (Sum.inr false))),Sum.inr (Sum.inl (Sigma.mk (Sum.inr false) (Sum.inr ())))] : List (PlugSegment cut rhs))

/-- Two-ended finite normalization of an actual copied-APP argument edge
ending at copied APP context. Both seams and the OLD split come from the
same whole assignment; the outside writer pivot excludes reader overlap. -/
theorem SourceEdgeFragment.cro_double_copied_app_argument_cut
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site)
    (source : SourceEdgeFragment current site.net root edge position)
    (target : SourceEdgeFragment current site.reduce root edge position)
    (role : SourceDeparture parentTerm .arg edge.fromPort)
    (sourceParent : RootAccess site.net root) (targetParent : RootAccess site.reduce root)
    (sourceWord : position=accessWord site.net sourceParent.val++[.arg])
    (targetWord : position=accessWord site.reduce targetParent.val++[.arg])
    (parentFinish : targetParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),appCtx⟩)))
    (endFinish : target.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),appCtx⟩)))
    {a b : Context} (wholeLabels : Labelling site.reduce target.access.val a b) :
    ∃ pending : PendingRhsBlock cut rhs (target.access.val.map (plugEnd (cut).label (rhs).label).invFun) a b,
      ∃ rawTail oldTail seam,
      pending.pre=(targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++[argumentSegment,writerSegment,Sum.inl exitPivot])++rawTail ∧
      target.segments.map (plugEnd (cut).label (rhs).label).invFun=[argumentSegment,writerSegment,Sum.inl exitPivot]++rawTail++readerTail ∧
      source.segments=oldArgument::oldTail ∧
      ActionCanonicalBlocks site principal (Sum.inl exitPivot::rawTail) (site.outsideEnd exitPivot::oldTail) ∧
      PlugLabelling cut rhs (Sum.inl exitPivot::rawTail) seam pending.middle := by
  have targetCut := target.child_prefix targetMatches role targetParent targetWord
  obtain ⟨pieceInput,prefixLabels,pieceLabels⟩ := target.assignments a b wholeLabels
  rw [targetCut.1] at prefixLabels
  have parentLabels : Labelling site.reduce targetParent.val a pieceInput := by
    rcases prefixLabels with ⟨empty,_⟩|actual
    · have head := targetParent.property.2.1;rw [empty] at head;cases head
    · exact actual
  obtain ⟨rawFullTail,_writerOutput,targetShape,_writerRule,_targetTailLabels⟩ := unary_copied_argument_fragment cut .cro
    (Bij.refl _) i (j-1) (by simp) targetMatches target role targetParent targetWord parentFinish pieceLabels
  change List (PlugSegment cut rhs) at rawFullTail
  change target.segments.map (plugEnd (cut).label (rhs).label).invFun=[argumentSegment,writerSegment,Sum.inl exitPivot]++rawFullTail at targetShape
  obtain ⟨pending,whole,_sourceLabels,_sourceFinish,trimmed⟩ := site.cro_aux_canonical_access
    flow root positive sourceMatches principal source.access target.access
    (source.word.trans target.word.symm) false endFinish wholeLabels
  change PendingRhsBlock cut rhs (target.access.val.map (plugEnd (cut).label (rhs).label).invFun) a b at pending
  have untrimmed : ((targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++[argumentSegment,writerSegment])++
      [Sum.inl exitPivot])++rawFullTail=pending.pre++readerTail := by
    rw [←trimmed,targetCut.2,List.map_append,targetShape]
    simp only [List.append_assoc,List.cons_append,List.nil_append]
  obtain ⟨rawTail,trimmedSplit,tailSplit⟩ := trim_after_literal_pivot
    (targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++[argumentSegment,writerSegment])
    rawFullTail pending.pre (Sum.inl exitPivot)
    (.inr (.inr (.inl (.inr false)))) (.inr (.inl ⟨.inr false,.inr ()⟩))
    untrimmed (by intro wrong;cases wrong) (by intro wrong;cases wrong)
  have rawSplit : pending.pre=(targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++[argumentSegment,writerSegment,Sum.inl exitPivot])++rawTail := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using trimmedSplit
  have parentWord : accessWord site.net sourceParent.val=accessWord site.reduce targetParent.val :=
    List.append_cancel_right (sourceWord.symm.trans targetWord)
  have parent := site.cro_argument_padding_access flow root positive sourceMatches principal
    sourceParent targetParent parentWord parentFinish parentLabels
  have parentLast : (targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++[argumentSegment,writerSegment,Sum.inl exitPivot]).getLast?=
      some (Sum.inl exitPivot) := by
    simp only [List.getLast?_append,List.getLast?_cons_cons,List.getLast?_singleton,Option.some_or]
  obtain ⟨oldTail,seam,oldSplit,relation,_actualParentLabels,actualPieceLabels⟩ :=
    whole.cut_at_raw_parent site parent pending.prefixPath.labelling rawSplit exitPivot parentLast
  have sourceCut := source.child_prefix sourceMatches role sourceParent sourceWord
  have sourceShape : source.segments=oldArgument::oldTail := by
    apply List.append_cancel_left (as:=sourceParent.val)
    rw [←sourceCut.2,oldSplit]
    simp only [List.append_assoc,List.singleton_append]
  refine ⟨pending,rawTail,oldTail,seam,rawSplit,?_,sourceShape,relation,actualPieceLabels⟩
  rw [targetShape,tailSplit]
  simp only [List.append_assoc]
end
#print axioms SourceEdgeFragment.cro_double_copied_app_argument_cut
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.braAction Op.app i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.braAction Op.app i j lt) V) site.closed
private abbrev doublebrafunctionRight (i j : Nat) (lt : i<j) := (Schema.braAction Op.app i j lt).right.net
local notation "rhs" => doublebrafunctionRight i j lt
local notation "functionSegment" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inl ()) (Sum.inl ()))) : PlugSegment cut rhs)
local notation "argumentSegment" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inl ()) appArg)) : PlugSegment cut rhs)
local notation "writerSegment" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inr true) (Sum.inl ()))) : PlugSegment cut rhs)
local notation "exitPivot" => (Sum.inr (Sum.inl (Sum.inr (Sum.inl ()))) : Endpoint cut)
local notation "activeAux" => (Sum.inl (Sigma.mk (Sum.inr (Sum.inl ())) (Sum.inr ())) : Endpoint site.net)
local notation "oldArgument" => (Sum.inl (Sigma.mk (Sum.inr (Sum.inr ())) appArg) : Endpoint site.net)
local notation "readerTail" => ([Sum.inr (Sum.inr (Sum.inl (Sum.inr false))),Sum.inr (Sum.inl (Sigma.mk (Sum.inr false) (Sum.inr ())))] : List (PlugSegment cut rhs))

/-- Two-ended finite normalization of an actual copied-APP function edge
ending at copied APP context. Both seams and the OLD split come from the
same whole assignment; the outside writer pivot excludes reader overlap. -/
theorem SourceEdgeFragment.bra_double_copied_app_function_cut
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site)
    (source : SourceEdgeFragment current site.net root edge position)
    (target : SourceEdgeFragment current site.reduce root edge position)
    (role : SourceDeparture parentTerm .fn edge.fromPort)
    (sourceParent : RootAccess site.net root) (targetParent : RootAccess site.reduce root)
    (sourceWord : position=accessWord site.net sourceParent.val++[.fn])
    (targetWord : position=accessWord site.reduce targetParent.val++[.fn])
    (parentFinish : targetParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),appCtx⟩)))
    (endFinish : target.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),appCtx⟩)))
    {a b : Context} (wholeLabels : Labelling site.reduce target.access.val a b) :
    ∃ pending : PendingRhsBlock cut rhs (target.access.val.map (plugEnd (cut).label (rhs).label).invFun) a b,
      ∃ rawTail oldTail seam,
      pending.pre=(targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++[functionSegment,Sum.inl exitPivot])++rawTail ∧
      target.segments.map (plugEnd (cut).label (rhs).label).invFun=[functionSegment,Sum.inl exitPivot]++rawTail++readerTail ∧
      source.segments=reverseEdges principal.edges++activeAux::oldTail ∧
      ActionCanonicalBlocks site principal (Sum.inl exitPivot::rawTail) (site.outsideEnd exitPivot::oldTail) ∧
      PlugLabelling cut rhs (Sum.inl exitPivot::rawTail) seam pending.middle := by
  have targetCut := target.child_prefix targetMatches role targetParent targetWord
  obtain ⟨pieceInput,prefixLabels,pieceLabels⟩ := target.assignments a b wholeLabels
  rw [targetCut.1] at prefixLabels
  have parentLabels : Labelling site.reduce targetParent.val a pieceInput := by
    rcases prefixLabels with ⟨empty,_⟩|actual
    · have head := targetParent.property.2.1;rw [empty] at head;cases head
    · exact actual
  obtain ⟨rawFullTail,targetShape,_targetTailLabels⟩ := unary_copied_function_fragment cut .bra
    (Bij.refl _) i (j+1) targetMatches target role targetParent targetWord parentFinish pieceLabels
  change List (PlugSegment cut rhs) at rawFullTail
  change target.segments.map (plugEnd (cut).label (rhs).label).invFun=[functionSegment,Sum.inl exitPivot]++rawFullTail at targetShape
  obtain ⟨pending,whole,_sourceLabels,_sourceFinish,trimmed⟩ := site.bra_aux_canonical_access
    flow root positive sourceMatches principal source.access target.access
    (source.word.trans target.word.symm) false endFinish wholeLabels
  change PendingRhsBlock cut rhs (target.access.val.map (plugEnd (cut).label (rhs).label).invFun) a b at pending
  have untrimmed : ((targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++[functionSegment])++
      [Sum.inl exitPivot])++rawFullTail=pending.pre++readerTail := by
    rw [←trimmed,targetCut.2,List.map_append,targetShape]
    simp only [List.append_assoc,List.cons_append,List.nil_append]
  obtain ⟨rawTail,trimmedSplit,tailSplit⟩ := trim_after_literal_pivot
    (targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++[functionSegment])
    rawFullTail pending.pre (Sum.inl exitPivot)
    (.inr (.inr (.inl (.inr false)))) (.inr (.inl ⟨.inr false,.inr ()⟩))
    untrimmed (by intro wrong;cases wrong) (by intro wrong;cases wrong)
  have rawSplit : pending.pre=(targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++[functionSegment,Sum.inl exitPivot])++rawTail := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using trimmedSplit
  have parentWord : accessWord site.net sourceParent.val=accessWord site.reduce targetParent.val :=
    List.append_cancel_right (sourceWord.symm.trans targetWord)
  have parent := site.bra_function_padding_access flow root positive sourceMatches principal
    sourceParent targetParent parentWord parentFinish parentLabels
  have parentLast : (targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++[functionSegment,Sum.inl exitPivot]).getLast?=
      some (Sum.inl exitPivot) := by
    simp only [List.getLast?_append,List.getLast?_cons_cons,List.getLast?_singleton,Option.some_or]
  obtain ⟨oldTail,seam,oldSplit,relation,_actualParentLabels,actualPieceLabels⟩ :=
    whole.cut_at_raw_parent site parent pending.prefixPath.labelling rawSplit exitPivot parentLast
  have sourceCut := source.child_prefix sourceMatches role sourceParent sourceWord
  have sourceShape : source.segments=reverseEdges principal.edges++activeAux::oldTail := by
    apply List.append_cancel_left (as:=sourceParent.val)
    rw [←sourceCut.2,oldSplit]
    simp only [List.append_assoc,List.singleton_append]
  refine ⟨pending,rawTail,oldTail,seam,rawSplit,?_,sourceShape,relation,actualPieceLabels⟩
  rw [targetShape,tailSplit]
  simp only [List.append_assoc]
end
#print axioms SourceEdgeFragment.bra_double_copied_app_function_cut
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.braAction Op.app i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.braAction Op.app i j lt) V) site.closed
private abbrev doublebraargumentRight (i j : Nat) (lt : i<j) := (Schema.braAction Op.app i j lt).right.net
local notation "rhs" => doublebraargumentRight i j lt
local notation "functionSegment" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inl ()) (Sum.inl ()))) : PlugSegment cut rhs)
local notation "argumentSegment" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inl ()) appArg)) : PlugSegment cut rhs)
local notation "writerSegment" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inr true) (Sum.inl ()))) : PlugSegment cut rhs)
local notation "exitPivot" => (Sum.inr (Sum.inl (Sum.inr (Sum.inr true))) : Endpoint cut)
local notation "activeAux" => (Sum.inl (Sigma.mk (Sum.inr (Sum.inl ())) (Sum.inr ())) : Endpoint site.net)
local notation "oldArgument" => (Sum.inl (Sigma.mk (Sum.inr (Sum.inr ())) appArg) : Endpoint site.net)
local notation "readerTail" => ([Sum.inr (Sum.inr (Sum.inl (Sum.inr false))),Sum.inr (Sum.inl (Sigma.mk (Sum.inr false) (Sum.inr ())))] : List (PlugSegment cut rhs))

/-- Two-ended finite normalization of an actual copied-APP argument edge
ending at copied APP context. Both seams and the OLD split come from the
same whole assignment; the outside writer pivot excludes reader overlap. -/
theorem SourceEdgeFragment.bra_double_copied_app_argument_cut
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site)
    (source : SourceEdgeFragment current site.net root edge position)
    (target : SourceEdgeFragment current site.reduce root edge position)
    (role : SourceDeparture parentTerm .arg edge.fromPort)
    (sourceParent : RootAccess site.net root) (targetParent : RootAccess site.reduce root)
    (sourceWord : position=accessWord site.net sourceParent.val++[.arg])
    (targetWord : position=accessWord site.reduce targetParent.val++[.arg])
    (parentFinish : targetParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),appCtx⟩)))
    (endFinish : target.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),appCtx⟩)))
    {a b : Context} (wholeLabels : Labelling site.reduce target.access.val a b) :
    ∃ pending : PendingRhsBlock cut rhs (target.access.val.map (plugEnd (cut).label (rhs).label).invFun) a b,
      ∃ rawTail oldTail seam,
      pending.pre=(targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++[argumentSegment,writerSegment,Sum.inl exitPivot])++rawTail ∧
      target.segments.map (plugEnd (cut).label (rhs).label).invFun=[argumentSegment,writerSegment,Sum.inl exitPivot]++rawTail++readerTail ∧
      source.segments=oldArgument::oldTail ∧
      ActionCanonicalBlocks site principal (Sum.inl exitPivot::rawTail) (site.outsideEnd exitPivot::oldTail) ∧
      PlugLabelling cut rhs (Sum.inl exitPivot::rawTail) seam pending.middle := by
  have targetCut := target.child_prefix targetMatches role targetParent targetWord
  obtain ⟨pieceInput,prefixLabels,pieceLabels⟩ := target.assignments a b wholeLabels
  rw [targetCut.1] at prefixLabels
  have parentLabels : Labelling site.reduce targetParent.val a pieceInput := by
    rcases prefixLabels with ⟨empty,_⟩|actual
    · have head := targetParent.property.2.1;rw [empty] at head;cases head
    · exact actual
  obtain ⟨rawFullTail,_writerOutput,targetShape,_writerRule,_targetTailLabels⟩ := unary_copied_argument_fragment cut .bra
    (Bij.refl _) i (j+1) (by simp) targetMatches target role targetParent targetWord parentFinish pieceLabels
  change List (PlugSegment cut rhs) at rawFullTail
  change target.segments.map (plugEnd (cut).label (rhs).label).invFun=[argumentSegment,writerSegment,Sum.inl exitPivot]++rawFullTail at targetShape
  obtain ⟨pending,whole,_sourceLabels,_sourceFinish,trimmed⟩ := site.bra_aux_canonical_access
    flow root positive sourceMatches principal source.access target.access
    (source.word.trans target.word.symm) false endFinish wholeLabels
  change PendingRhsBlock cut rhs (target.access.val.map (plugEnd (cut).label (rhs).label).invFun) a b at pending
  have untrimmed : ((targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++[argumentSegment,writerSegment])++
      [Sum.inl exitPivot])++rawFullTail=pending.pre++readerTail := by
    rw [←trimmed,targetCut.2,List.map_append,targetShape]
    simp only [List.append_assoc,List.cons_append,List.nil_append]
  obtain ⟨rawTail,trimmedSplit,tailSplit⟩ := trim_after_literal_pivot
    (targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++[argumentSegment,writerSegment])
    rawFullTail pending.pre (Sum.inl exitPivot)
    (.inr (.inr (.inl (.inr false)))) (.inr (.inl ⟨.inr false,.inr ()⟩))
    untrimmed (by intro wrong;cases wrong) (by intro wrong;cases wrong)
  have rawSplit : pending.pre=(targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++[argumentSegment,writerSegment,Sum.inl exitPivot])++rawTail := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using trimmedSplit
  have parentWord : accessWord site.net sourceParent.val=accessWord site.reduce targetParent.val :=
    List.append_cancel_right (sourceWord.symm.trans targetWord)
  have parent := site.bra_argument_padding_access flow root positive sourceMatches principal
    sourceParent targetParent parentWord parentFinish parentLabels
  have parentLast : (targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++[argumentSegment,writerSegment,Sum.inl exitPivot]).getLast?=
      some (Sum.inl exitPivot) := by
    simp only [List.getLast?_append,List.getLast?_cons_cons,List.getLast?_singleton,Option.some_or]
  obtain ⟨oldTail,seam,oldSplit,relation,_actualParentLabels,actualPieceLabels⟩ :=
    whole.cut_at_raw_parent site parent pending.prefixPath.labelling rawSplit exitPivot parentLast
  have sourceCut := source.child_prefix sourceMatches role sourceParent sourceWord
  have sourceShape : source.segments=oldArgument::oldTail := by
    apply List.append_cancel_left (as:=sourceParent.val)
    rw [←sourceCut.2,oldSplit]
    simp only [List.append_assoc,List.singleton_append]
  refine ⟨pending,rawTail,oldTail,seam,rawSplit,?_,sourceShape,relation,actualPieceLabels⟩
  rw [targetShape,tailSplit]
  simp only [List.append_assoc]
end
#print axioms SourceEdgeFragment.bra_double_copied_app_argument_cut

end Lamping.AG
