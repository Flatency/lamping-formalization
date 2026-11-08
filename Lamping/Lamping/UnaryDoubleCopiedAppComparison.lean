import Lamping.Lamping.UnaryDoubleCopiedAppCuts
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.croAction Op.app i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.croAction Op.app i j lt) V) site.closed
private abbrev comparisoncrofunctionRight (i j : Nat) (lt : i<j) := (Schema.croAction Op.app i j lt).right.net
local notation "rhs" => comparisoncrofunctionRight i j lt
local notation "functionSegment" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inl ()) (Sum.inl ()))) : PlugSegment cut rhs)
local notation "argumentSegment" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inl ()) appArg)) : PlugSegment cut rhs)
local notation "writerSegment" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inr true) (Sum.inl ()))) : PlugSegment cut rhs)
local notation "exitPivot" => (Sum.inr (Sum.inl (Sum.inr (Sum.inl ()))) : Endpoint cut)
local notation "readerTail" => ([Sum.inr (Sum.inr (Sum.inl (Sum.inr false))),Sum.inr (Sum.inl (Sigma.mk (Sum.inr false) (Sum.inr ())))] : List (PlugSegment cut rhs))

/-- Conditional exact piece comparison when both the APP parent and APP
context terminal are copied by this unary action. Each normalized assignment
comes from its own actual whole path. No reachable inhabitant is asserted. -/
theorem SourceEdgeFragment.cro_double_copied_app_function_equality
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site)
    (sourceLeft : SourceEdgeFragment current site.net root leftEdge p)
    (targetLeft : SourceEdgeFragment current site.reduce root leftEdge p)
    (sourceRight : SourceEdgeFragment current site.net root rightEdge q)
    (targetRight : SourceEdgeFragment current site.reduce root rightEdge q)
    (leftRole : SourceDeparture leftTerm .fn leftEdge.fromPort)
    (rightRole : SourceDeparture rightTerm .fn rightEdge.fromPort)
    (oldParentLeft oldParentRight : RootAccess site.net root)
    (newParentLeft newParentRight : RootAccess site.reduce root)
    (oldWordLeft : p=accessWord site.net oldParentLeft.val++[.fn])
    (oldWordRight : q=accessWord site.net oldParentRight.val++[.fn])
    (newWordLeft : p=accessWord site.reduce newParentLeft.val++[.fn])
    (newWordRight : q=accessWord site.reduce newParentRight.val++[.fn])
    (parentLeftAt : newParentLeft.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),appCtx⟩)))
    (parentRightAt : newParentRight.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),appCtx⟩)))
    (leftEnd : targetLeft.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),appCtx⟩)))
    (rightEnd : targetRight.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),appCtx⟩))) :
    targetLeft.segments=targetRight.segments ↔sourceLeft.segments=sourceRight.segments := by
  obtain ⟨a,b,leftWholeLabels⟩ := targetLeft.access.property.1.1
  obtain ⟨c,d,rightWholeLabels⟩ := targetRight.access.property.1.1
  obtain ⟨leftPending,leftRaw,leftOld,leftSeam,_leftRawSplit,leftShape,leftSource,leftRelation,leftLabels⟩ :=
    sourceLeft.cro_double_copied_app_function_cut site flow root positive sourceMatches targetMatches principal
      targetLeft leftRole oldParentLeft newParentLeft oldWordLeft newWordLeft parentLeftAt leftEnd leftWholeLabels
  obtain ⟨rightPending,rightRaw,rightOld,rightSeam,_rightRawSplit,rightShape,rightSource,rightRelation,rightLabels⟩ :=
    sourceRight.cro_double_copied_app_function_cut site flow root positive sourceMatches targetMatches principal
      targetRight rightRole oldParentRight newParentRight oldWordRight newWordRight parentRightAt rightEnd rightWholeLabels
  constructor
  · intro pieces
    have maps := congrArg (fun xs=>xs.map (plugEnd (cut).label (rhs).label).invFun) pieces
    dsimp only at maps
    rw [leftShape,rightShape] at maps
    have normalized : leftRaw=rightRaw := List.append_cancel_left (List.append_cancel_right maps)
    have old : site.outsideEnd exitPivot::leftOld=site.outsideEnd exitPivot::rightOld :=
      leftRelation.fixed_source_unique_of_eq site rightRelation (by rw [normalized])
    rw [leftSource,rightSource,(List.cons.inj old).2]
  · intro pieces
    have oldWords := leftSource.symm.trans (pieces.trans rightSource)
    have tails : leftOld=rightOld := (List.cons.inj (List.append_cancel_left oldWords)).2
    have raw := leftRelation.unary_target_unique_of_labels site (by intro h;cases h)
      rightRelation leftLabels rightLabels (by rw [tails])
    have maps : targetLeft.segments.map (plugEnd (cut).label (rhs).label).invFun=
        targetRight.segments.map (plugEnd (cut).label (rhs).label).invFun := by
      rw [leftShape,rightShape,(List.cons.inj raw).2]
    have actual := congrArg (fun xs=>xs.map (plugEnd (cut).label (rhs).label)) maps
    simpa only [plug_decomposition_flatten] using actual
end
#print axioms SourceEdgeFragment.cro_double_copied_app_function_equality
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.croAction Op.app i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.croAction Op.app i j lt) V) site.closed
private abbrev comparisoncroargumentRight (i j : Nat) (lt : i<j) := (Schema.croAction Op.app i j lt).right.net
local notation "rhs" => comparisoncroargumentRight i j lt
local notation "functionSegment" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inl ()) (Sum.inl ()))) : PlugSegment cut rhs)
local notation "argumentSegment" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inl ()) appArg)) : PlugSegment cut rhs)
local notation "writerSegment" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inr true) (Sum.inl ()))) : PlugSegment cut rhs)
local notation "exitPivot" => (Sum.inr (Sum.inl (Sum.inr (Sum.inr true))) : Endpoint cut)
local notation "readerTail" => ([Sum.inr (Sum.inr (Sum.inl (Sum.inr false))),Sum.inr (Sum.inl (Sigma.mk (Sum.inr false) (Sum.inr ())))] : List (PlugSegment cut rhs))

/-- Conditional exact piece comparison when both the APP parent and APP
context terminal are copied by this unary action. Each normalized assignment
comes from its own actual whole path. No reachable inhabitant is asserted. -/
theorem SourceEdgeFragment.cro_double_copied_app_argument_equality
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site)
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
    (leftEnd : targetLeft.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),appCtx⟩)))
    (rightEnd : targetRight.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),appCtx⟩))) :
    targetLeft.segments=targetRight.segments ↔sourceLeft.segments=sourceRight.segments := by
  obtain ⟨a,b,leftWholeLabels⟩ := targetLeft.access.property.1.1
  obtain ⟨c,d,rightWholeLabels⟩ := targetRight.access.property.1.1
  obtain ⟨leftPending,leftRaw,leftOld,leftSeam,_leftRawSplit,leftShape,leftSource,leftRelation,leftLabels⟩ :=
    sourceLeft.cro_double_copied_app_argument_cut site flow root positive sourceMatches targetMatches principal
      targetLeft leftRole oldParentLeft newParentLeft oldWordLeft newWordLeft parentLeftAt leftEnd leftWholeLabels
  obtain ⟨rightPending,rightRaw,rightOld,rightSeam,_rightRawSplit,rightShape,rightSource,rightRelation,rightLabels⟩ :=
    sourceRight.cro_double_copied_app_argument_cut site flow root positive sourceMatches targetMatches principal
      targetRight rightRole oldParentRight newParentRight oldWordRight newWordRight parentRightAt rightEnd rightWholeLabels
  constructor
  · intro pieces
    have maps := congrArg (fun xs=>xs.map (plugEnd (cut).label (rhs).label).invFun) pieces
    dsimp only at maps
    rw [leftShape,rightShape] at maps
    have normalized : leftRaw=rightRaw := List.append_cancel_left (List.append_cancel_right maps)
    have old : site.outsideEnd exitPivot::leftOld=site.outsideEnd exitPivot::rightOld :=
      leftRelation.fixed_source_unique_of_eq site rightRelation (by rw [normalized])
    rw [leftSource,rightSource,(List.cons.inj old).2]
  · intro pieces
    have oldWords := leftSource.symm.trans (pieces.trans rightSource)
    have tails : leftOld=rightOld := (List.cons.inj oldWords).2
    have raw := leftRelation.unary_target_unique_of_labels site (by intro h;cases h)
      rightRelation leftLabels rightLabels (by rw [tails])
    have maps : targetLeft.segments.map (plugEnd (cut).label (rhs).label).invFun=
        targetRight.segments.map (plugEnd (cut).label (rhs).label).invFun := by
      rw [leftShape,rightShape,(List.cons.inj raw).2]
    have actual := congrArg (fun xs=>xs.map (plugEnd (cut).label (rhs).label)) maps
    simpa only [plug_decomposition_flatten] using actual
end
#print axioms SourceEdgeFragment.cro_double_copied_app_argument_equality
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.braAction Op.app i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.braAction Op.app i j lt) V) site.closed
private abbrev comparisonbrafunctionRight (i j : Nat) (lt : i<j) := (Schema.braAction Op.app i j lt).right.net
local notation "rhs" => comparisonbrafunctionRight i j lt
local notation "functionSegment" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inl ()) (Sum.inl ()))) : PlugSegment cut rhs)
local notation "argumentSegment" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inl ()) appArg)) : PlugSegment cut rhs)
local notation "writerSegment" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inr true) (Sum.inl ()))) : PlugSegment cut rhs)
local notation "exitPivot" => (Sum.inr (Sum.inl (Sum.inr (Sum.inl ()))) : Endpoint cut)
local notation "readerTail" => ([Sum.inr (Sum.inr (Sum.inl (Sum.inr false))),Sum.inr (Sum.inl (Sigma.mk (Sum.inr false) (Sum.inr ())))] : List (PlugSegment cut rhs))

/-- Conditional exact piece comparison when both the APP parent and APP
context terminal are copied by this unary action. Each normalized assignment
comes from its own actual whole path. No reachable inhabitant is asserted. -/
theorem SourceEdgeFragment.bra_double_copied_app_function_equality
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site)
    (sourceLeft : SourceEdgeFragment current site.net root leftEdge p)
    (targetLeft : SourceEdgeFragment current site.reduce root leftEdge p)
    (sourceRight : SourceEdgeFragment current site.net root rightEdge q)
    (targetRight : SourceEdgeFragment current site.reduce root rightEdge q)
    (leftRole : SourceDeparture leftTerm .fn leftEdge.fromPort)
    (rightRole : SourceDeparture rightTerm .fn rightEdge.fromPort)
    (oldParentLeft oldParentRight : RootAccess site.net root)
    (newParentLeft newParentRight : RootAccess site.reduce root)
    (oldWordLeft : p=accessWord site.net oldParentLeft.val++[.fn])
    (oldWordRight : q=accessWord site.net oldParentRight.val++[.fn])
    (newWordLeft : p=accessWord site.reduce newParentLeft.val++[.fn])
    (newWordRight : q=accessWord site.reduce newParentRight.val++[.fn])
    (parentLeftAt : newParentLeft.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),appCtx⟩)))
    (parentRightAt : newParentRight.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),appCtx⟩)))
    (leftEnd : targetLeft.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),appCtx⟩)))
    (rightEnd : targetRight.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),appCtx⟩))) :
    targetLeft.segments=targetRight.segments ↔sourceLeft.segments=sourceRight.segments := by
  obtain ⟨a,b,leftWholeLabels⟩ := targetLeft.access.property.1.1
  obtain ⟨c,d,rightWholeLabels⟩ := targetRight.access.property.1.1
  obtain ⟨leftPending,leftRaw,leftOld,leftSeam,_leftRawSplit,leftShape,leftSource,leftRelation,leftLabels⟩ :=
    sourceLeft.bra_double_copied_app_function_cut site flow root positive sourceMatches targetMatches principal
      targetLeft leftRole oldParentLeft newParentLeft oldWordLeft newWordLeft parentLeftAt leftEnd leftWholeLabels
  obtain ⟨rightPending,rightRaw,rightOld,rightSeam,_rightRawSplit,rightShape,rightSource,rightRelation,rightLabels⟩ :=
    sourceRight.bra_double_copied_app_function_cut site flow root positive sourceMatches targetMatches principal
      targetRight rightRole oldParentRight newParentRight oldWordRight newWordRight parentRightAt rightEnd rightWholeLabels
  constructor
  · intro pieces
    have maps := congrArg (fun xs=>xs.map (plugEnd (cut).label (rhs).label).invFun) pieces
    dsimp only at maps
    rw [leftShape,rightShape] at maps
    have normalized : leftRaw=rightRaw := List.append_cancel_left (List.append_cancel_right maps)
    have old : site.outsideEnd exitPivot::leftOld=site.outsideEnd exitPivot::rightOld :=
      leftRelation.fixed_source_unique_of_eq site rightRelation (by rw [normalized])
    rw [leftSource,rightSource,(List.cons.inj old).2]
  · intro pieces
    have oldWords := leftSource.symm.trans (pieces.trans rightSource)
    have tails : leftOld=rightOld := (List.cons.inj (List.append_cancel_left oldWords)).2
    have raw := leftRelation.unary_target_unique_of_labels site (by intro h;cases h)
      rightRelation leftLabels rightLabels (by rw [tails])
    have maps : targetLeft.segments.map (plugEnd (cut).label (rhs).label).invFun=
        targetRight.segments.map (plugEnd (cut).label (rhs).label).invFun := by
      rw [leftShape,rightShape,(List.cons.inj raw).2]
    have actual := congrArg (fun xs=>xs.map (plugEnd (cut).label (rhs).label)) maps
    simpa only [plug_decomposition_flatten] using actual
end
#print axioms SourceEdgeFragment.bra_double_copied_app_function_equality
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.braAction Op.app i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.braAction Op.app i j lt) V) site.closed
private abbrev comparisonbraargumentRight (i j : Nat) (lt : i<j) := (Schema.braAction Op.app i j lt).right.net
local notation "rhs" => comparisonbraargumentRight i j lt
local notation "functionSegment" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inl ()) (Sum.inl ()))) : PlugSegment cut rhs)
local notation "argumentSegment" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inl ()) appArg)) : PlugSegment cut rhs)
local notation "writerSegment" => (Sum.inr (Sum.inl (Sigma.mk (Sum.inr true) (Sum.inl ()))) : PlugSegment cut rhs)
local notation "exitPivot" => (Sum.inr (Sum.inl (Sum.inr (Sum.inr true))) : Endpoint cut)
local notation "readerTail" => ([Sum.inr (Sum.inr (Sum.inl (Sum.inr false))),Sum.inr (Sum.inl (Sigma.mk (Sum.inr false) (Sum.inr ())))] : List (PlugSegment cut rhs))

/-- Conditional exact piece comparison when both the APP parent and APP
context terminal are copied by this unary action. Each normalized assignment
comes from its own actual whole path. No reachable inhabitant is asserted. -/
theorem SourceEdgeFragment.bra_double_copied_app_argument_equality
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site)
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
    (leftEnd : targetLeft.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),appCtx⟩)))
    (rightEnd : targetRight.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),appCtx⟩))) :
    targetLeft.segments=targetRight.segments ↔sourceLeft.segments=sourceRight.segments := by
  obtain ⟨a,b,leftWholeLabels⟩ := targetLeft.access.property.1.1
  obtain ⟨c,d,rightWholeLabels⟩ := targetRight.access.property.1.1
  obtain ⟨leftPending,leftRaw,leftOld,leftSeam,_leftRawSplit,leftShape,leftSource,leftRelation,leftLabels⟩ :=
    sourceLeft.bra_double_copied_app_argument_cut site flow root positive sourceMatches targetMatches principal
      targetLeft leftRole oldParentLeft newParentLeft oldWordLeft newWordLeft parentLeftAt leftEnd leftWholeLabels
  obtain ⟨rightPending,rightRaw,rightOld,rightSeam,_rightRawSplit,rightShape,rightSource,rightRelation,rightLabels⟩ :=
    sourceRight.bra_double_copied_app_argument_cut site flow root positive sourceMatches targetMatches principal
      targetRight rightRole oldParentRight newParentRight oldWordRight newWordRight parentRightAt rightEnd rightWholeLabels
  constructor
  · intro pieces
    have maps := congrArg (fun xs=>xs.map (plugEnd (cut).label (rhs).label).invFun) pieces
    dsimp only at maps
    rw [leftShape,rightShape] at maps
    have normalized : leftRaw=rightRaw := List.append_cancel_left (List.append_cancel_right maps)
    have old : site.outsideEnd exitPivot::leftOld=site.outsideEnd exitPivot::rightOld :=
      leftRelation.fixed_source_unique_of_eq site rightRelation (by rw [normalized])
    rw [leftSource,rightSource,(List.cons.inj old).2]
  · intro pieces
    have oldWords := leftSource.symm.trans (pieces.trans rightSource)
    have tails : leftOld=rightOld := (List.cons.inj oldWords).2
    have raw := leftRelation.unary_target_unique_of_labels site (by intro h;cases h)
      rightRelation leftLabels rightLabels (by rw [tails])
    have maps : targetLeft.segments.map (plugEnd (cut).label (rhs).label).invFun=
        targetRight.segments.map (plugEnd (cut).label (rhs).label).invFun := by
      rw [leftShape,rightShape,(List.cons.inj raw).2]
    have actual := congrArg (fun xs=>xs.map (plugEnd (cut).label (rhs).label)) maps
    simpa only [plug_decomposition_flatten] using actual
end
#print axioms SourceEdgeFragment.bra_double_copied_app_argument_equality

end Lamping.AG
