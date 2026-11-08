import Lamping.Lamping.FanVariableFragmentTransport
import Lamping.Lamping.FanKeptFragmentComparison
import Lamping.Lamping.FragmentTerminalSeparation
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {current : LTerm}
theorem Matches.variable_access_typed (matching : Matches g root current.erase)
    (lookup : current.subterm p=some (.var stamp index))
    (path : RootAccess g root) (word : accessWord g path.val=p) :
    accessKind g path.val=some .var := by
  let pos : Position current.erase := ⟨p,by rw [←LTerm.erase_subterm,lookup];rfl⟩
  obtain ⟨observed,observedWord,sub,observedLookup,observes⟩ := Matches.observation g matching pos
  have erased : subtermAt current.erase p=some (.var index) := by rw [←LTerm.erase_subterm,lookup];rfl
  have subEq : sub=.var index := Option.some.inj (observedLookup.symm.trans erased)
  subst sub
  have same : path=observed := matching.accessWord_injective (word.trans observedWord.symm)
  rw [same]
  exact observes.1
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.fanAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.fanAction Op.lam i j lt) V) site.closed
private abbrev variableBindingRight (i j : Nat) (lt : i<j) := (Schema.fanAction Op.lam i j lt).right.net
local notation "rhs" => variableBindingRight i j lt
/-- This is an actual endpoint classification OUTPUT, not a desired profile. -/
theorem PathSite.fan_variable_access_cases {root : B} (path : RootAccess site.reduce root)
    (typed : accessKind site.reduce path.val=some .var) :
    (∃port : NodePort signature K kept,
      path.val.getLast?=some (site.reduce.wire (.inl ⟨.inl port.1,port.2⟩))) ∨
    (∃branch : Bool,
      path.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),lamBind⟩))) := by
  rcases site.action_access_node_cases (.fan .lam i j lt) path with kept |⟨node,port,passive,finish⟩
  · exact Or.inl kept
  · cases passive with
    | fan branch =>
      have actual := accessKind_at_actual_finish typed (.inr (.inl branch)) port finish
      cases port with
      | inl u => cases u;cases actual
      | inr aux =>
        cases aux
        · exact Or.inr ⟨branch,finish⟩
        · cases actual

/-- Reverse preserves each cut SAMEwhole seam and cancels its actual TWO reader segments. -/
theorem SourceEdgeFragment.fan_kept_parent_copied_binding_reflect
    {directions : B→Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site) {leftEdge rightEdge : SourceEdge} {p q : Path}
    (sourceFirst : SourceEdgeFragment current site.net root leftEdge p)
    (targetFirst : SourceEdgeFragment current site.reduce root leftEdge p)
    (sourceSecond : SourceEdgeFragment current site.net root rightEdge q)
    (targetSecond : SourceEdgeFragment current site.reduce root rightEdge q)
    (leftRole : SourceDeparture leftTerm leftStep leftEdge.fromPort)
    (rightRole : SourceDeparture rightTerm rightStep rightEdge.fromPort)
    (sourceLeft sourceRight : RootAccess site.net root) (targetLeft targetRight : RootAccess site.reduce root)
    (sourceLeftWord : p=accessWord site.net sourceLeft.val++[leftStep])
    (sourceRightWord : q=accessWord site.net sourceRight.val++[rightStep])
    (targetLeftWord : p=accessWord site.reduce targetLeft.val++[leftStep])
    (targetRightWord : q=accessWord site.reduce targetRight.val++[rightStep])
    (leftParent rightParent : NodePort signature K kept)
    (leftParentAt : targetLeft.val.getLast?=some (site.reduce.wire (.inl ⟨.inl leftParent.1,leftParent.2⟩)))
    (rightParentAt : targetRight.val.getLast?=some (site.reduce.wire (.inl ⟨.inl rightParent.1,rightParent.2⟩)))
    (leftBranch rightBranch : Bool)
    (leftEndAt : targetFirst.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl leftBranch),lamBind⟩)))
    (rightEndAt : targetSecond.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl rightBranch),lamBind⟩)))
    (pieces : targetFirst.segments=targetSecond.segments) : sourceFirst.segments=sourceSecond.segments := by
  obtain ⟨a,b,leftLabels⟩ := targetFirst.access.property.1.1
  obtain ⟨c,d,rightLabels⟩ := targetSecond.access.property.1.1
  obtain ⟨lp,leftRaw,ls,lo,_leftOldLast,leftNewLast,leftShape,leftRelation,_leftPieceLabels⟩ :=
    sourceFirst.fan_kept_parent_copied_binding_cut site flow root positive sourceMatches targetMatches principal
      targetFirst leftRole sourceLeft targetLeft sourceLeftWord targetLeftWord leftParent.1 leftParent.2 leftParentAt
      leftBranch leftEndAt leftLabels
  obtain ⟨rp,rightRaw,rs,ro,_rightOldLast,rightNewLast,rightShape,rightRelation,_rightPieceLabels⟩ :=
    sourceSecond.fan_kept_parent_copied_binding_cut site flow root positive sourceMatches targetMatches principal
      targetSecond rightRole sourceRight targetRight sourceRightWord targetRightWord rightParent.1 rightParent.2 rightParentAt
      rightBranch rightEndAt rightLabels
  have maps := congrArg (fun xs=>xs.map (plugEnd (cut).label (rhs).label).invFun) pieces
  dsimp only at maps
  rw [leftShape,rightShape] at maps
  have last := congrArg List.getLast? maps
  simp only [List.getLast?_append,List.getLast?_cons_cons,List.getLast?_singleton,Option.some_or] at last
  have branches : leftBranch=rightBranch := by
    cases leftBranch <;> cases rightBranch <;> first |rfl |cases last
  subst rightBranch
  have rawSame : leftRaw=rightRaw := List.append_cancel_right maps
  have parents := SourceEdgeFragment.equal_piece_parent_seams targetMatches targetFirst targetSecond
    leftRole rightRole targetLeft targetRight targetLeftWord targetRightWord pieces
  have outsideSame := Option.some.inj (leftNewLast.symm.trans (parents.trans rightNewLast))
  have pivots : lp=rp := by
    apply Sum.inl.inj
    apply (plugEnd (cut).label (rhs).label).injective
    exact outsideSame
  subst rp
  have oldSame := leftRelation.fixed_source_unique_of_eq site rightRelation (by rw [rawSame])
  exact (List.cons.inj oldSame).2

/-- OLD and target terminal inequalities are reflected independently. -/
theorem SourceEdgeFragment.fan_lambda_copied_binding_vs_kept_terminal
    {directions : B→Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase)
    (principal : SiteActionPrincipal site)
    (sourceCopy : SourceEdgeFragment current site.net root copyEdge p)
    (targetCopy : SourceEdgeFragment current site.reduce root copyEdge p)
    (sourceKept : SourceEdgeFragment current site.net root keptEdge q)
    (targetKept : SourceEdgeFragment current site.reduce root keptEdge q)
    (branch : Bool)
    (copyFinish : targetCopy.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),lamBind⟩)))
    (node : K) (port : Port (kept node).sort)
    (keptFinish : targetKept.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl node,port⟩))) :
    sourceCopy.segments≠sourceKept.segments ∧targetCopy.segments≠targetKept.segments := by
  obtain ⟨a,b,copyLabels⟩ := targetCopy.access.property.1.1
  obtain ⟨_pending,_relation,_labels,oldCopyFinish,_shape⟩ := site.fan_aux_canonical_access flow root positive
    sourceMatches principal sourceCopy.access targetCopy.access (sourceCopy.word.trans targetCopy.word.symm)
    branch false copyFinish copyLabels
  obtain ⟨c,d,keptLabels⟩ := targetKept.access.property.1.1
  obtain ⟨_keptRelation,_keptLabels,oldKeptFinish⟩ := site.action_kept_canonical_access (.fan .lam i j lt)
    flow root positive sourceMatches principal sourceKept.access targetKept.access
    (sourceKept.word.trans targetKept.word.symm) node port keptFinish keptLabels
  exact ⟨sourceCopy.ne_of_terminal_nodes sourceKept (.inr (.inr ())) (.inl node)
      lamBind port oldCopyFinish oldKeptFinish (by intro h;cases h),
    targetCopy.ne_of_terminal_nodes targetKept (.inr (.inl branch)) (.inl node)
      lamBind port copyFinish keptFinish (by intro h;cases h)⟩
end
end Lamping.AG
#print axioms Lamping.AG.Matches.variable_access_typed
#print axioms Lamping.AG.PathSite.fan_variable_access_cases
#print axioms Lamping.AG.SourceEdgeFragment.fan_kept_parent_copied_binding_reflect
#print axioms Lamping.AG.SourceEdgeFragment.fan_lambda_copied_binding_vs_kept_terminal
