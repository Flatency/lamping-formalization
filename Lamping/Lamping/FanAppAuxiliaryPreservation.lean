import Lamping.Lamping.FanAppCopiedArgumentContextCuts
import Lamping.Lamping.FanAppArgumentLambdaTransport
import Lamping.Lamping.FanVariableBindingComparison
import Lamping.Lamping.ActionPrerequisiteCopyBranches
set_option maxHeartbeats 4000000
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {current : LTerm} {g : Net signature N B W} {root : B}

/-- Metadata is an output of the actual occurrence, never a graph premise. -/
private structure AuxiliaryParent (position : SyntaxIncidence.Edge current)
    (fragment : OccurrenceFragment current g root position.val) where
  parent : Path
  term : LTerm
  step : Step
  lookup : current.subterm parent=some term
  split : position.val=parent++[step]
  role : SourceDeparture term step (sourceEdge fragment.environment fragment.context fragment.term).fromPort
  allowed : step=.arg ∨step=.body
  proper : SyntaxIncidence.ProperAt current parent
  endpoint : SyntaxIncidence.source current position=some ⟨parent,proper⟩

private theorem auxiliary_parent (position : SyntaxIncidence.Edge current)
    (fragment : OccurrenceFragment current g root position.val)
    (aux : AuxiliaryAt current position.val)
    (available : ∃edges,EndpointChain current (SyntaxIncidence.source current position) edges) :
    Nonempty (AuxiliaryParent position fragment) := by
  rcases fragment with ⟨sub,env,ctx,occurrence,fragment⟩
  have fromEq : (sourceEdge env ctx sub).fromPort=ctx := by
    cases sub <;> rfl
  rcases occurrence.last_departure with ⟨external,_⟩|⟨parent,step,term,split,lookup,role⟩
  · have endpoint := SyntaxIncidence.source_eq_of_spec current position (vertex:=none) external
    obtain ⟨edges,chain⟩ := available
    rw [endpoint] at chain
    exact False.elim chain
  · cases role with
    | fn => exact False.elim (aux.1 ⟨parent,_,_,_,split,lookup⟩)
    | arg =>
      have proper : SyntaxIncidence.ProperAt current parent := Or.inl ⟨_,_,_,lookup⟩
      exact ⟨⟨parent,_,.arg,lookup,split,(by rw [fromEq];exact .arg),Or.inl rfl,proper,
        SyntaxIncidence.source_eq_of_spec current position ⟨.arg,_,_,split,lookup,.arg⟩⟩⟩
    | body =>
      have proper : SyntaxIncidence.ProperAt current parent := Or.inr ⟨_,_,lookup⟩
      exact ⟨⟨parent,_,.body,lookup,split,(by rw [fromEq];exact .body),Or.inr rfl,proper,
        SyntaxIncidence.source_eq_of_spec current position ⟨.body,_,_,split,lookup,.body⟩⟩⟩

private theorem auxiliary_child_cases (position : SyntaxIncidence.Edge current)
    (aux : AuxiliaryAt current position.val) :
    (∃stamp fn arg,current.subterm position.val=some (.app stamp fn arg)) ∨
      ∃stamp index,current.subterm position.val=some (.var stamp index) := by
  obtain ⟨child,lookup⟩ := SyntaxIncidence.edge_lookup current position
  cases child with
  | app stamp fn arg => exact Or.inl ⟨stamp,fn,arg,lookup⟩
  | var stamp index => exact Or.inr ⟨stamp,index,lookup⟩
  | lam stamp body => exact False.elim (aux.2 ⟨stamp,body,lookup⟩)

private theorem app_variable_source_ne (matching : Matches g root current.erase)
    (first : OccurrenceFragment current g root p) (second : OccurrenceFragment current g root q)
    (app : current.subterm p=some (.app stamp fn arg))
    (var : current.subterm q=some (.var atom index)) :
    first.fragment.segments≠second.fragment.segments := by
  intro equal
  have kinds := first.fragment.access_kind_eq_of_segments_eq second.fragment equal
  rw [matching.app_access_typed app first.fragment.access first.fragment.word,
    matching.variable_access_typed var second.fragment.access second.fragment.word] at kinds
  cases kinds
end

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.fanAction .app i j lt) kept (B:=B) (W:=W) (V:=V))

private theorem copied_access_app {current : LTerm} {root : B}
    (matching : Matches site.reduce root current.erase) (position : Position current.erase)
    (access : RootAccess site.reduce root) (word : accessWord site.reduce access.val=position.val)
    (branch : Bool)
    (finish : access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),appCtx⟩))) :
    ∃stamp fn arg,current.subterm position.val=some (.app stamp fn arg) := by
  have actual : accessKind site.reduce access.val=some .app := by
    simp only [accessKind,finish,Option.bind_some,Pairing.involutive];rfl
  cases lookup : current.subterm position.val with
  | none =>
    have valid := position.property
    rw [←LTerm.erase_subterm,lookup] at valid
    cases valid
  | some term =>
    cases term with
    | app stamp fn arg => exact ⟨stamp,fn,arg,rfl⟩
    | lam stamp body =>
      have wrong := matching.lambda_access_typed lookup access word
      cases actual.symm.trans wrong
    | var stamp index =>
      have wrong := matching.variable_access_typed lookup access word
      cases actual.symm.trans wrong

/-- Both branch locks use the real APP endpoint's first FUNCTION slot. -/
private theorem endpoint_app_branches
    {current : LTerm} {root : B} {boundary : B→Bool}
    (matching : Matches site.net root current.erase) (inputs : RootInputs site.net root)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (closed : Closed current.erase) (selection : OccurrenceFragmentSelection current site.net root)
    (joint : JointRepresentation closed selection)
    (leftLookup : current.subterm p=some (.app la lf lx))
    (rightLookup : current.subterm q=some (.app ra rf rx))
    (iso : SuccessfulEndpointIso current closed
      (some ⟨p,Or.inl ⟨la,lf,lx,leftLookup⟩⟩) (some ⟨q,Or.inl ⟨ra,rf,rx,rightLookup⟩⟩))
    (leftTarget rightTarget : RootAccess site.reduce root)
    (leftWord : accessWord site.reduce leftTarget.val=p)
    (rightWord : accessWord site.reduce rightTarget.val=q)
    (lb rb : Bool)
    (leftAt : leftTarget.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl lb),appCtx⟩)))
    (rightAt : rightTarget.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl rb),appCtx⟩))) : lb=rb := by
  obtain ⟨es,fs,leftChain,rightChain,bare⟩ := iso
  exact site.prerequisite_app_copy_branches matching inputs flow positive closed selection joint
    leftLookup rightLookup leftChain rightChain bare leftTarget rightTarget leftWord rightWord lb rb leftAt rightAt

private theorem terminal_mixed_source_ne
    {current : LTerm} {root : B} {boundary : B→Bool}
    (matching : Matches site.net root current.erase) (flow : FlowBalance site.net boundary)
    (positive : boundary root=true) (principal : SiteActionPrincipal site)
    (sourceFirst : SourceEdgeFragment current site.net root leftEdge p)
    (targetFirst : SourceEdgeFragment current site.reduce root leftEdge p)
    (sourceSecond : SourceEdgeFragment current site.net root rightEdge q)
    (targetSecond : SourceEdgeFragment current site.reduce root rightEdge q)
    (branch : Bool)
    (copyAt : targetFirst.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),appCtx⟩)))
    (keptPort : NodePort signature K kept)
    (keptAt : targetSecond.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl keptPort.1,keptPort.2⟩))) :
    sourceFirst.segments≠sourceSecond.segments := by
  obtain ⟨a,b,labels⟩ := targetFirst.access.property.1.1
  obtain ⟨_,_,_,leftFinish,_⟩ := site.fan_aux_canonical_access flow root positive matching principal
    sourceFirst.access targetFirst.access (sourceFirst.word.trans targetFirst.word.symm) branch false copyAt labels
  obtain ⟨c,d,otherLabels⟩ := targetSecond.access.property.1.1
  obtain ⟨_,_,rightFinish⟩ := site.action_kept_canonical_access (.fan .app i j lt) flow root positive matching principal
    sourceSecond.access targetSecond.access (sourceSecond.word.trans targetSecond.word.symm)
    keptPort.1 keptPort.2 keptAt otherLabels
  exact sourceFirst.ne_of_terminal_nodes sourceSecond (.inr (.inr ())) (.inl keptPort.1)
    appCtx keptPort.2 leftFinish rightFinish (by intro wrong;cases wrong)

private theorem parent_mixed_source_ne
    {current : LTerm} {root : B} {boundary : B→Bool}
    (matching : Matches site.net root current.erase) (flow : FlowBalance site.net boundary)
    (positive : boundary root=true) (principal : SiteActionPrincipal site)
    (sourceFirst : SourceEdgeFragment current site.net root leftEdge p)
    (sourceSecond : SourceEdgeFragment current site.net root rightEdge q)
    (leftRole : SourceDeparture leftTerm leftStep leftEdge.fromPort)
    (rightRole : SourceDeparture rightTerm rightStep rightEdge.fromPort)
    (sourceLeft sourceRight : RootAccess site.net root) (targetLeft targetRight : RootAccess site.reduce root)
    (sourceLeftWord : p=accessWord site.net sourceLeft.val++[leftStep])
    (sourceRightWord : q=accessWord site.net sourceRight.val++[rightStep])
    (leftWord : accessWord site.net sourceLeft.val=accessWord site.reduce targetLeft.val)
    (rightWord : accessWord site.net sourceRight.val=accessWord site.reduce targetRight.val)
    (branch : Bool)
    (copyAt : targetLeft.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),appCtx⟩)))
    (keptPort : NodePort signature K kept)
    (keptAt : targetRight.val.getLast?=some (site.reduce.wire (.inl ⟨.inl keptPort.1,keptPort.2⟩))) :
    sourceFirst.segments≠sourceSecond.segments := by
  obtain ⟨a,b,labels⟩ := targetLeft.property.1.1
  obtain ⟨_,_,_,leftFinish,_⟩ := site.fan_aux_canonical_access flow root positive matching principal
    sourceLeft targetLeft leftWord branch false copyAt labels
  obtain ⟨c,d,otherLabels⟩ := targetRight.property.1.1
  obtain ⟨_,_,rightFinish⟩ := site.action_kept_canonical_access (.fan .app i j lt) flow root positive matching principal
    sourceRight targetRight rightWord keptPort.1 keptPort.2 keptAt otherLabels
  intro equal
  have seams := sourceFirst.equal_piece_parent_seams matching sourceSecond leftRole rightRole
    sourceLeft sourceRight sourceLeftWord sourceRightWord equal
  rw [leftFinish,rightFinish] at seams
  have endpoints := congrArg site.net.wire (Option.some.inj seams)
  simp only [Pairing.involutive] at endpoints
  cases endpoints

private theorem copied_child_branches
    {current : LTerm} {root : B} {boundary : B→Bool}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (inputs : RootInputs site.net root) (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (closed : Closed current.erase) (selection : OccurrenceFragmentSelection current site.net root)
    (joint : JointRepresentation closed selection) (left right : SyntaxIncidence.Edge current)
    (iso : SuccessfulEndpointIso current closed (SyntaxIncidence.target current closed left)
      (SyntaxIncidence.target current closed right))
    (leftTarget rightTarget : RootAccess site.reduce root)
    (leftWord : accessWord site.reduce leftTarget.val=left.val)
    (rightWord : accessWord site.reduce rightTarget.val=right.val)
    (lb rb : Bool)
    (leftAt : leftTarget.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl lb),appCtx⟩)))
    (rightAt : rightTarget.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl rb),appCtx⟩))) : lb=rb := by
  obtain ⟨la,lf,lx,leftLookup⟩ := copied_access_app site targetMatches left leftTarget leftWord lb leftAt
  obtain ⟨ra,rf,rx,rightLookup⟩ := copied_access_app site targetMatches right rightTarget rightWord rb rightAt
  have leftEndpoint : SyntaxIncidence.target current closed left=some ⟨left.val,Or.inl ⟨la,lf,lx,leftLookup⟩⟩ :=
    SyntaxIncidence.target_eq_of_spec current closed left (Or.inl rfl)
  have rightEndpoint : SyntaxIncidence.target current closed right=some ⟨right.val,Or.inl ⟨ra,rf,rx,rightLookup⟩⟩ :=
    SyntaxIncidence.target_eq_of_spec current closed right (Or.inl rfl)
  rw [leftEndpoint,rightEndpoint] at iso
  exact endpoint_app_branches site sourceMatches inputs flow positive closed selection joint
    leftLookup rightLookup iso leftTarget rightTarget leftWord rightWord lb rb leftAt rightAt

private theorem argument_step_of_app_role
    (role : SourceDeparture (.app stamp fn arg) step port) (allowed : step=.arg ∨step=.body) : step=.arg := by
  cases role with
  | fn => rcases allowed with wrong|wrong <;> cases wrong
  | arg => rfl


private def proper_read_position {current : LTerm} (position : SyntaxIncidence.ProperPosition current) : Position current.erase :=
  ⟨position.val,by
    rcases position.property with ⟨stamp,fn,arg,lookup⟩|⟨stamp,body,lookup⟩ <;>
      rw [←LTerm.erase_subterm,lookup] <;> rfl⟩

/-- The finite physical routing has only actual endpoint cases as input.
The public natural top below constructs all this metadata itself. -/
private theorem paired_forward
    {current : LTerm} {root : B} {boundary : B→Bool}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (inputs : RootInputs site.net root) (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (principal : SiteActionPrincipal site) (closed : Closed current.erase)
    (selection : OccurrenceFragmentSelection current site.net root) (joint : JointRepresentation closed selection)
    (left right : SyntaxIncidence.Edge current)
    (sourceFirst : SourceEdgeFragment current site.net root leftEdge left.val)
    (targetFirst : SourceEdgeFragment current site.reduce root leftEdge left.val)
    (sourceSecond : SourceEdgeFragment current site.net root rightEdge right.val)
    (targetSecond : SourceEdgeFragment current site.reduce root rightEdge right.val)
    (leftRole : SourceDeparture leftTerm leftStep leftEdge.fromPort)
    (rightRole : SourceDeparture rightTerm rightStep rightEdge.fromPort)
    (leftAllowed : leftStep=.arg ∨leftStep=.body)
    (rightAllowed : rightStep=.arg ∨rightStep=.body)
    (leftParentPosition rightParentPosition : SyntaxIncidence.ProperPosition current)
    (leftLookup : current.subterm leftParentPosition.val=some leftTerm)
    (rightLookup : current.subterm rightParentPosition.val=some rightTerm)
    (leftEndpoint : SyntaxIncidence.source current left=some leftParentPosition)
    (rightEndpoint : SyntaxIncidence.source current right=some rightParentPosition)
    (sourceLeft sourceRight : RootAccess site.net root) (targetLeft targetRight : RootAccess site.reduce root)
    (sourceLeftWord : left.val=accessWord site.net sourceLeft.val++[leftStep])
    (sourceRightWord : right.val=accessWord site.net sourceRight.val++[rightStep])
    (targetLeftWord : left.val=accessWord site.reduce targetLeft.val++[leftStep])
    (targetRightWord : right.val=accessWord site.reduce targetRight.val++[rightStep])
    (leftParentWord : accessWord site.reduce targetLeft.val=leftParentPosition.val)
    (rightParentWord : accessWord site.reduce targetRight.val=rightParentPosition.val)
    (sourceIso : SuccessfulEndpointIso current closed (SyntaxIncidence.source current left) (SyntaxIncidence.source current right))
    (targetIso : SuccessfulEndpointIso current closed (SyntaxIncidence.target current closed left) (SyntaxIncidence.target current closed right))
    (pieces : sourceFirst.segments=sourceSecond.segments) : targetFirst.segments=targetSecond.segments := by
  have sameSteps : leftStep=rightStep := by
    apply Classical.byContradiction
    intro different
    exact sourceFirst.ne_of_child_steps sourceMatches sourceSecond leftRole rightRole sourceLeft sourceRight
      sourceLeftWord sourceRightWord different pieces
  subst rightStep
  have leftWord : accessWord site.net sourceLeft.val=accessWord site.reduce targetLeft.val :=
    List.append_cancel_right (sourceLeftWord.symm.trans targetLeftWord)
  have rightWord : accessWord site.net sourceRight.val=accessWord site.reduce targetRight.val :=
    List.append_cancel_right (sourceRightWord.symm.trans targetRightWord)
  rcases site.fan_app_access_cases targetLeft with ⟨lp,lpAt⟩|⟨lpb,lpAt⟩
  · rcases site.fan_app_access_cases targetRight with ⟨rp,rpAt⟩|⟨rpb,rpAt⟩
    · rcases site.fan_app_access_cases targetFirst.access with ⟨lc,lcAt⟩|⟨lcb,lcAt⟩
      · rcases site.fan_app_access_cases targetSecond.access with ⟨rc,rcAt⟩|⟨rcb,rcAt⟩
        · exact (sourceFirst.fan_kept_piece_equality site flow root positive sourceMatches targetMatches principal
            targetFirst sourceSecond targetSecond leftRole rightRole sourceLeft sourceRight targetLeft targetRight
            sourceLeftWord sourceRightWord targetLeftWord targetRightWord lp rp lc rc lpAt rpAt lcAt rcAt).mpr pieces
        · exact False.elim (terminal_mixed_source_ne site sourceMatches flow positive principal
            sourceSecond targetSecond sourceFirst targetFirst rcb rcAt lc lcAt pieces.symm)
      · rcases site.fan_app_access_cases targetSecond.access with ⟨rc,rcAt⟩|⟨rcb,rcAt⟩
        · exact False.elim (terminal_mixed_source_ne site sourceMatches flow positive principal
            sourceFirst targetFirst sourceSecond targetSecond lcb lcAt rc rcAt pieces)
        · have same := copied_child_branches site sourceMatches targetMatches inputs flow positive closed selection joint
            left right targetIso targetFirst.access targetSecond.access targetFirst.word targetSecond.word lcb rcb lcAt rcAt
          subst rcb
          exact sourceFirst.fan_kept_parent_copied_app_context_forward site flow root positive sourceMatches targetMatches principal
            targetFirst sourceSecond targetSecond leftRole rightRole sourceLeft sourceRight targetLeft targetRight
            sourceLeftWord sourceRightWord targetLeftWord targetRightWord lp rp lpAt rpAt lcb lcAt rcAt pieces
    · exact False.elim (parent_mixed_source_ne site sourceMatches flow positive principal sourceSecond sourceFirst
        rightRole leftRole sourceRight sourceLeft targetRight targetLeft sourceRightWord sourceLeftWord rightWord leftWord
        rpb rpAt lp lpAt pieces.symm)
  · rcases site.fan_app_access_cases targetRight with ⟨rp,rpAt⟩|⟨rpb,rpAt⟩
    · exact False.elim (parent_mixed_source_ne site sourceMatches flow positive principal sourceFirst sourceSecond
        leftRole rightRole sourceLeft sourceRight targetLeft targetRight sourceLeftWord sourceRightWord leftWord rightWord
        lpb lpAt rp rpAt pieces)
    · obtain ⟨la,lf,lx,lApp⟩ := copied_access_app site targetMatches (proper_read_position leftParentPosition)
        targetLeft leftParentWord lpb lpAt
      obtain ⟨ra,rf,rx,rApp⟩ := copied_access_app site targetMatches (proper_read_position rightParentPosition)
        targetRight rightParentWord rpb rpAt
      have lTerm : leftTerm=.app la lf lx := Option.some.inj (leftLookup.symm.trans lApp)
      have rTerm : rightTerm=.app ra rf rx := Option.some.inj (rightLookup.symm.trans rApp)
      rw [lTerm] at leftRole
      rw [rTerm] at rightRole
      have argStep := argument_step_of_app_role leftRole leftAllowed
      subst leftStep
      rw [leftEndpoint,rightEndpoint] at sourceIso
      have branchEq := endpoint_app_branches site sourceMatches inputs flow positive closed selection joint
        lApp rApp sourceIso targetLeft targetRight leftParentWord rightParentWord lpb rpb lpAt rpAt
      subst rpb
      rcases site.fan_app_access_cases targetFirst.access with ⟨lc,lcAt⟩|⟨lcb,lcAt⟩
      · rcases site.fan_app_access_cases targetSecond.access with ⟨rc,rcAt⟩|⟨rcb,rcAt⟩
        · exact sourceFirst.fan_app_copied_argument_kept_forward site flow root positive sourceMatches targetMatches principal
            targetFirst sourceSecond targetSecond leftRole rightRole sourceLeft sourceRight targetLeft targetRight
            sourceLeftWord sourceRightWord targetLeftWord targetRightWord lpb lpAt rpAt lc rc lcAt rcAt pieces
        · exact False.elim (terminal_mixed_source_ne site sourceMatches flow positive principal
            sourceSecond targetSecond sourceFirst targetFirst rcb rcAt lc lcAt pieces.symm)
      · rcases site.fan_app_access_cases targetSecond.access with ⟨rc,rcAt⟩|⟨rcb,rcAt⟩
        · exact False.elim (terminal_mixed_source_ne site sourceMatches flow positive principal
            sourceFirst targetFirst sourceSecond targetSecond lcb lcAt rc rcAt pieces)
        · have same := copied_child_branches site sourceMatches targetMatches inputs flow positive closed selection joint
            left right targetIso targetFirst.access targetSecond.access targetFirst.word targetSecond.word lcb rcb lcAt rcAt
          subst rcb
          exact sourceFirst.fan_copied_argument_copied_app_context_forward site flow root positive sourceMatches targetMatches principal
            targetFirst sourceSecond targetSecond leftRole rightRole sourceLeft sourceRight targetLeft targetRight
            sourceLeftWord sourceRightWord targetLeftWord targetRightWord lpb lcb lpAt rpAt lcAt rcAt pieces


private theorem paired_occurrences
    {current : LTerm} {root : B} {boundary : B→Bool}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (inputs : RootInputs site.net root) (principal : SiteActionPrincipal site)
    (closed : Closed current.erase) (selection : OccurrenceFragmentSelection current site.net root)
    (joint : JointRepresentation closed selection) (left right : SyntaxIncidence.Edge current)
    (sourceFirst : OccurrenceFragment current site.net root left.val)
    (targetFirst : OccurrenceFragment current site.reduce root left.val)
    (sourceSecond : OccurrenceFragment current site.net root right.val)
    (targetSecond : OccurrenceFragment current site.reduce root right.val)
    (leftAux : AuxiliaryAt current left.val) (rightAux : AuxiliaryAt current right.val)
    (sourceIso : SuccessfulEndpointIso current closed (SyntaxIncidence.source current left) (SyntaxIncidence.source current right))
    (targetIso : SuccessfulEndpointIso current closed (SyntaxIncidence.target current closed left) (SyntaxIncidence.target current closed right))
    (pieces : sourceFirst.fragment.segments=sourceSecond.fragment.segments) :
    targetFirst.fragment.segments=targetSecond.fragment.segments := by
  obtain ⟨ld⟩ := auxiliary_parent left sourceFirst leftAux sourceIso.left_available
  obtain ⟨rd⟩ := auxiliary_parent right sourceSecond rightAux sourceIso.right_available
  let lpos : SyntaxIncidence.ProperPosition current := ⟨ld.parent,ld.proper⟩
  let rpos : SyntaxIncidence.ProperPosition current := ⟨rd.parent,rd.proper⟩
  obtain ⟨sl,slWord,_⟩ := Matches.observation site.net sourceMatches (proper_read_position lpos)
  obtain ⟨sr,srWord,_⟩ := Matches.observation site.net sourceMatches (proper_read_position rpos)
  obtain ⟨tl,tlWord,_⟩ := Matches.observation site.reduce targetMatches (proper_read_position lpos)
  obtain ⟨tr,trWord,_⟩ := Matches.observation site.reduce targetMatches (proper_read_position rpos)
  have slSplit : left.val=accessWord site.net sl.val++[ld.step] := by rw [slWord];exact ld.split
  have srSplit : right.val=accessWord site.net sr.val++[rd.step] := by rw [srWord];exact rd.split
  have tlSplit : left.val=accessWord site.reduce tl.val++[ld.step] := by rw [tlWord];exact ld.split
  have trSplit : right.val=accessWord site.reduce tr.val++[rd.step] := by rw [trWord];exact rd.split
  rcases sourceFirst with ⟨lsub,lenv,lctx,locc,sourceFirst⟩
  rcases targetFirst with ⟨_,_,_,ltocc,targetFirst⟩
  obtain ⟨rfl,rfl,rfl⟩ := locc.same_occurrence ltocc
  rcases sourceSecond with ⟨rsub,renv,rctx,rocc,sourceSecond⟩
  rcases targetSecond with ⟨_,_,_,rtocc,targetSecond⟩
  obtain ⟨rfl,rfl,rfl⟩ := rocc.same_occurrence rtocc
  exact paired_forward site sourceMatches targetMatches inputs flow positive principal closed selection joint left right
    sourceFirst targetFirst sourceSecond targetSecond ld.role rd.role ld.allowed rd.allowed lpos rpos
    ld.lookup rd.lookup ld.endpoint rd.endpoint sl sr tl tr slSplit srSplit tlSplit trSplit tlWord trWord sourceIso targetIso pieces

/-- Natural D017 comparison. The SOURCE Joint IH supplies the OLD auxiliary
literal equality and both real endpoint-chain comparisons. No profile is input. -/
theorem PathSite.fan_app_auxiliary_endpoint_equality
    {current : LTerm} {root : B} {boundary : B→Bool}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (inputs : RootInputs site.net root) (principal : SiteActionPrincipal site)
    (closed : Closed current.erase)
    (source : OccurrenceFragmentSelection current site.net root)
    (target : OccurrenceFragmentSelection current site.reduce root)
    (sourceJoint : JointRepresentation closed source)
    (left right : SyntaxIncidence.Edge current)
    (leftAux : AuxiliaryAt current left.val) (rightAux : AuxiliaryAt current right.val)
    (sameLabel : SyntaxIncidence.label current left=SyntaxIncidence.label current right)
    (sourceIso : SuccessfulEndpointIso current closed (SyntaxIncidence.source current left) (SyntaxIncidence.source current right))
    (targetIso : SuccessfulEndpointIso current closed (SyntaxIncidence.target current closed left) (SyntaxIncidence.target current closed right)) :
    (target left).fragment.segments=(target right).fragment.segments := by
  have pieces : (source left).fragment.segments=(source right).fragment.segments := by
    apply Classical.byContradiction
    intro different
    exact sourceJoint.2 left right leftAux rightAux sameLabel different ⟨sourceIso,targetIso⟩
  -- SOURCE typed kind independently rejects APP/VAR mixed directions.
  rcases auxiliary_child_cases left leftAux with ⟨la,lf,lx,lLookup⟩|⟨la,lk,lLookup⟩
  · rcases auxiliary_child_cases right rightAux with ⟨ra,rf,rx,rLookup⟩|⟨ra,rk,rLookup⟩
    · exact paired_occurrences site sourceMatches targetMatches flow positive inputs principal closed source sourceJoint
        left right (source left) (target left) (source right) (target right) leftAux rightAux sourceIso targetIso pieces
    · exact False.elim (app_variable_source_ne sourceMatches (source left) (source right) lLookup rLookup pieces)
  · rcases auxiliary_child_cases right rightAux with ⟨ra,rf,rx,rLookup⟩|⟨ra,rk,rLookup⟩
    · exact False.elim (app_variable_source_ne sourceMatches (source right) (source left) rLookup lLookup pieces.symm)
    · exact paired_occurrences site sourceMatches targetMatches flow positive inputs principal closed source sourceJoint
        left right (source left) (target left) (source right) (target right) leftAux rightAux sourceIso targetIso pieces

/-- Target Aux preservation is conditional on the actual SOURCE Joint IH;
this theorem proves no instance of that IH or an unconditional trace invariant. -/
theorem PathSite.fan_app_auxiliary_separation_preserve
    {current : LTerm} {root : B} {boundary : B→Bool}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (inputs : RootInputs site.net root) (principal : SiteActionPrincipal site)
    (closed : Closed current.erase)
    (source : OccurrenceFragmentSelection current site.net root)
    (target : OccurrenceFragmentSelection current site.reduce root)
    (sourceJoint : JointRepresentation closed source) : AuxiliarySeparation closed target := by
  intro left right leftAux rightAux sameLabel different isos
  exact different (site.fan_app_auxiliary_endpoint_equality sourceMatches targetMatches flow positive inputs principal
    closed source target sourceJoint left right leftAux rightAux sameLabel isos.1 isos.2)

end
end Lamping.AG
#print axioms Lamping.AG.PathSite.fan_app_auxiliary_endpoint_equality
#print axioms Lamping.AG.PathSite.fan_app_auxiliary_separation_preserve
