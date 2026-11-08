import Lamping.Lamping.FanBodyVariableAuxiliary
import Lamping.Lamping.FanChainRepresentationTransport
import Lamping.Lamping.FragmentChildStepSeparation
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

private theorem argument_term (role : SourceDeparture term .arg port) :
    ∃stamp fn arg,term=.app stamp fn arg := by
  cases role
  exact ⟨_,_,_,rfl⟩
private theorem body_term (role : SourceDeparture term .body port) :
    ∃stamp body,term=.lam stamp body := by
  cases role
  exact ⟨_,_,rfl⟩
private theorem auxiliary_argument_spec {position : SyntaxIncidence.Edge current}
    {fragment : OccurrenceFragment current g root position.val} (data : AuxiliaryParent position fragment)
    (argument : data.step=.arg) (lookup : current.subterm position.val=some child) :
    ∃parent stamp fn,position.val=parent++[.arg] ∧current.subterm parent=some (.app stamp fn child) := by
  have role : SourceDeparture data.term .arg (sourceEdge fragment.environment fragment.context fragment.term).fromPort := by
    simpa only [argument] using data.role
  obtain ⟨stamp,fn,arg,same⟩ := argument_term role
  have parentLookup := data.lookup
  rw [same] at parentLookup
  have actual := lookup
  rw [data.split,argument,LTerm.subterm_append,parentLookup] at actual
  simp only [Option.bind_some,LTerm.subterm] at actual
  have children := Option.some.inj actual
  refine ⟨data.parent,stamp,fn,by simpa only [argument] using data.split,?_⟩
  simpa only [children] using parentLookup
private theorem auxiliary_body_spec {position : SyntaxIncidence.Edge current}
    {fragment : OccurrenceFragment current g root position.val} (data : AuxiliaryParent position fragment)
    (body : data.step=.body) (lookup : current.subterm position.val=some child) :
    ∃parent stamp,position.val=parent++[.body] ∧current.subterm parent=some (.lam stamp child) := by
  have role : SourceDeparture data.term .body (sourceEdge fragment.environment fragment.context fragment.term).fromPort := by
    simpa only [body] using data.role
  obtain ⟨stamp,sub,same⟩ := body_term role
  have parentLookup := data.lookup
  rw [same] at parentLookup
  have actual := lookup
  rw [data.split,body,LTerm.subterm_append,parentLookup] at actual
  simp only [Option.bind_some,LTerm.subterm] at actual
  have children := Option.some.inj actual
  refine ⟨data.parent,stamp,by simpa only [body] using data.split,?_⟩
  simpa only [children] using parentLookup
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.fanAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
private theorem kept_piece_equality
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site) {p q : Path}
    (sourceFirst : OccurrenceFragment current site.net root p)
    (targetFirst : OccurrenceFragment current site.reduce root p)
    (sourceSecond : OccurrenceFragment current site.net root q)
    (targetSecond : OccurrenceFragment current site.reduce root q)
    {leftTerm rightTerm : LTerm} {leftStep rightStep : Step}
    (leftRole : SourceDeparture leftTerm leftStep (sourceEdge sourceFirst.environment sourceFirst.context sourceFirst.term).fromPort)
    (rightRole : SourceDeparture rightTerm rightStep (sourceEdge sourceSecond.environment sourceSecond.context sourceSecond.term).fromPort)
    (sourceLeft sourceRight : RootAccess site.net root) (targetLeft targetRight : RootAccess site.reduce root)
    (sourceLeftWord : p=accessWord site.net sourceLeft.val++[leftStep])
    (sourceRightWord : q=accessWord site.net sourceRight.val++[rightStep])
    (targetLeftWord : p=accessWord site.reduce targetLeft.val++[leftStep])
    (targetRightWord : q=accessWord site.reduce targetRight.val++[rightStep])
    (leftParent rightParent leftEnd rightEnd : NodePort signature K kept)
    (leftParentAt : targetLeft.val.getLast?=some (site.reduce.wire (.inl ⟨.inl leftParent.1,leftParent.2⟩)))
    (rightParentAt : targetRight.val.getLast?=some (site.reduce.wire (.inl ⟨.inl rightParent.1,rightParent.2⟩)))
    (leftEndAt : targetFirst.fragment.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl leftEnd.1,leftEnd.2⟩)))
    (rightEndAt : targetSecond.fragment.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl rightEnd.1,rightEnd.2⟩))) :
    targetFirst.fragment.segments=targetSecond.fragment.segments ↔sourceFirst.fragment.segments=sourceSecond.fragment.segments := by
  rcases sourceFirst with ⟨lsub,lenv,lctx,locc,lsource⟩
  rcases targetFirst with ⟨_,_,_,ltocc,ltarget⟩
  obtain ⟨rfl,rfl,rfl⟩ := locc.same_occurrence ltocc
  rcases sourceSecond with ⟨rsub,renv,rctx,rocc,rsource⟩
  rcases targetSecond with ⟨_,_,_,rtocc,rtarget⟩
  obtain ⟨rfl,rfl,rfl⟩ := rocc.same_occurrence rtocc
  exact lsource.fan_kept_piece_equality site flow root positive sourceMatches targetMatches principal
    ltarget rsource rtarget leftRole rightRole sourceLeft sourceRight targetLeft targetRight
    sourceLeftWord sourceRightWord targetLeftWord targetRightWord leftParent rightParent leftEnd rightEnd
    leftParentAt rightParentAt leftEndAt rightEndAt


/-- Real lexical binders from successful endpoint iso, not FUNCTION membership
or a supplied nextslot/profile, synchronize the copied binding endpoints. -/

private theorem body_kept_forward
    {directions : B→Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site)
    (sourceFirst : OccurrenceFragment current site.net root p)
    (targetFirst : OccurrenceFragment current site.reduce root p)
    (sourceSecond : OccurrenceFragment current site.net root q)
    (targetSecond : OccurrenceFragment current site.reduce root q)
    (leftRole : SourceDeparture leftTerm .body (sourceEdge sourceFirst.environment sourceFirst.context sourceFirst.term).fromPort)
    (rightRole : SourceDeparture rightTerm .body (sourceEdge sourceSecond.environment sourceSecond.context sourceSecond.term).fromPort)
    (sourceLeft sourceRight : RootAccess site.net root) (targetLeft targetRight : RootAccess site.reduce root)
    (sourceLeftWord : p=accessWord site.net sourceLeft.val++[.body])
    (sourceRightWord : q=accessWord site.net sourceRight.val++[.body])
    (targetLeftWord : p=accessWord site.reduce targetLeft.val++[.body])
    (targetRightWord : q=accessWord site.reduce targetRight.val++[.body])
    (branch : Bool)
    (leftParentAt : targetLeft.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),.inl ()⟩)))
    (rightParentAt : targetRight.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),.inl ()⟩)))
    (leftTerminal rightTerminal : NodePort signature K kept)
    (leftEndAt : targetFirst.fragment.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl leftTerminal.1,leftTerminal.2⟩)))
    (rightEndAt : targetSecond.fragment.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl rightTerminal.1,rightTerminal.2⟩)))
    (pieces : sourceFirst.fragment.segments=sourceSecond.fragment.segments) : targetFirst.fragment.segments=targetSecond.fragment.segments := by
  rcases sourceFirst with ⟨lsub,lenv,lctx,locc,lsource⟩
  rcases targetFirst with ⟨_,_,_,ltocc,ltarget⟩
  obtain ⟨rfl,rfl,rfl⟩ := locc.same_occurrence ltocc
  rcases sourceSecond with ⟨rsub,renv,rctx,rocc,rsource⟩
  rcases targetSecond with ⟨_,_,_,rtocc,rtarget⟩
  obtain ⟨rfl,rfl,rfl⟩ := rocc.same_occurrence rtocc
  exact lsource.fan_copied_body_kept_forward site flow root positive sourceMatches targetMatches principal
    ltarget rsource rtarget leftRole rightRole sourceLeft sourceRight targetLeft targetRight
    sourceLeftWord sourceRightWord targetLeftWord targetRightWord branch leftParentAt rightParentAt
    leftTerminal rightTerminal leftEndAt rightEndAt pieces

private theorem parent_mixed_ne
    {directions : B→Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site)
    (sourceCopy : OccurrenceFragment current site.net root p)
    (targetCopy : OccurrenceFragment current site.reduce root p)
    (sourceKept : OccurrenceFragment current site.net root q)
    (targetKept : OccurrenceFragment current site.reduce root q)
    (copyRole : SourceDeparture copyTerm .body (sourceEdge sourceCopy.environment sourceCopy.context sourceCopy.term).fromPort)
    (keptRole : SourceDeparture keptTerm keptStep (sourceEdge sourceKept.environment sourceKept.context sourceKept.term).fromPort)
    (sourceCopyParent sourceKeptParent : RootAccess site.net root)
    (targetCopyParent targetKeptParent : RootAccess site.reduce root)
    (sourceCopyWord : p=accessWord site.net sourceCopyParent.val++[.body])
    (sourceKeptWord : q=accessWord site.net sourceKeptParent.val++[keptStep])
    (targetCopyWord : p=accessWord site.reduce targetCopyParent.val++[.body])
    (targetKeptWord : q=accessWord site.reduce targetKeptParent.val++[keptStep])
    (branch : Bool)
    (copyFinish : targetCopyParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),.inl ()⟩)))
    (node : K) (port : Port (kept node).sort)
    (keptFinish : targetKeptParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inl node,port⟩))) :
    sourceCopy.fragment.segments≠sourceKept.fragment.segments ∧targetCopy.fragment.segments≠targetKept.fragment.segments := by
  rcases sourceCopy with ⟨lsub,lenv,lctx,locc,lsource⟩
  rcases targetCopy with ⟨_,_,_,ltocc,ltarget⟩
  obtain ⟨rfl,rfl,rfl⟩ := locc.same_occurrence ltocc
  rcases sourceKept with ⟨rsub,renv,rctx,rocc,rsource⟩
  rcases targetKept with ⟨_,_,_,rtocc,rtarget⟩
  obtain ⟨rfl,rfl,rfl⟩ := rocc.same_occurrence rtocc
  exact lsource.fan_lambda_copied_parent_vs_kept_parent site flow root positive sourceMatches targetMatches principal
    ltarget rsource rtarget copyRole keptRole sourceCopyParent sourceKeptParent targetCopyParent targetKeptParent
    sourceCopyWord sourceKeptWord targetCopyWord targetKeptWord branch copyFinish node port keptFinish

private def proper_read_position {current : LTerm} (position : SyntaxIncidence.ProperPosition current) : Position current.erase :=
  ⟨position.val,by
    rcases position.property with ⟨stamp,fn,arg,lookup⟩|⟨stamp,body,lookup⟩ <;>
      rw [←LTerm.erase_subterm,lookup] <;> rfl⟩

private theorem app_access_kept {current : LTerm} {root : B}
    (matching : Matches site.reduce root current.erase)
    (lookup : current.subterm p=some (.app stamp fn arg))
    (path : RootAccess site.reduce root) (word : accessWord site.reduce path.val=p) :
    ∃port : NodePort signature K kept,
      path.val.getLast?=some (site.reduce.wire (.inl ⟨.inl port.1,port.2⟩)) := by
  apply site.action_access_kept_of_kind_excluded (.fan .lam i j lt) path
    (matching.app_access_typed lookup path word)
  intro port wrong
  rcases port with u|aux
  · cases u;cases wrong
  · cases aux <;> cases wrong

private theorem app_occurrences_forward
    {current : LTerm} {root : B} {boundary : B→Bool}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (principal : SiteActionPrincipal site) (closed : Closed current.erase)
    (selection : OccurrenceFragmentSelection current site.net root) (joint : JointRepresentation closed selection)
    (left right : SyntaxIncidence.Edge current)
    (sourceFirst : OccurrenceFragment current site.net root left.val)
    (targetFirst : OccurrenceFragment current site.reduce root left.val)
    (sourceSecond : OccurrenceFragment current site.net root right.val)
    (targetSecond : OccurrenceFragment current site.reduce root right.val)
    (ld : AuxiliaryParent left sourceFirst) (rd : AuxiliaryParent right sourceSecond)
    (sameStep : ld.step=rd.step)
    (leftLookup : current.subterm left.val=some (.app la lf lx))
    (rightLookup : current.subterm right.val=some (.app ra rf rx))
    (sourceIso : SuccessfulEndpointIso current closed (SyntaxIncidence.source current left) (SyntaxIncidence.source current right))
    (pieces : sourceFirst.fragment.segments=sourceSecond.fragment.segments) :
    targetFirst.fragment.segments=targetSecond.fragment.segments := by
  let lpos : SyntaxIncidence.ProperPosition current := ⟨ld.parent,ld.proper⟩
  let rpos : SyntaxIncidence.ProperPosition current := ⟨rd.parent,rd.proper⟩
  obtain ⟨sl,slWord,_⟩ := Matches.observation site.net sourceMatches (proper_read_position lpos)
  obtain ⟨sr,srWord,_⟩ := Matches.observation site.net sourceMatches (proper_read_position rpos)
  obtain ⟨tl,tlWord,_⟩ := Matches.observation site.reduce targetMatches (proper_read_position lpos)
  obtain ⟨tr,trWord,_⟩ := Matches.observation site.reduce targetMatches (proper_read_position rpos)
  obtain ⟨lc,lcAt⟩ := app_access_kept site targetMatches leftLookup targetFirst.fragment.access targetFirst.fragment.word
  obtain ⟨rc,rcAt⟩ := app_access_kept site targetMatches rightLookup targetSecond.fragment.access targetSecond.fragment.word
  rcases ld.allowed with lArg|lBody
  · have rArg : rd.step=.arg := sameStep.symm.trans lArg
    have lRole : SourceDeparture ld.term .arg (sourceEdge sourceFirst.environment sourceFirst.context sourceFirst.term).fromPort := by simpa only [lArg] using ld.role
    have rRole : SourceDeparture rd.term .arg (sourceEdge sourceSecond.environment sourceSecond.context sourceSecond.term).fromPort := by simpa only [rArg] using rd.role
    obtain ⟨a,f,x,lTerm⟩ := argument_term lRole
    obtain ⟨b,g,y,rTerm⟩ := argument_term rRole
    have lLookup := ld.lookup
    have rLookup := rd.lookup
    rw [lTerm] at lLookup
    rw [rTerm] at rLookup
    obtain ⟨lp,lpAt⟩ := app_access_kept site targetMatches lLookup tl tlWord
    obtain ⟨rp,rpAt⟩ := app_access_kept site targetMatches rLookup tr trWord
    have slSplit : left.val=accessWord site.net sl.val++[.arg] := by rw [slWord];simpa only [lArg] using ld.split
    have srSplit : right.val=accessWord site.net sr.val++[.arg] := by rw [srWord];simpa only [rArg] using rd.split
    have tlSplit : left.val=accessWord site.reduce tl.val++[.arg] := by rw [tlWord];simpa only [lArg] using ld.split
    have trSplit : right.val=accessWord site.reduce tr.val++[.arg] := by rw [trWord];simpa only [rArg] using rd.split
    exact (kept_piece_equality site flow root positive sourceMatches targetMatches principal sourceFirst targetFirst sourceSecond targetSecond
      lRole rRole sl sr tl tr slSplit srSplit tlSplit trSplit lp rp lc rc lpAt rpAt lcAt rcAt).mpr pieces
  · have rBody : rd.step=.body := sameStep.symm.trans lBody
    have lRole : SourceDeparture ld.term .body (sourceEdge sourceFirst.environment sourceFirst.context sourceFirst.term).fromPort := by simpa only [lBody] using ld.role
    have rRole : SourceDeparture rd.term .body (sourceEdge sourceSecond.environment sourceSecond.context sourceSecond.term).fromPort := by simpa only [rBody] using rd.role
    obtain ⟨a,sub,lTerm⟩ := body_term lRole
    obtain ⟨b,other,rTerm⟩ := body_term rRole
    have lLookup := ld.lookup
    have rLookup := rd.lookup
    rw [lTerm] at lLookup
    rw [rTerm] at rLookup
    have slSplit : left.val=accessWord site.net sl.val++[.body] := by rw [slWord];simpa only [lBody] using ld.split
    have srSplit : right.val=accessWord site.net sr.val++[.body] := by rw [srWord];simpa only [rBody] using rd.split
    have tlSplit : left.val=accessWord site.reduce tl.val++[.body] := by rw [tlWord];simpa only [lBody] using ld.split
    have trSplit : right.val=accessWord site.reduce tr.val++[.body] := by rw [trWord];simpa only [rBody] using rd.split
    rcases site.fan_lambda_access_cases tl (targetMatches.lambda_access_typed lLookup tl tlWord) with ⟨lp,lpAt⟩|⟨lb,lpAt⟩
    · rcases site.fan_lambda_access_cases tr (targetMatches.lambda_access_typed rLookup tr trWord) with ⟨rp,rpAt⟩|⟨rb,rpAt⟩
      · exact (kept_piece_equality site flow root positive sourceMatches targetMatches principal sourceFirst targetFirst sourceSecond targetSecond
          lRole rRole sl sr tl tr slSplit srSplit tlSplit trSplit lp rp lc rc lpAt rpAt lcAt rcAt).mpr pieces
      · exact False.elim ((parent_mixed_ne site flow root positive sourceMatches targetMatches principal sourceSecond targetSecond sourceFirst targetFirst
          rRole lRole sr sl tr tl srSplit slSplit trSplit tlSplit rb rpAt lp.1 lp.2 lpAt).1 pieces.symm)
    · rcases site.fan_lambda_access_cases tr (targetMatches.lambda_access_typed rLookup tr trWord) with ⟨rp,rpAt⟩|⟨rb,rpAt⟩
      · exact False.elim ((parent_mixed_ne site flow root positive sourceMatches targetMatches principal sourceFirst targetFirst sourceSecond targetSecond
          lRole rRole sl sr tl tr slSplit srSplit tlSplit trSplit lb lpAt rp.1 rp.2 rpAt).1 pieces)
      · rw [ld.endpoint,rd.endpoint] at sourceIso
        obtain ⟨es,fs,first,second,iso⟩ := sourceIso
        change PrerequisiteChain current ld.parent es at first
        change PrerequisiteChain current rd.parent fs at second
        have branches := site.prerequisite_lambda_copy_branches sourceMatches flow positive principal closed selection joint
          lLookup rLookup first second iso tl tr tlWord trWord lb rb lpAt rpAt
        subst rb
        exact body_kept_forward site flow root positive sourceMatches targetMatches principal sourceFirst targetFirst sourceSecond targetSecond
          lRole rRole sl sr tl tr slSplit srSplit tlSplit trSplit lb lpAt rpAt lc rc lcAt rcAt pieces

private theorem auxiliary_endpoint_equality
    {current : LTerm} {root : B} {boundary : B→Bool}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (oldT : Transparency site.net root) (principal : SiteActionPrincipal site) (closed : Closed current.erase)
    (source : OccurrenceFragmentSelection current site.net root) (target : OccurrenceFragmentSelection current site.reduce root)
    (sourceJoint : JointRepresentation closed source) (left right : SyntaxIncidence.Edge current)
    (leftAux : AuxiliaryAt current left.val) (rightAux : AuxiliaryAt current right.val)
    (sameLabel : SyntaxIncidence.label current left=SyntaxIncidence.label current right)
    (sourceIso : SuccessfulEndpointIso current closed (SyntaxIncidence.source current left) (SyntaxIncidence.source current right))
    (targetIso : SuccessfulEndpointIso current closed (SyntaxIncidence.target current closed left) (SyntaxIncidence.target current closed right)) :
    (target left).fragment.segments=(target right).fragment.segments := by
  have pieces : (source left).fragment.segments=(source right).fragment.segments := by
    apply Classical.byContradiction
    intro different
    exact sourceJoint.2 left right leftAux rightAux sameLabel different ⟨sourceIso,targetIso⟩
  obtain ⟨ld⟩ := auxiliary_parent left (source left) leftAux sourceIso.left_available
  obtain ⟨rd⟩ := auxiliary_parent right (source right) rightAux sourceIso.right_available
  by_cases sameStep : ld.step=rd.step
  · rcases auxiliary_child_cases left leftAux with ⟨la,lf,lx,lLookup⟩|⟨la,lk,lLookup⟩
    · rcases auxiliary_child_cases right rightAux with ⟨ra,rf,rx,rLookup⟩|⟨ra,rk,rLookup⟩
      · exact app_occurrences_forward site sourceMatches targetMatches flow positive principal closed source sourceJoint left right
          (source left) (target left) (source right) (target right) ld rd sameStep lLookup rLookup sourceIso pieces
      · exact False.elim (app_variable_source_ne sourceMatches (source left) (source right) lLookup rLookup pieces)
    · rcases auxiliary_child_cases right rightAux with ⟨ra,rf,rx,rLookup⟩|⟨ra,rk,rLookup⟩
      · exact False.elim (app_variable_source_ne sourceMatches (source right) (source left) rLookup lLookup pieces.symm)
      · rcases ld.allowed with lArg|lBody
        · have rArg : rd.step=.arg := sameStep.symm.trans lArg
          exact site.fan_argument_variable_endpoint_equality sourceMatches targetMatches flow positive oldT principal closed source target sourceJoint
            left right lLookup rLookup (auxiliary_argument_spec ld lArg lLookup) (auxiliary_argument_spec rd rArg rLookup) sameLabel sourceIso targetIso
        · have rBody : rd.step=.body := sameStep.symm.trans lBody
          exact site.fan_body_variable_endpoint_equality sourceMatches targetMatches flow positive oldT principal closed source target sourceJoint
            left right lLookup rLookup (auxiliary_body_spec ld lBody lLookup) (auxiliary_body_spec rd rBody rLookup) sameLabel sourceIso targetIso
  · let lpos : SyntaxIncidence.ProperPosition current := ⟨ld.parent,ld.proper⟩
    let rpos : SyntaxIncidence.ProperPosition current := ⟨rd.parent,rd.proper⟩
    obtain ⟨sl,slWord,_⟩ := Matches.observation site.net sourceMatches (proper_read_position lpos)
    obtain ⟨sr,srWord,_⟩ := Matches.observation site.net sourceMatches (proper_read_position rpos)
    have slSplit : left.val=accessWord site.net sl.val++[ld.step] := by rw [slWord];exact ld.split
    have srSplit : right.val=accessWord site.net sr.val++[rd.step] := by rw [srWord];exact rd.split
    exact False.elim ((source left).fragment.ne_of_child_steps sourceMatches (source right).fragment
      ld.role rd.role sl sr slSplit srSplit sameStep pieces)

/-- Complete natural D017 Aux preservation on fanlambda. SOURCEJoint is
an explicit IH; all actual roles, typed cases and OLD equality are internal. -/
theorem PathSite.fan_lambda_auxiliary_separation_preserve
    {current : LTerm} {root : B} {boundary : B→Bool}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (oldT : Transparency site.net root) (principal : SiteActionPrincipal site) (closed : Closed current.erase)
    (source : OccurrenceFragmentSelection current site.net root) (target : OccurrenceFragmentSelection current site.reduce root)
    (sourceJoint : JointRepresentation closed source) : AuxiliarySeparation closed target := by
  intro left right leftAux rightAux sameLabel different isos
  exact different (auxiliary_endpoint_equality site sourceMatches targetMatches flow positive oldT principal closed
    source target sourceJoint left right leftAux rightAux sameLabel isos.1 isos.2)

/-- Only preservation from a genuine SOURCE IH; this proves no instance
of that IH, no complete history invariant and no other schema. -/
theorem PathSite.fan_lambda_joint_representation_preserve
    {current : LTerm} {root : B} {boundary : B→Bool}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (oldT : Transparency site.net root) (principal : SiteActionPrincipal site) (closed : Closed current.erase)
    (source : OccurrenceFragmentSelection current site.net root) (target : OccurrenceFragmentSelection current site.reduce root)
    (sourceJoint : JointRepresentation closed source) : JointRepresentation closed target :=
  ⟨(site.fan_lambda_chain_invariant sourceMatches targetMatches flow positive oldT principal closed source target).2 sourceJoint.1,
    site.fan_lambda_auxiliary_separation_preserve sourceMatches targetMatches flow positive oldT principal closed source target sourceJoint⟩
end
end Lamping.AG
#print axioms Lamping.AG.PathSite.fan_lambda_auxiliary_separation_preserve
#print axioms Lamping.AG.PathSite.fan_lambda_joint_representation_preserve
