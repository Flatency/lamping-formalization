import Lamping.Lamping.BetaSyntaxTrailAccess
import Lamping.Lamping.TypedBinderRealization
import Lamping.Lamping.BindingObservationWords
import Lamping.Lamping.BetaBindingLoopContraction
import Lamping.Lambda.ClosedVariableBinders

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

private theorem lambda_kind {kind : Kind} {ctx : Port kind}
    (sort : kind=.op .lam) (role : HEq ctx (Sum.inl () : Port (.op .lam))) : portKind kind ctx=some .lam := by
  subst kind
  cases eq_of_heq role
  rfl
private theorem binding_kind {kind : Kind} {bind : Port kind}
    (sort : kind=.op .lam) (role : HEq bind lamBind) : portKind kind bind=some .var := by
  subst kind
  cases eq_of_heq role
  rfl

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
variable {root : B} {original target : LTerm} {ps : List Path} {marked : Marked}

/-- A current variable's lexical binder, its SAME-assignment typed loop and
the actual residual produce its precise RHS binding suffix. The source
walks are structural witnesses for the one shared selector; they assert no
target path, index observation or coverage. -/
theorem PathSite.beta_variable_access
    (initial : INIT original) (matching : Matches site.net root original.erase)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (relative : Marked.RelativeHistory ps (Marked.mark (site.betaSyntaxFiber root original.erase) original.erase) marked)
    (normal : Marked.Normal marked) (history : History ps original target) (closed : Closed target.erase)
    {edge : BetaEdge site.net} (geometry : SiteBetaGeometry site edge)
    (selection : SourceEdgeSelection original site.net root)
    (allWalks : ∀ {start stamp finish},SelectedSourceRoute (sourceEdges [] .external original)
      (SelectedDegree original (site.betaSyntaxFiber root original.erase)) start stamp finish →
      ∃ walk : PhysicalSourceWalk original root edge start stamp finish,walk.edges=selection.evalLabel edge stamp)
    (generated : GeneratedSyntaxPaths selection edge target)
    (supported : SupportedSyntaxBinders selection edge target)
    (paths : TypedSyntaxPaths selection edge target) (binders : TypedSyntaxBinders selection edge target)
    {position stamp index} (lookup : target.subterm position=some (.var stamp index)) :
    ∃ access : RootAccess site.reduce root,accessWord site.reduce access.val=position ∧
      accessKind site.reduce access.val=some .var ∧BindingSuffix site.reduce access.val index := by
  obtain ⟨parent,q,origin,body,positionEq,atLambda,_bodyLookup,atVariable,indexEq⟩ := target.closed_variable_binder closed lookup
  obtain ⟨ambient,loop,binder,ctx,ambientEval,leafEval,sort,ctxRole,ambientEnd,total⟩ :=
    realize_typed_binder generated supported paths binders atLambda atVariable
  have routes := relative_development_selected_routes initial relative history
  obtain ⟨parentFinish,parentTrail,parentEval⟩ := selection.syntax_evaluation initial matching allWalks routes atLambda
  have parentEdges : parentTrail.edges=ambient := Option.some.inj (parentEval.symm.trans ambientEval)
  obtain ⟨node,parentCtx,parentKept,_parentSort,_parentRole⟩ :=
    parentTrail.complete_lambda_terminal site initial matching flow positive relative normal history
  have parentEnd : parentTrail.toEndpoint=.inl ⟨binder,ctx⟩ := by
    have last := parentTrail.last
    rw [parentEdges] at last
    have wires := congrArg site.net.wire (Option.some.inj (last.symm.trans ambientEnd))
    simpa only [Pairing.involutive] using wires
  have nodeEq : binder=.inl node := by
    have ends := parentEnd.symm.trans parentKept
    exact congrArg Sigma.fst (Sum.inl.inj ends)
  subst binder
  obtain ⟨output,seam,_count,whole,prefixLabels,binding,binderEq⟩ := total Context.empty
  rcases binding with ⟨actualBinder,isLam,bodyPort,bindPort,bodyRole,bindRole,loopStart,loopEnd,loopLabels,loopForward,shell⟩
  dsimp only at binderEq
  subst actualBinder
  let binding : ExpandedBindingLoop site.net loop seam output :=
    ⟨.inl node,isLam,bodyPort,bindPort,bodyRole,bindRole,loopStart,loopEnd,loopLabels,loopForward,shell⟩
  obtain ⟨leafFinish,leafTrail,leafEvaluation⟩ := selection.syntax_evaluation initial matching allWalks routes lookup
  have fullEval : target.sourceTrail selection.atomWord edge.principal edge.reverseRoute position=some (ambient++loop) := by
    rw [positionEq]; exact leafEval
  have leafEdges : leafTrail.edges=ambient++loop := Option.some.inj (leafEvaluation.symm.trans fullEval)
  have leafEnd : leafTrail.toEndpoint=.inl ⟨.inl node,bindPort⟩ := by
    have fullLast : leafTrail.edges.getLast?=some (site.net.wire (.inl ⟨.inl node,bindPort⟩)) := by
      rw [leafEdges]
      simp only [List.getLast?_append,loopEnd,Option.some_or]
    have wires := congrArg site.net.wire (Option.some.inj (leafTrail.last.symm.trans fullLast))
    simpa only [Pairing.involutive] using wires
  have leafLabels : ExpandedLabelling site.net leafTrail.edges Context.empty output := by rw [leafEdges]; exact whole.labelling _
  obtain ⟨leafAccess,leafResidual,leafActual,leafWord,leafKind,_leafLast⟩ :=
    leafTrail.beta_contract_access site initial matching flow positive relative normal history geometry leafLabels
      node bindPort .var leafEnd (binding_kind isLam bindRole)
  have parentLabels : ExpandedLabelling site.net parentTrail.edges Context.empty seam := by rw [parentEdges]; exact prefixLabels
  obtain ⟨parentAccess,_parentResidual,parentActual,parentWord,_parentKind,parentLast⟩ :=
    parentTrail.beta_contract_access site initial matching flow positive relative normal history geometry parentLabels
      node ctx .lam parentEnd (lambda_kind sort ctxRole)
  obtain ⟨targetPre,targetLoop,split,targetPreLabels,targetPreEnd,targetBinding,targetBinder⟩ :=
    leafResidual.contract_binding_prefix_actual site geometry leafActual root leafAccess.property.2.1 leafAccess.property.1.2
      ambient loop leafEdges binding node rfl ctx ctxRole ambientEnd prefixLabels
  rcases targetBinding with ⟨targetNode,targetSort,targetBody,targetBind,targetBodyRole,targetBindRole,
    targetStart,targetEnd,targetLabels,targetForward,targetShell⟩
  dsimp only at targetBinder
  subst targetNode
  let targetBinding : BindingLoop site.reduce targetLoop seam output :=
    ⟨.inl node,targetSort,targetBody,targetBind,targetBodyRole,targetBindRole,targetStart,targetEnd,targetLabels,targetForward,targetShell⟩
  have words : accessWord site.reduce leafAccess.val=accessWord site.reduce parentAccess.val++(.body::q) := by
    rw [leafWord,parentWord]; exact positionEq
  have suffix := leafAccess.binding_suffix_of_same_seam parentAccess targetPre targetLoop targetBinding ctx ctxRole
    split targetPreLabels targetPreEnd parentActual parentLast q words
  exact ⟨leafAccess,leafWord,leafKind,by rw [indexEq]; exact suffix⟩
end
end Lamping.AG
